
module Agda2Dk.Compiler where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.ByteString.Lazy as BS
import qualified Data.Map as M
import Data.Maybe

import System.Directory ( canonicalizePath, createDirectoryIfMissing
                        , setCurrentDirectory
                        , doesDirectoryExist
                        , doesFileExist
                        , getDirectoryContents, copyFile
                        )
import Data.List as L
import Data.Int
import System.IO
import System.Exit
import System.FilePath hiding (normalise)

import Agda.Compiler.CallCompiler
import Agda.Interaction.FindFile
import Agda.Interaction.Options
import Agda.Interaction.Imports
import qualified Agda.Syntax.Concrete.Name as CN
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Serialise
import Agda.TypeChecking.Datatypes
import Agda.Utils.FileName
import Agda.Utils.IO.Directory
import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.TypeChecking.ReconstructParameters

import Agda.Compiler.Common
import Agda.Compiler.Backend

import Agda.Utils.Impossible

import Text.PrettyPrint

import Debug.Trace

import Agda2Dk.DkSyntax

-- Backend callbacks ------------------------------------------------------

dkBackend :: Backend
dkBackend = Backend dkBackend'

dkBackend' :: Backend' DkOptions DkOptions DkModuleEnv () DkDefinition --
dkBackend' = Backend'
  { backendName           = "Dk"
  , backendVersion        = Nothing
  , options               = defaultDkOptions
  , commandLineFlags      = dkCommandLineFlags
  , isEnabled             = optDkCompile
  , preCompile            = \opts -> return opts
  , postCompile           = \_ _ _ -> return ()
  , preModule             = dkPreModule
  , postModule            = dkPostModule
  , compileDef            = dkCompileDef
  , scopeCheckingSuffices = False
  , mayEraseType          = \_ -> return True
  }

--- Options ---

data DkOptions = DkOptions
  { optDkCompile :: Bool
  , optDkFlags   :: [String]
  , optDkDir     :: Maybe String
  }

defaultDkOptions :: DkOptions
defaultDkOptions = DkOptions
  { optDkCompile = False
  , optDkFlags   = []
  , optDkDir     = Nothing
  }

dkCommandLineFlags :: [OptDescr (Flag DkOptions)]
dkCommandLineFlags =
    [ Option []     ["dk"]     (NoArg compileDkFlag) "compile program using the Dk backend"
    , Option []     ["outDir"] (OptArg outp "DIR")  "output DIR"
    ]
  where
    compileDkFlag o = return $ o { optDkCompile = True}
    outp d o        = return $ o { optDkDir = d}

--- Module compilation ---

type DkModuleEnv = ()


dkPreModule :: DkOptions -> IsMain -> ModuleName -> FilePath -> TCM (Recompile DkModuleEnv ())
dkPreModule opts _ mods _ =
  let concMods = modName2DkModIdent mods in
  let dir = case optDkDir opts of Nothing -> ""
                                  Just s  -> s
  in
  let mod = intercalate "__" concMods in
  let filePath = dir++mod++".dk" in
  liftIO $
    ifM (doesFileExist filePath)
      (do putStrLn $ "Already generated "++filePath
          return (Skip ()))
      (do putStrLn $ "Generation of "++filePath
          return (Recompile ()))

dkPostModule :: DkOptions -> DkModuleEnv -> IsMain -> ModuleName -> [DkDefinition] -> TCM ()
dkPostModule opts _ _ mods defs =
  let concMods = modName2DkModIdent mods in
  let output = orderDeclRules defs concMods in
  let dir = case optDkDir opts of Nothing -> ""
                                  Just s  -> s
  in
  let mod = intercalate "__" concMods in
  let filePath = dir++mod++".dk" in
  liftIO $
    do putStrLn $ "We indeed create "++filePath
       writeFile filePath (show output)

orderDeclRules :: [DkDefinition] -> DkModName -> Doc
orderDeclRules = orderDeclRules' 0 empty []

orderDeclRules' mutInd acc waitingRules []     mods = acc <> (hcat waitingRules)
orderDeclRules' mutInd acc waitingRules (d:tl) mods
  | mutInd==mut d  =
      orderDeclRules' mutInd (acc<>(printDecl mods d)) (waitingRules++(printRules mods d)) tl mods
  | otherwise =
      orderDeclRules' (mut d) (acc<>(hcat waitingRules)<>(printDecl mods d)) (printRules mods d) tl mods

-- The main function --

dkCompileDef :: DkOptions -> DkModuleEnv -> IsMain -> Definition -> TCM (DkDefinition)
dkCompileDef _ _ _ (Defn {defName=n, theDef=d, defType=t, defMutual=MutId m}) =
  do tParams <- reconstructParametersInType t
     typ     <- return (translateType 0 [] tParams)
     typ     <- return (translateType 0 [] t)
     rules   <- extractRules n d
     return DkDefinition
       { name      = qname2DkName n
       , mut       = m
       , staticity = extractStaticity d
       , typ       = snd typ
       , kind      = getKind (fst typ) [] t
       , rules     = rules}

translateType :: NextIndex -> [DkIdent] -> Type -> (NextIndex,DkTerm)
translateType k l (El {_getSort=_, unEl=x}) = translateTerm k l x

extractStaticity :: Defn -> IsStatic
extractStaticity Axiom             = True
extractStaticity (DataOrRecSig {}) = True
extractStaticity GeneralizableVar  = True
extractStaticity (Function {})     = False
extractStaticity (Datatype {})     = True
extractStaticity (Record {})       = True
extractStaticity (Constructor {})  = True
extractStaticity (Primitive {})    = False

extractRules :: QName -> Defn -> TCM [DkRule]
extractRules n (Function {funCovering=f})     = mapM (clause2rule n) f
extractRules n (Datatype {dataClause=Just c}) = sequence [clause2rule n c]
extractRules n (Record {recClause=Just c})    = sequence [clause2rule n c]
extractRules n (Primitive {primClauses=p})    = mapM (clause2rule n) p
extractRules _ _                              = sequence []

clause2rule :: QName -> Clause -> TCM DkRule
clause2rule nam c =
  let ty =
        case clauseType c of
          Nothing -> error "Type of a clause shouldn't be Nothing"
          Just t  -> unArg t
  in
  case (clauseBody c) of
    Nothing  -> error "Unexpected empty RHS"
    Just r   ->
      addContext (clauseTel c) $
      do
        rr <-
          case r of
            Var _ _ -> return r
            otherwise -> reconstructParameters ty r
        imp <- isProjection nam
        implicits <-
          case imp of
            Nothing                             -> return Nothing
            Just Projection{projProper=Nothing} -> return Nothing
            Just Projection{projProper=Just n}  -> getNumberOfParameters n
        names <- getContextNames
        dkNames <- return $ map (\n -> name2DkIdent n) names
        (k, ctx) <- return $ extractContext 0 dkNames (clauseTel c)
        (kk,patts,nn) <- extractPatterns k dkNames (namedClausePats c)
        rhs <- return $ snd $ translateTerm kk dkNames rr
        return DkRule
          { context   = ctx
          , headsymb  = qname2DkName nam
          , implicits = fromMaybe 0 implicits
          , patts     = patts
          , rhs       = rhs
          }

extractContext :: NextIndex -> [DkIdent] -> Telescope -> (Int,DkCtx)
extractContext= extractContextAux []

extractContextAux :: [DkTerm] -> NextIndex -> [DkIdent] -> Telescope -> (Int,DkCtx)
extractContextAux acc k names EmptyTel                                    =
  (k, DkCtx (zip names acc))
extractContextAux acc k names (ExtendTel (Dom {unDom=t}) (Abs {unAbs=r})) =
  let (kk, typ) = translateType k names t in
  extractContextAux (typ:acc) kk names r

extractPatterns :: NextIndex -> [DkIdent] -> [NamedArg DeBruijnPattern] -> TCM (Int,[DkPattern],Int)
extractPatterns = auxPatt (-1) []

auxPatt ::  LastUsed -> [DkPattern] -> NextIndex ->[DkIdent] -> [NamedArg DeBruijnPattern] -> TCM (Int,[DkPattern],Int)
auxPatt n acc k l []        =
  return (k,reverse acc,n)
auxPatt n acc k l (p:patts) =
  do (kk, t, nn) <- extractPattern n k l p
     auxPatt (max n nn) (t:acc) kk l patts

extractPattern :: LastUsed -> NextIndex -> [DkIdent] -> NamedArg DeBruijnPattern -> TCM (Int,DkPattern,Int)
extractPattern n k l x =
  let pat = namedThing (unArg x) in
  case pat of
    VarP _ (DBPatVar {dbPatVarIndex=i}) ->
      return (k,DkVar (l!!i) i [], max i n)
    DotP _ t                           ->
      let (kk, term) = translateTerm k l t in
      return (kk, DkBrackets term, n)
    ConP (ConHead {conName=h}) _ tl     ->
      do (kFin, patts, nn) <- auxPatt n [] k l tl
         mbNbParams <- getNumberOfParameters h
         nbParams <- case mbNbParams of
                Nothing -> error "Why no Parameters?"
                Just n  -> return n
         return (kFin, DkFun (qname2DkName h) nbParams patts, max n nn)
    otherwise                           ->
      return (k, DkBrackets (DkFake ""), n)

translateTerm :: Int -> [DkIdent] -> Term -> (Int,DkTerm)
translateTerm k l (Var i [])                    = (k,DkDB (l!!i) i)
translateTerm k l (Var i (e:elims))             =
  let (kk, trElim) = translateElim k l e in
  let (kFin, trArgs) = auxVar kk l [] elims in
  (kFin, DkApp (DkDB (l!!i) i) trElim trArgs)
translateTerm k l (Lam _ ab)
  | absName ab=="_" =
      let id = "UNNAMED_VAR_" ++ (show k) in
      let (kk,body) = translateTerm (k+1) (id:l) (unAbs ab) in
      (kk, DkLam id Nothing body)
  | otherwise       =
      let id = absName ab in
      let (kk,body) = translateTerm k (id:l) (unAbs ab) in
      (kk,DkLam id Nothing body)
translateTerm k l (Lit _)                       = (k, DkFake "")
translateTerm k l (Def n [])                    = (k, DkConst (qname2DkName n))
translateTerm k l (Def n (e:elims))             =
  let (kk,trElim) = translateElim k l e in
  let (kFin,trArgs) = auxVar kk l [] elims in
  (kFin, DkApp (DkConst (qname2DkName n)) trElim trArgs)
translateTerm k l (Con (ConHead {conName=h}) _ [])        =
  (k, DkConst (qname2DkName h))
translateTerm k l (Con (ConHead {conName=h}) _ (e:elims)) =
  let (kk,trElim) = translateElim k l e in
  let (kFin,trArgs) = auxVar kk l [] elims in
  (kFin, DkApp (DkConst (qname2DkName h)) trElim trArgs)
translateTerm k l (Pi (Dom {unDom=t}) (Abs{absName=n, unAbs=u})) =
  case t of
    El {unEl=Con (ConHead {conName=h}) _ _} ->
      let dom = qname2DkName h in
        if dom == DkQualified ["Agda","Primitive"] "Level"
        then
          let (kFin, body) = translateType k (n:l) u in
          (kFin,DkQuantifLevel (getKind k (n:l) u) n body)
        else
          localAux
    El {unEl=Def h []} ->
      let dom = qname2DkName h in
        if dom == DkQualified ["Agda","Primitive"] "Level"
        then
          let (kFin, body) = translateType k (n:l) u in
          (kFin,DkQuantifLevel (getKind k (n:l) u) n body)
        else
          localAux
    otherwise -> localAux
    where
      localAux =
        case n of
          "_" ->
            let id = "UNNAMED_VAR_" ++ (show k) in
            let (kk, dom) = translateType (k+1) l t in
            let (kFin, body) = translateType kk (id:l) u in
            (kFin, DkProd (getKind kk l t) (getKind kk (id:l) u) id dom body)
          otherwise ->
            let (kk, dom) = translateType k l t in
            let (kFin, body) = translateType kk (n:l) u in
            (kFin, DkProd (getKind k l t) (getKind kk (n:l) u) n dom body)
translateTerm k l (Pi (Dom {unDom=t}) (NoAbs{absName=n, unAbs=u}))
  | n=="_" =
      let id = "UNNAMED_VAR_" ++ (show k) in
      let (kk, dom) = translateType (k+1) l t in
      let (kFin, body) = translateType kk l u in
      (kFin, DkProd (getKind (k+1) l t) (getKind kk l u) id dom body)
  | otherwise       =
      let (kk, dom) = translateType k l t in
      let (kFin, body) = translateType kk l u in
      (kFin, DkProd (getKind k l t) (getKind kk l u) n dom body)
translateTerm k l (Sort s)                      = (k, DkSort (extractSort k l s))
translateTerm k l (Level _)                     = (k, DkFake "")
translateTerm k l (MetaV {})                    = (k, DkFake "")
translateTerm k l (DontCare t)                  = translateTerm k l t
translateTerm k l (Dummy _ _)                   = (k, DkFake "")

auxVar :: Int -> [DkIdent] -> [DkTerm] -> [Elim] -> (Int,[DkTerm])
auxVar k l acc []       = (k,reverse acc)
auxVar k l acc (e:elim) =
  let (kk, t) = translateElim k l e in
  auxVar kk l (t:acc) elim

extractSort :: Int -> [DkIdent] -> Sort -> DkSort
extractSort k l (Type i)                  = DkSet (lvlFromLevel k l i)
extractSort k l (Prop i)                  = DkSet (lvlFromLevel k l i)
extractSort k l Inf                       = DkSetOmega
extractSort k l SizeUniv                  = DkSet (LvlInt 0)
extractSort k l (PiSort (Dom{unDom=s}) t) =
  DkPi (extractSort k l (_getSort s)) (extractSort k l (unAbs t))
extractSort k l (UnivSort s)              = DkUniv (extractSort k l s)
extractSort _ _ _                         = DkDefaultSort

translateElim :: Int -> [DkIdent] -> Elim -> (Int,DkTerm)
translateElim k l (Apply e)      = translateTerm k l (unArg e)
translateElim k l (Proj _ qn)    = (k,DkFake "")
translateElim k l (IApply _ _ _) = (k,DkFake "")

getKind :: Int -> [DkIdent] -> Type -> DkSort
getKind k l (El {_getSort=s}) = extractSort k l s

lvlFromLevel :: Int -> [DkIdent] -> Level -> Lvl
lvlFromLevel k l (Max [])                             = LvlInt 0
lvlFromLevel k l (Max ((ClosedLevel i):[]))           = LvlInt (fromInteger i)
lvlFromLevel k l (Max ((ClosedLevel i):tl))           =
  LvlMax (LvlInt (fromInteger i)) (lvlFromLevel k l (Max tl))
lvlFromLevel k l (Max ((Plus 0 (BlockedLevel _ t)):[])) =
  LvlTerm (snd (translateTerm k l t))
lvlFromLevel k l (Max ((Plus i (BlockedLevel _ t)):[])) =
  LvlPlus (LvlInt (fromInteger i)) (LvlTerm (snd (translateTerm k l t)))
lvlFromLevel k l (Max ((Plus 0 (BlockedLevel _ t)):tl)) =
  LvlMax (LvlTerm (snd (translateTerm k l t))) (lvlFromLevel k l (Max tl))
lvlFromLevel k l (Max ((Plus i (BlockedLevel _ t)):tl)) =
  LvlMax (LvlPlus (LvlInt (fromInteger i)) (LvlTerm (snd (translateTerm k l t)))) (lvlFromLevel k l (Max tl))
lvlFromLevel k l (Max ((Plus 0 (NeutralLevel _ t)):[])) =
  LvlTerm (snd (translateTerm k l t))
lvlFromLevel k l (Max ((Plus i (NeutralLevel _ t)):[])) =
  LvlPlus (LvlInt (fromInteger i)) (LvlTerm (snd (translateTerm k l t)))
lvlFromLevel k l (Max ((Plus 0 (NeutralLevel _ t)):tl)) =
  LvlMax (LvlTerm (snd (translateTerm k l t))) (lvlFromLevel k l (Max tl))
lvlFromLevel k l (Max ((Plus i (NeutralLevel _ t)):tl)) =
  LvlMax (LvlPlus (LvlInt (fromInteger i)) (LvlTerm (snd (translateTerm k l t)))) (lvlFromLevel k l (Max tl))
lvlFromLevel k l (Max ((Plus 0 (UnreducedLevel t)):[])) =
  LvlTerm (snd (translateTerm k l t))
lvlFromLevel k l (Max ((Plus i (UnreducedLevel t)):[])) =
  LvlPlus (LvlInt (fromInteger i)) (LvlTerm (snd (translateTerm k l t)))
lvlFromLevel k l (Max ((Plus 0 (UnreducedLevel t)):tl)) =
  LvlMax (LvlTerm (snd (translateTerm k l t))) (lvlFromLevel k l (Max tl))
lvlFromLevel k l (Max ((Plus i (UnreducedLevel t)):tl)) =
  LvlMax (LvlPlus (LvlInt (fromInteger i)) (LvlTerm (snd (translateTerm k l t)))) (lvlFromLevel k l (Max tl))

qname2DkName :: QName -> DkName
qname2DkName n = DkQualified (modName2DkModIdent (qnameModule n)) (name2DkIdent (qnameName n))

name2DkIdent :: Name -> DkIdent
name2DkIdent (Name {nameId=NameId w64 _,nameConcrete=CN.Name {CN.nameNameParts=n}}) =
  concat (map namePart2String n)
name2DkIdent (Name {nameId=NameId w64 _,nameConcrete=CN.NoName {}}) =
  "DEFAULT"

namePart2String :: CN.NamePart -> String
namePart2String CN.Hole  = "_"
namePart2String (CN.Id s) = s

modName2DkModIdent :: ModuleName -> DkModName
modName2DkModIdent (MName {mnameToList=l}) = map name2DkIdent l

type NextIndex = Int
type LastUsed = Int
