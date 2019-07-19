
module Agda2Dk.Compiler where

import Control.Monad.State
import Data.Maybe
import System.Directory (doesFileExist)
import Data.List
import Text.PrettyPrint
import Debug.Trace

import Agda.Compiler.Backend
import Agda.Interaction.Options
import qualified Agda.Syntax.Concrete.Name as CN
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.ReconstructParameters
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.Utils.Monad
import Agda.Utils.Pretty (pretty)

import Agda2Dk.DkSyntax

-- Backend callbacks ------------------------------------------------------

dkBackend :: Backend
dkBackend = Backend dkBackend'

dkBackend' :: Backend' DkOptions DkOptions DkModuleEnv () (Maybe DkDefinition)
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
  , optDkRegen   :: Bool
  }

defaultDkOptions :: DkOptions
defaultDkOptions = DkOptions
  { optDkCompile = False
  , optDkFlags   = []
  , optDkDir     = Nothing
  , optDkRegen   = False
  }

dkCommandLineFlags :: [OptDescr (Flag DkOptions)]
dkCommandLineFlags =
    [ Option []     ["dk"]     (NoArg compileDkFlag) "compile program using the Dk backend"
    , Option []     ["outDir"] (OptArg outp "DIR")  "output DIR"
    , Option []     ["regenerate"] (NoArg forceRegenDk)  "regenerate the Dedukti file even if it already exists"
    ]
  where
    compileDkFlag o = return $ o { optDkCompile = True}
    outp d o        = return $ o { optDkDir = d}
    forceRegenDk o  = return $ o { optDkRegen = True}

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
    ifM ((doesFileExist filePath) >>= \x -> return $ x && not (optDkRegen opts))
      (do putStrLn $ "Already generated "++filePath
          return (Skip ()))
      (do putStrLn $ "Generation of "++filePath
          return (Recompile ()))

dkPostModule :: DkOptions -> DkModuleEnv -> IsMain -> ModuleName -> [Maybe DkDefinition] -> TCM ()
dkPostModule opts _ _ mods defs =
  let concMods = modName2DkModIdent mods in
  let output = orderDeclRules (catMaybes defs) concMods in
  let dir = case optDkDir opts of Nothing -> ""
                                  Just s  -> s
  in
  let mod = intercalate "__" concMods in
  let filePath = dir++mod++".dk" in
  liftIO $
    do writeFile filePath (show output)
       putStrLn $ filePath ++ " has been created"

orderDeclRules :: [DkDefinition] -> DkModName -> Doc
orderDeclRules = orderDeclRules' 0 empty []

orderDeclRules' mutInd acc waitingRules []     mods = acc <> (hcat waitingRules)
orderDeclRules' mutInd acc waitingRules (d:tl) mods
  | mutInd==mut d  =
      orderDeclRules' mutInd (acc<>(printDecl mods d)) (waitingRules++(printRules mods d)) tl mods
  | otherwise =
      orderDeclRules' (mut d) (acc<>(hcat waitingRules)<>(printDecl mods d)) (printRules mods d) tl mods

-- The main function --

dkCompileDef :: DkOptions -> DkModuleEnv -> IsMain -> Definition -> TCM (Maybe DkDefinition)
dkCompileDef _ _ _ def@(Defn {defCopy=isCopy, defName=n, theDef=d, defType=t, defMutual=MutId m}) =
  if isCopy
  then return Nothing
  else
    do
      reportSDoc "agda2Dedukti" 2 $ return $ pretty def
      rules   <- extractRules n d
      tParams <- return t -- reconstructParametersInType t
      typ     <- return (translateType [] tParams)
      name    <- tcMonadQname2DkNameAux d n
      return $ Just DkDefinition
        { name      = name
        , mut       = m
        , staticity = extractStaticity d
        , typ       = typ
        , kind      = getKind [] t
        , rules     = rules}

translateType :: [DkIdent] -> Type -> DkTerm
translateType l (El {_getSort=_, unEl=x}) = translateTerm l x

extractStaticity :: Defn -> IsStatic
extractStaticity Axiom             = Static
extractStaticity (DataOrRecSig {}) = Static
extractStaticity GeneralizableVar  = Static
extractStaticity (Function {})     = Defin
extractStaticity (Datatype {})     = TypeConstr
extractStaticity (Record {})       = TypeConstr
extractStaticity (Constructor {})  = Static
extractStaticity (Primitive {})    = Defin

extractRules :: QName -> Defn -> TCM [DkRule]
extractRules n (Function {funCovering=f})     =
  do l <- mapM (clause2rule n) f
     return $ catMaybes l
extractRules n (Datatype {dataClause=Just c, dataPars=i, dataIxs=j}) =
  do l <- sequence [clause2rule n c, return $ Just $ decodedVersion n (i+j)]
     return $ catMaybes l
extractRules n (Record {recClause=Just c, recPars=i})    =
  do l <- sequence [clause2rule n c, return $ Just $ decodedVersion n i]
     return $ catMaybes l
extractRules n (Datatype {dataClause=Nothing, dataPars=i, dataIxs=j}) =
  do l <- return [Just $ decodedVersion n (i+j)]
     return $ catMaybes l
extractRules n (Record {recClause=Nothing, recPars=i})    =
  do l <- return [Just $ decodedVersion n i]
     return $ catMaybes l
extractRules n (Primitive {primClauses=p})    =
  do l <- mapM (clause2rule n) p
     return $ catMaybes l
extractRules _ _                              = sequence []

decodedVersion :: QName -> Int -> DkRule
decodedVersion nam i =
  let DkQualified mods (Nothing, n) = plainQname2DkName nam in
  let decodedName = DkQualified mods (Just "TYPE", n) in
  DkRule
  { context   = genCtx i
  , headsymb  = DkQualified ["naiveAgda"] (Nothing, "Term")
  , implicits = 1
  , patts     = [DkFun (plainQname2DkName nam) 0 (genVars i)]
  , rhs       = constructRhs (DkConst decodedName) i}
  where
    genCtx = genCtxAux []
    genCtxAux acc 0 = DkCtx acc
    genCtxAux acc i = genCtxAux ((idOfVarInd i, dummyTerm):acc) (i-1)
    genVars = genVarsAux []
    genVarsAux acc 0 = acc
    genVarsAux acc i = genVarsAux ((DkVar (idOfVarInd i) (i-1) []):acc) (i-1)
    constructRhs = constructRhsAux 0
    constructRhsAux j t i =
      if i==j
      then t
      else constructRhsAux (j+1) (DkApp t (DkDB (idOfVarInd (j+1)) (i-j-1))) i
    idOfVarInd i = (Nothing, "x"++ show i)
    dummyTerm = DkConst (DkLocal (Nothing, "DUMMY__TERM"))

clause2rule :: QName -> Clause -> TCM (Maybe DkRule)
clause2rule nam c =
  case (clauseBody c) of
    Nothing  -> return Nothing
    Just r   ->
      addContext (clauseTel c) $
      do
        imp <- isProjection nam
        implicits <- case imp of
                       Nothing                             -> return Nothing
                       Just Projection{projProper=Nothing} -> return Nothing
                       Just Projection{projProper=Just n}  -> getNumberOfParameters n
        names <- getContextNames
        reportSDoc "agda2Dedukti" 5 $ prettyTCM nam
        reportSDoc "agda2Dedukti" 5 $ return $ text $ show names
        reportSDoc "agda2Dedukti" 10 $ prettyTCM c
        reportSDoc "agda2Dedukti" 10 $ prettyTCM (clauseTel c)
        rr <-
          case clauseType c of
            Nothing -> return r
            Just t  -> reconstructParameters (unArg t) r
        dkNames <- return $ separateVars [] $ map (\n -> plainName2DkIdent n) names
        ctx <- return $ extractContext dkNames (clauseTel c)
        (patts,nn) <- extractPatterns dkNames (namedClausePats c)
        rhs <- return $ translateTerm dkNames rr
        headSymb <- tcMonadQname2DkName nam
        return $ Just DkRule
          { context   = ctx
          , headsymb  = headSymb
          , implicits = fromMaybe 0 implicits
          , patts     = patts
          , rhs       = rhs
          }

extractContext :: [DkIdent] -> Telescope -> DkCtx
extractContext = extractContextAux []

extractContextAux :: [DkTerm] -> [DkIdent] -> Telescope -> DkCtx
extractContextAux acc names EmptyTel                                    =
  DkCtx (zip names acc)
extractContextAux acc names (ExtendTel (Dom {unDom=t}) (Abs {unAbs=r})) =
  let typ = translateType names t in
  extractContextAux (typ:acc) names r

extractPatterns :: [DkIdent] -> [NamedArg DeBruijnPattern] -> TCM ([DkPattern],LastUsed)
extractPatterns = auxPatt (-1) []

auxPatt ::  LastUsed -> [DkPattern] -> [DkIdent] -> [NamedArg DeBruijnPattern] -> TCM ([DkPattern],LastUsed)
auxPatt n acc l []        =
  return (reverse acc,n)
auxPatt n acc l (p:patts) =
  do (t, nn) <- extractPattern n l p
     auxPatt (max n nn) (t:acc) l patts

extractPattern :: LastUsed -> [DkIdent] -> NamedArg DeBruijnPattern -> TCM (DkPattern,LastUsed)
extractPattern n l x =
  let pat = namedThing (unArg x) in
  case pat of
    VarP _ (DBPatVar {dbPatVarIndex=i}) ->
      return (DkVar (l!!i) i [], max i n)
    DotP _ t                           ->
      let term = translateTerm l t in
      return (DkBrackets term, n)
    ConP (ConHead {conName=h}) _ tl     ->
      do (patts, nn) <- auxPatt n [] l tl
         mbNbParams <- getNumberOfParameters h
         nbParams <- case mbNbParams of
                Nothing -> error "Why no Parameters?"
                Just n  -> return n
         return (DkFun (labeledQname2DkName h) nbParams patts, max n nn)
    otherwise                           ->
      error "Unexpected pattern"


translateElim :: [DkIdent] -> DkTerm -> Elims -> DkTerm
translateElim l t []                  = t
translateElim l t ((Apply e):tl)      =
  let arg = translateTerm l (unArg e) in
  translateElim l (DkApp t arg) tl
translateElim l t ((Proj _ qn):tl)    =
  let proj = DkConst $ labeledQname2DkName qn in
  translateElim l (DkApp proj t) tl
translateElim l t ((IApply _ _ _):tl) = error "Unexpected IApply"


translateTerm :: [DkIdent] -> Term -> DkTerm
translateTerm l (Var i elims) =
  translateElim l (DkDB (l!!i) i) elims
translateTerm l (Lam _ ab) =
  let n=absName ab in
  let id = unusedVar l $ idOfVar (if n=="_" then "UNNAMED_VAR_" else n) in
  let body = translateTerm (id:l) (unAbs ab) in
  DkLam id Nothing body
translateTerm l (Lit (LitNat _ i))            =
  toBuildInNat i
translateTerm l (Def n elims)                    =
  translateElim l (DkConst (plainQname2DkName n)) elims
translateTerm l (Con (ConHead {conName=h}) _ elims)        =
  translateElim l  (DkConst (labeledQname2DkName h)) elims
translateTerm l (Pi (Dom {unDom=t}) (Abs{absName=n, unAbs=u})) =
  case t of
    El {unEl=Con (ConHead {conName=h}) _ _} ->
      let dom = plainQname2DkName h in
        if dom == DkQualified ["Agda","Primitive"] (Nothing, "Level")
        then
          let id = unusedVar l $ idOfVar n in
          let body = translateType (id:l) u in
          DkQuantifLevel (getKind (id:l) u) id body
        else
          localAux
    El {unEl=Def h []} ->
      let dom = plainQname2DkName h in
        if dom == DkQualified ["Agda","Primitive"] (Nothing, "Level")
        then
          let id = unusedVar l $ idOfVar n in
          let body = translateType (id:l) u in
          DkQuantifLevel (getKind (id:l) u) id body
        else
          localAux
    otherwise -> localAux
    where
      localAux =
        let id = unusedVar l $ idOfVar (if n=="_" then "UNNAMED_VAR_" else n) in
        let dom = translateType l t in
        let body = translateType (id:l) u in
        DkProd (getKind l t) (getKind (id:l) u) id dom body
translateTerm l (Pi (Dom {unDom=t}) (NoAbs{absName=n, unAbs=u})) =
  let id = unusedVar l $ idOfVar (if n=="_" then "UNNAMED_VAR_" else n) in
  let dom = translateType l t in
  let body = translateType l u in
  DkProd (getKind l t) (getKind l u) id dom body
translateTerm l (Sort s)                      = DkSort (extractSort l s)
translateTerm l (Level lev)                   = DkLevel (lvlFromLevel l lev)
translateTerm l (MetaV {})                    = error "Not implemented yet : MetaV"
translateTerm l (DontCare t)                  = translateTerm l t
translateTerm l (Dummy _ _)                   = error "Not implemented yet : Dummy"
translateTerm l (Lit _)                       = error "Not implemented yet : Lit"

extractSort :: [DkIdent] -> Sort -> DkSort
extractSort l (Type i)                  = DkSet (lvlFromLevel l i)
extractSort l (Prop i)                  = DkSet (lvlFromLevel l i)
extractSort l Inf                       = DkSetOmega
extractSort l SizeUniv                  = DkSet (LvlInt 0)
extractSort l (PiSort (Dom{unDom=s}) t) =
  DkPi (extractSort l (_getSort s)) (extractSort l (unAbs t))
extractSort l (UnivSort s)              = DkUniv (extractSort l s)
extractSort _ _                         = DkDefaultSort

getKind :: [DkIdent] -> Type -> DkSort
getKind l (El {_getSort=s}) = extractSort l s

lvlFromLevel :: [DkIdent] -> Level -> Lvl
lvlFromLevel l (Max [])                             = LvlInt 0
lvlFromLevel l (Max ((ClosedLevel i):[]))           = LvlInt (fromInteger i)
lvlFromLevel l (Max ((ClosedLevel i):tl))           =
  LvlMax (LvlInt (fromInteger i)) (lvlFromLevel l (Max tl))
lvlFromLevel l (Max ((Plus 0 (BlockedLevel _ t)):[])) =
  LvlTerm (translateTerm l t)
lvlFromLevel l (Max ((Plus i (BlockedLevel _ t)):[])) =
  LvlPlus (LvlInt (fromInteger i)) (LvlTerm (translateTerm l t))
lvlFromLevel l (Max ((Plus 0 (BlockedLevel _ t)):tl)) =
  LvlMax (LvlTerm (translateTerm l t)) (lvlFromLevel l (Max tl))
lvlFromLevel l (Max ((Plus i (BlockedLevel _ t)):tl)) =
  LvlMax (LvlPlus (LvlInt (fromInteger i)) (LvlTerm (translateTerm l t))) (lvlFromLevel l (Max tl))
lvlFromLevel l (Max ((Plus 0 (NeutralLevel _ t)):[])) =
  LvlTerm (translateTerm l t)
lvlFromLevel l (Max ((Plus i (NeutralLevel _ t)):[])) =
  LvlPlus (LvlInt (fromInteger i)) (LvlTerm (translateTerm l t))
lvlFromLevel l (Max ((Plus 0 (NeutralLevel _ t)):tl)) =
  LvlMax (LvlTerm (translateTerm l t)) (lvlFromLevel l (Max tl))
lvlFromLevel l (Max ((Plus i (NeutralLevel _ t)):tl)) =
  LvlMax (LvlPlus (LvlInt (fromInteger i)) (LvlTerm (translateTerm l t))) (lvlFromLevel l (Max tl))
lvlFromLevel l (Max ((Plus 0 (UnreducedLevel t)):[])) =
  LvlTerm (translateTerm l t)
lvlFromLevel l (Max ((Plus i (UnreducedLevel t)):[])) =
  LvlPlus (LvlInt (fromInteger i)) (LvlTerm (translateTerm l t))
lvlFromLevel l (Max ((Plus 0 (UnreducedLevel t)):tl)) =
  LvlMax (LvlTerm (translateTerm l t)) (lvlFromLevel l (Max tl))
lvlFromLevel l (Max ((Plus i (UnreducedLevel t)):tl)) =
  LvlMax (LvlPlus (LvlInt (fromInteger i)) (LvlTerm (translateTerm l t))) (lvlFromLevel l (Max tl))

plainQname2DkName :: QName -> DkName
plainQname2DkName n
  | mnameToList (qnameModule n) == [] = DkLocal (Nothing, name2String (qnameName n))
  | otherwise = DkQualified (modName2DkModIdent (qnameModule n)) (Nothing, name2String (qnameName n))

labeledQname2DkName :: QName -> DkName
labeledQname2DkName n =
  let l = modName2DkModIdent (qnameModule n) in
  let id = (Just $ last l, name2String (qnameName n)) in
  if init l == []
  then DkLocal id
  else DkQualified (init l) id

name2String :: Name -> String
name2String (Name {nameId=NameId w64 _,nameConcrete=CN.Name {CN.nameNameParts=n}}) =
  concat (map namePart2String n)
name2String (Name {nameId=NameId w64 _,nameConcrete=CN.NoName {}}) =
  "DEFAULT"

namePart2String :: CN.NamePart -> String
namePart2String CN.Hole  = "_"
namePart2String (CN.Id s) = s

modName2DkModIdent :: ModuleName -> DkModName
modName2DkModIdent (MName {mnameToList=l}) = map name2String l

type LastUsed = Int

idOfVar :: String -> DkIdent
idOfVar n = (Nothing, n)

plainName2DkIdent :: Name -> DkIdent
plainName2DkIdent n = idOfVar $ name2String n

tcMonadQname2DkNameAux :: Defn -> QName -> TCM DkName
tcMonadQname2DkNameAux (Function{})    nam = do
  imp <- isProjection nam
  case imp of
    Nothing                             -> return $ plainQname2DkName nam
    Just Projection{projProper=Nothing} -> return $ plainQname2DkName nam
    Just Projection{projProper=Just n}  -> return $ labeledQname2DkName nam
tcMonadQname2DkNameAux (Constructor{}) nam = return $ labeledQname2DkName nam
tcMonadQname2DkNameAux _               nam = return $ plainQname2DkName nam

tcMonadQname2DkName nam = do
  def <- getConstInfo nam
  tcMonadQname2DkNameAux (theDef def) nam

toBuildInNat :: Integer -> DkTerm
toBuildInNat i =
  let zero = DkConst $ DkQualified ["Agda", "Builtin", "Nat"] (Just "Nat", "zero") in
  let suc = DkConst $ DkQualified ["Agda", "Builtin", "Nat"] (Just "Nat", "suc") in
  iterate (\x -> DkApp suc x) zero !! (fromInteger i)

unusedVar :: [DkIdent] -> DkIdent -> DkIdent
unusedVar l = unusedVarAux 0 (map snd l)

unusedVarAux i used (_, x)
  | elem (appInd i x) used = unusedVarAux (i+1) used (Nothing, x)
  | otherwise              = (Nothing,appInd i x)
  where appInd i x = if i==0 then x else x++(show i)

separateVars :: [String] -> [DkIdent] -> [DkIdent]
separateVars used []     = []
separateVars used (h:tl) =
  let v = unusedVarAux 0 used h in
  v:(separateVars ((snd v):used) tl)
