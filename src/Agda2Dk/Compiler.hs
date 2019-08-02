
module Agda2Dk.Compiler where

import Control.Monad.State
import Data.Maybe
import System.Directory (doesFileExist)
import Data.Int
import Data.List
import Text.PrettyPrint
import Debug.Trace

import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Interaction.Options
import qualified Agda.Syntax.Concrete.Name as CN
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Literal
import Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.ReconstructParameters
import Agda.TypeChecking.RecordPatterns
import Agda.TypeChecking.Records
import Agda.TypeChecking.EtaExpand
import Agda.TypeChecking.Substitute.Class
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.Utils.Monad
import Agda.Utils.Pretty (pretty)
import Agda.Utils.Impossible

import Agda2Dk.DkSyntax

-- Backend callbacks ------------------------------------------------------

dkBackend :: Backend
dkBackend = Backend dkBackend'

dkBackend' :: Backend' DkOptions DkOptions DkModuleEnv () DkCompiled
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

type DkCompiled = Maybe (Int32,DkDefinition)

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
      (return (Skip ()))
      (do putStrLn $ "Generation of "++filePath
          return (Recompile ()))

dkPostModule :: DkOptions -> DkModuleEnv -> IsMain -> ModuleName -> [DkCompiled] -> TCM ()
dkPostModule opts _ _ mods defs =
  let concMods = modName2DkModIdent mods in
  let dir = case optDkDir opts of Nothing -> ""
                                  Just s  -> s
  in
  let mod = intercalate "__" concMods in
  let filePath = dir++mod++".dk" in
  do
    output <- orderDeclRules (catMaybes defs) concMods
    liftIO $
      do
        ss <- return $ show output
        writeFile filePath ss

orderDeclRules :: [(Int32,DkDefinition)] -> DkModName -> TCM Doc
orderDeclRules l = orderDeclRules' 0 empty empty [] (sortOn fst l)

orderDeclRules' mut accTy accOther waitingRules []          mods =
  return $ accTy <> accOther <> (hcat waitingRules)
orderDeclRules' mut accTy accOther waitingRules ((m,d):tl) mods
  | m==mut =
    case staticity d of
      TypeConstr -> orderDeclRules' mut (accTy<>(printDecl mods d)) accOther (waitingRules++(printRules mods d)) tl mods
      _ -> orderDeclRules' mut accTy (accOther<>(printDecl mods d)) (waitingRules++(printRules mods d)) tl mods
  | otherwise =
    case staticity d of
      TypeConstr -> orderDeclRules' m (accTy<>accOther<>(hcat waitingRules)<>(printDecl mods d)) empty (printRules mods d) tl mods
      _ -> orderDeclRules' m (accTy<>accOther<>(hcat waitingRules)) (printDecl mods d) (printRules mods d) tl mods

-- The main function --

dkCompileDef :: DkOptions -> DkModuleEnv -> IsMain -> Definition -> TCM DkCompiled
dkCompileDef _ _ _ def@(Defn {defCopy=isCopy, defName=n, theDef=d, defType=t, defMutual=MutId m}) =
  if isCopy
  then return Nothing
  else
    do
      reportSDoc "agda2Dedukti" 3 $ (text "Compiling definition of" <+>) <$> prettyTCM n
      reportSDoc "agda2Dedukti" 60 $ return $ text $ show def
      rules   <- extractRules n d
      tExpand <- checkInternalType' etaExpandAction t
      tParam  <- reconstructParametersInType' etaExpandAction tExpand
      typ     <- translateType tParam
      name    <- qName2DkName n
      kk      <- getKind t
      stat    <- extractStaticity n d
      return $ Just (m,DkDefinition
        { name      = name
        , staticity = stat
        , typ       = typ
        , kind      = kk
        , rules     = rules})

translateType :: Type -> TCM DkTerm
translateType (El {unEl=ty}) = translateTerm ty

extractStaticity :: QName -> Defn -> TCM IsStatic
extractStaticity _ Axiom             = return Static
extractStaticity _ (DataOrRecSig {}) = return Static
extractStaticity _ GeneralizableVar  = return Static
extractStaticity n (Function {})     = do
  test <- isRecordConstructor n
  return $ case test of
    Nothing -> Defin
    Just {} -> Static
extractStaticity _ (Datatype {})     = return TypeConstr
extractStaticity _ (Record {})       = return TypeConstr
extractStaticity _ (Constructor {})  = return Static
extractStaticity _ (Primitive {})    = return Defin

extractRules :: QName -> Defn -> TCM [DkRule]
extractRules n (Function {funCovering=f})     =
  do
    l <- mapM (clause2rule n) f
    return $ catMaybes l
extractRules n (Datatype {dataClause=Just c, dataPars=i, dataIxs=j}) =
  do l <- sequence [clause2rule n c, decodedVersion n (i+j) >>= (return . Just)]
     return $ catMaybes l
extractRules n (Record {recClause=Just c, recPars=i})    =
  do l <- sequence [clause2rule n c, decodedVersion n i >>= (return . Just)]
     return $ catMaybes l
extractRules n (Datatype {dataClause=Nothing, dataPars=i, dataIxs=j}) =
  do l <- sequence [decodedVersion n (i+j) >>= (return . Just)]
     return $ catMaybes l
extractRules n (Record {recClause=Nothing, recPars=i})    =
  do l <- sequence [decodedVersion n i >>= (return . Just)]
     return $ catMaybes l
extractRules n (Primitive {primClauses=p})    =
  do
    recordCleaned <- mapM translateRecordPatterns p
    l <- mapM (clause2rule n) recordCleaned
    return $ catMaybes l
extractRules _ _                              = sequence []

decodedVersion :: QName -> Int -> TCM DkRule
decodedVersion nam i = do
  nn@(DkQualified mods pseudo n) <- qName2DkName nam
  let decodedName = DkQualified mods ("TYPE":pseudo) n
  let hd = DkQualified ["naiveAgda"] [] "Term"
  return $ DkRule
    { context   = genCtx i
    , headsymb  = hd
    , patts     = [DkJoker,DkFun nn (genVars i)]
    , rhs       = constructRhs (DkConst decodedName) i}
  where
    genCtx = genCtxAux []
    genCtxAux acc 0 = acc
    genCtxAux acc i = genCtxAux (name2DkIdentInd i:acc) (i-1)
    genVars = genVarsAux []
    genVarsAux acc 0 = acc
    genVarsAux acc i = genVarsAux ((DkVar (name2DkIdentInd i) (i-1) []):acc) (i-1)
    constructRhs = constructRhsAux 0
    constructRhsAux j t i =
      if i==j
      then t
      else constructRhsAux (j+1) (DkApp t (DkDB (name2DkIdentInd (j+1)) (i-j-1))) i
    name2DkIdentInd i = "x"++ show i

clause2rule :: QName -> Clause -> TCM (Maybe DkRule)
clause2rule nam c = do
  reportSDoc "agda2Dedukti" 5  $ ((text "We are treating:") <+>) <$> (prettyTCM nam)
  reportSDoc "agda2Dedukti" 10 $ return $ (text "The clause is") <+> (pretty c)
  reportSDoc "agda2Dedukti" 20 $ ((text "In the context:") <+> ) <$> (prettyTCM (clauseTel c))
  reportSDoc "agda2Dedukti" 20 $ return $ (text "The type is:") <+> (pretty (clauseType c))
  reportSDoc "agda2Dedukti" 20 $ return $ (text "The body is:") <+> (pretty (clauseBody c))
  reportSDoc "agda2Dedukti" 50 $ return $ text $ "More precisely:" ++ show (clauseBody c)
  isProj <- isProjection nam
  -- c <-
    -- case isProj of
    --   Nothing ->
    --     translateRecordPatterns' AllRecordPatterns cc
    --   Just Projection{projProper=Nothing} ->
    --     translateRecordPatterns' AllRecordPatterns cc
    --   Just{} -> do
    --      reportSDoc "agda2Dedukti" 30 $ (<+> text " is considered as a projection") <$> (prettyTCM nam)
         -- return cc
  -- reportSDoc "agda2Dedukti" 30 $ ((text "The new clause is") <+>) <$> (prettyTCM c)
  -- reportSDoc "agda2Dedukti" 30 $ ((text "In the context:") <+> ) <$> (prettyTCM (clauseTel c))
  -- reportSDoc "agda2Dedukti" 30 $ return $ (text "The new body is:") <+> (pretty (clauseBody c))
  -- reportSDoc "agda2Dedukti" 50 $ return $ text $ "More precisely:" ++ show (clauseBody c)
  case (clauseBody c) of
    Nothing  -> return Nothing
    Just r   ->
      addContext (clauseTel c) $
      modifyContext separateVars $
      do
        imp <- isProjection nam
        implicits <-
          case imp of
            Nothing                             -> return 0
            Just Projection{projProper=Nothing} -> return 0
            Just Projection{projProper=Just n}  ->
              (fromMaybe __IMPOSSIBLE__) <$> getNumberOfParameters n
        tele <- getContext
        ctx <- extractContext tele
        let preLhs = Def nam (patternsToElims (namedClausePats c))
        rr <-
          case clauseType c of
            Nothing -> return r
            Just t  -> do
              reportSDoc "agda2Dedukti" 20 $ return $ (text "Type is:") <+> pretty t
              r1 <- deepEtaExpand r (unArg t)
              reportSDoc "agda2Dedukti" 20 $ return $ (text "Eta expansion done")
              reconstructParameters' etaExpandAction (unArg t) r
        reportSDoc "agda2Dedukti" 30 $ return $ text "Parameters reconstructed"
        reportSDoc "agda2Dedukti" 40 $ return $ (text "The final body is") <+> (pretty rr)
        (patts,_) <- extractPatterns (namedClausePats c)
        let impArgs = implicitArgs implicits (reverse ctx)
        rhs <- translateTerm rr
        headSymb <- qName2DkName nam
        return $ Just DkRule
          { context   = ctx
          , headsymb  = headSymb
          , patts     = impArgs ++ patts
          , rhs       = rhs
          }

          where
            implicitArgs 0 locCtx = []
            implicitArgs n (h:tl) =
              (DkVar h (length tl) []):(implicitArgs (n-1) tl)


-- etaExpandAction :: Action TCM
-- etaExpandAction = defaultAction {preAction = etaExpansion}

-- etaExpansion :: Type -> Term -> TCM Term
-- etaExpansion t u = do
--   tRed <- reduce t
--   isRec <- isEtaRecordType =<< tRed
--   case isRec of
--     Nothing ->
--     Just{} -> do
--       (_,uExpand) <- etaExpandAtRecordType t u
--       return uExpand

extractContext :: Context -> TCM DkCtx
extractContext = extractContextAux []

extractContextAux :: DkCtx -> Context -> TCM DkCtx
extractContextAux acc []                                    =
  return $ reverse acc
extractContextAux acc (Dom {unDom=(n,t)}:r) =
  extractContextAux (name2DkIdent n:acc) r

extractPatterns :: [NamedArg DeBruijnPattern] -> TCM ([DkPattern],LastUsed)
extractPatterns = auxPatt (-1) []

auxPatt ::  LastUsed -> [DkPattern] -> [NamedArg DeBruijnPattern] -> TCM ([DkPattern],LastUsed)
auxPatt n acc []        =
  return (reverse acc,n)
auxPatt n acc (p:patts) =
  do (t, nn) <- extractPattern n p
     auxPatt (max n nn) (t:acc) patts

extractPattern :: LastUsed -> NamedArg DeBruijnPattern -> TCM (DkPattern,LastUsed)
extractPattern n x =
  let pat = namedThing (unArg x) in
  case pat of
    VarP _ (DBPatVar {dbPatVarIndex=i}) ->
      do
        nam <- nameOfBV i
        return (DkVar (name2DkIdent nam) i [], max i n)
    DotP _ t                           ->
      do term <- translateTerm t
         return (DkBrackets term, n)
    ConP (ConHead {conName=h}) ci tl     ->
      do
        (patts, nn) <- auxPatt n [] tl
        mbNbParams <- getNumberOfParameters h
        nbParams <-
          case mbNbParams of
            Nothing -> error "Why no Parameters?"
            Just n  -> return n
        nam <- qName2DkName h
        let args = (replicate nbParams DkJoker) ++ patts
        return (DkFun nam args, max n nn)
    LitP l                              -> return (DkBuiltin (translateLiteral l),n)
    ProjP _ nam                         ->
      do
        imp <- isProjection nam
        mbNbParams <-
          case imp of
            Nothing                             -> error "What is this projection !?"
            Just Projection{projProper=Nothing} -> error "What is this projection !?"
            Just Projection{projProper=Just n}  -> getNumberOfParameters n
        nbParams <-
          case mbNbParams of
            Nothing -> error "Why no Parameters?"
            Just n  -> return n
        dkNam <- qName2DkName nam
        let args = (replicate nbParams DkJoker)
        return (DkFun dkNam args, n)
    otherwise                           ->
      error "Unexpected pattern of HoTT"

translateElim :: DkTerm -> Term -> Elims -> TCM DkTerm
translateElim t tAg []                  = return t
translateElim t tAg (el@(Apply e):tl)      =
  do arg <- translateTerm (unArg e)
     translateElim (DkApp t arg) (addEl tAg el) tl
translateElim t tAg (el@(Proj _ qn):tl)    = do
  reportSDoc "agda2Dedukti" 2 $ prettyTCM (applyE tAg [el])
  error "Unspining not performed!"
  -- let proj = DkConst $ qName2DkName qn in
  -- do
  --   reportSDoc "agda2Dedukti" 15 $ (prettyTCM tAg) >>= (\x -> return $ (text "The term:") <+> x)
  --   reportSDoc "agda2Dedukti" 15 $ (prettyTCM el) >>= (\x -> return $ (text "Is eliminated with:") <+> x)
  --   def <- getConstInfo qn
  --   let tyProj = defType def
  --   reportSDoc "agda2Dedukti" 15 $ (prettyTCM tyProj) >>= (\x -> return $ (text "Of type:") <+> x)
  --   let nbPar = countHiddenArgs tyProj
  --   reportSDoc "agda2Dedukti" 16 $ return $ text $ "Hence has "++show nbPar++" parameters"
  --   res <-
  --     do
  --       ty <- infer tAg
  --       reportSDoc "agda2Dedukti" 2 $ (prettyTCM ty) >>= (\x -> return $ (text "Inferred type:") <+> x)
  --       dkTy <-
  --         case unEl ty of
  --           Dummy _ _ -> appNbDummyHd nbPar
  --           _         -> translateType ty
  --       reportSDoc "agda2Dedukti" 2 $ return $ (text "Translated as:") <+> (prettyDk [] dkTy)
  --       return $ replaceHd proj dkTy
  --   translateElim (DkApp res t) (addEl tAg el) tl
translateElim t tAg ((IApply _ _ _):tl) = error "Unexpected IApply"


translateTerm :: Term -> TCM DkTerm
translateTerm (Var i elims) =
  do
    nam <- nameOfBV i
    translateElim (DkDB (name2DkIdent nam) i) (Var i []) elims
translateTerm (Lam _ ab) =
  do
    ctx <- getContext
    let n = freshStr ctx (absName ab)
    addContext n $
      do
        body <- translateTerm (unAbs ab)
        nam <- nameOfBV 0
        return $ DkLam (name2DkIdent nam) Nothing body
translateTerm (Lit l)            =
  return $ translateLiteral l
translateTerm (Def n elims)                    = do
  nam <- qName2DkName n
  translateElim (DkConst nam) (Def n []) elims
translateTerm (Con hh@(ConHead {conName=h}) i elims)        = do
  nam <- qName2DkName h
  translateElim (DkConst nam) (Con hh i []) elims
translateTerm (Pi d@(Dom {unDom=t}) (Abs{absName=n, unAbs=u})) =
  case t of
    El {unEl=Def h []} -> do
      dom <- qName2DkName h
      if dom == DkQualified ["Agda","Primitive"] [] "Level"
      then
        do
          ctx <- getContext
          let nn = freshStr ctx n
          addContext (nn,d) $
            do
              body <-translateType u
              ku <- getKind u
              nam <- nameOfBV 0
              return $ DkQuantifLevel ku (name2DkIdent nam) body
      else
          localAux
    otherwise -> localAux
    where
      localAux =
        do
          ctx <- getContext
          let nn = freshStr ctx n
          dom <- translateType t
          body <- addContext (nn,d) $ translateType u
          kt <- getKind t
          ku <- addContext (nn,d) $ getKind u
          nam <- addContext (nn,d) $ nameOfBV 0
          return $ DkProd kt ku (name2DkIdent nam) dom body
translateTerm (Pi d@(Dom {unDom=t}) (NoAbs{absName=n, unAbs=u})) =
  do
    ctx <- getContext
    let nn = freshStr ctx n
    dom <- translateType t
    body <- translateType u
    kt <- getKind t
    ku <- getKind u
    nam <- addContext (nn,d) $ nameOfBV 0
    return $ DkProd kt ku (name2DkIdent nam) dom body
translateTerm (Sort s)                      =
  do ss <- extractSort s
     return $ DkSort ss
translateTerm (Level lev)                   =
  do lv <- lvlFromLevel lev
     return $ DkLevel lv
translateTerm (MetaV {})                    = error "Not implemented yet : MetaV"
translateTerm (DontCare t)                  = translateTerm t
translateTerm (Dummy _ _)                   = error "Not implemented yet : Dummy"

extractSort :: Sort -> TCM DkSort
extractSort (Type i)                  =
  do lv <- lvlFromLevel i
     return $ DkSet lv
extractSort (Prop i)                  =
  do lv <- lvlFromLevel i
     return $ DkProp lv
extractSort Inf                       = return DkSetOmega
extractSort SizeUniv                  = return $ DkSet (LvlInt 0)
extractSort (PiSort (Dom{unDom=s}) t) =
  do dom <- extractSort (_getSort s)
     codom <- extractSort (unAbs t)
     return $ DkPi dom codom
extractSort (UnivSort s)              =
  do ss <- extractSort s
     return $ DkUniv ss
extractSort _                         = return DkDefaultSort

getKind :: Type -> TCM DkSort
getKind (El {_getSort=s}) = extractSort s

lvlFromLevel :: Level -> TCM Lvl
lvlFromLevel (Max [])                             = return $ LvlInt 0
lvlFromLevel (Max ((ClosedLevel i):[]))           = return $ LvlInt (fromInteger i)
lvlFromLevel (Max ((ClosedLevel i):tl))           =
  do r <- lvlFromLevel (Max tl)
     return $ LvlMax (LvlInt (fromInteger i)) r
lvlFromLevel (Max ((Plus 0 (BlockedLevel _ t)):[])) =
  do tt <- translateTerm t
     return $ LvlTerm tt
lvlFromLevel (Max ((Plus i (BlockedLevel _ t)):[])) =
  do tt <- translateTerm t
     return $ LvlPlus (LvlInt (fromInteger i)) (LvlTerm tt)
lvlFromLevel (Max ((Plus 0 (BlockedLevel _ t)):tl)) =
  do r <- lvlFromLevel (Max tl)
     tt <- translateTerm t
     return $ LvlMax (LvlTerm tt) r
lvlFromLevel (Max ((Plus i (BlockedLevel _ t)):tl)) =
  do r <- lvlFromLevel (Max tl)
     tt <- translateTerm t
     return $ LvlMax (LvlPlus (LvlInt (fromInteger i)) (LvlTerm tt)) r
lvlFromLevel (Max ((Plus 0 (NeutralLevel _ t)):[])) =
  do tt <- translateTerm t
     return $ LvlTerm tt
lvlFromLevel (Max ((Plus i (NeutralLevel _ t)):[])) =
  do tt <- translateTerm t
     return $ LvlPlus (LvlInt (fromInteger i)) (LvlTerm tt)
lvlFromLevel (Max ((Plus 0 (NeutralLevel _ t)):tl)) =
  do r <- lvlFromLevel (Max tl)
     tt <- translateTerm t
     return $ LvlMax (LvlTerm tt) r
lvlFromLevel (Max ((Plus i (NeutralLevel _ t)):tl)) =
  do r <- lvlFromLevel (Max tl)
     tt <- translateTerm t
     return $ LvlMax (LvlPlus (LvlInt (fromInteger i)) (LvlTerm tt)) r
lvlFromLevel (Max ((Plus 0 (UnreducedLevel t)):[])) =
  do tt <- translateTerm t
     return $ LvlTerm tt
lvlFromLevel (Max ((Plus i (UnreducedLevel t)):[])) =
  do tt <- translateTerm t
     return $ LvlPlus (LvlInt (fromInteger i)) (LvlTerm tt)
lvlFromLevel (Max ((Plus 0 (UnreducedLevel t)):tl)) =
  do r <- lvlFromLevel (Max tl)
     tt <- translateTerm t
     return $ LvlMax (LvlTerm tt) r
lvlFromLevel (Max ((Plus i (UnreducedLevel t)):tl)) =
  do r <- lvlFromLevel (Max tl)
     tt <- translateTerm t
     return $ LvlMax (LvlPlus (LvlInt (fromInteger i)) (LvlTerm tt)) r

translateLiteral :: Literal -> DkTerm
translateLiteral (LitNat    _ i)   = toBuiltinNat i
translateLiteral (LitWord64 _ _)   = error "Unexpected literal Word64"
translateLiteral (LitFloat  _ _)   = error "Unexpected literal Float"
translateLiteral (LitString _ _)   = error "Unexpected literal String"
translateLiteral (LitChar   _ _)   = error "Unexpected literal Char"
translateLiteral (LitQName  _ _)   = error "Unexpected literal QName"
translateLiteral (LitMeta   _ _ _) = error "Unexpected literal Meta"

toBuiltinNat :: Integer -> DkTerm
toBuiltinNat i =
  let zero = DkConst $ DkQualified ["Agda", "Builtin", "Nat"] ["Nat"] "zero" in
  let suc = DkConst $ DkQualified ["Agda", "Builtin", "Nat"] ["Nat"] "suc" in
  iterate (\x -> DkApp suc x) zero !! (fromInteger i)

--------------------------------------------------------------------------------
-- Translation of Name and QName function
--------------------------------------------------------------------------------

qName2DkName :: QName -> TCM DkName
qName2DkName QName{qnameModule=mods, qnameName=nam} = do
  topMod <- topLevelModuleName mods
  let otherMods = stripPrefix (mnameToList topMod) (mnameToList mods)
  return $
    DkQualified (modName2DkModIdent topMod) (maybe [] (map name2DkIdent) otherMods) (name2DkIdent nam)

name2DkIdent :: Name -> DkIdent
name2DkIdent (Name {nameConcrete=CN.Name {CN.nameNameParts=n}}) =
  concat (map namePart2String n)
name2DkIdent (Name {nameConcrete=CN.NoName {}}) =
  "DEFAULT"

namePart2String :: CN.NamePart -> String
namePart2String CN.Hole  = "_"
namePart2String (CN.Id s) = s

modName2DkModIdent :: ModuleName -> DkModName
modName2DkModIdent (MName {mnameToList=l}) = map name2DkIdent l

type LastUsed = Int

separateVars :: Context -> Context
separateVars = separateAux ["_"]

separateAux used [] = []
separateAux used ((d@Dom{unDom=(n@Name{nameConcrete=cn@CN.Name{CN.nameNameParts=l}},ty)}):tl) =
  let s= name2DkIdent n in
  let ss = computeUnused used (-1) s in
  d {unDom=(n {nameConcrete= cn {CN.nameNameParts=[CN.Id ss]}},ty)}:(separateAux (ss:used) tl)

usedVars :: Context -> [String]
usedVars = map (name2DkIdent . fst . unDom)

computeUnused used i s =
  let ss = if i==(-1) then s else s++(show i) in
  if elem ss used
  then computeUnused used (i+1) s
  else ss

freshStr ctx = computeUnused ("_":(usedVars ctx)) (-1)

addEl :: Term -> Elim -> Term
addEl (Var i elims) e = Var i (elims++[e])
addEl (Def n elims) e = Def n (elims++[e])
addEl (Con h i elims) e = Con h i (elims++[e])
addEl _ _ = error "Those terms do not expect elimination"
