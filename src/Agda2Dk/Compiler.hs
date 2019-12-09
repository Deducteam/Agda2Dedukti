
module Agda2Dk.Compiler where

import Control.Monad.State
import Data.Maybe
import System.Directory (doesFileExist)
import Data.Int
import Data.List (sortOn, stripPrefix, intercalate, (++))
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
import Agda.Syntax.Position
import Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.ReconstructParameters
import Agda.TypeChecking.RecordPatterns
import Agda.TypeChecking.Records
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Primitive.Base
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Substitute.Class
import Agda.TypeChecking.Telescope
import qualified Agda.TypeChecking.Pretty as AP
import Agda.Utils.Monad
import Agda.Utils.Pretty (pretty)
import Agda.Utils.Impossible

import Agda2Dk.DkSyntax

------------------------------------------------------------------------------
-- Backend callbacks
------------------------------------------------------------------------------

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

------------------------------------------------------------------------------
--- Options ---
------------------------------------------------------------------------------

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

------------------------------------------------------------------------------
--- Module compilation ---
------------------------------------------------------------------------------

-- This is the name of the "etaExpand" function --
type DkModuleEnv = QName

dkPreModule :: DkOptions -> IsMain -> ModuleName -> FilePath -> TCM (Recompile DkModuleEnv ())
dkPreModule opts _ mods _ =
  let concMods = modName2DkModIdent mods in
  -- If a directory is not given by the user, we just use the current one.
  let dir = case optDkDir opts of Nothing -> ""
                                  Just s  -> s
  in
  let mod = intercalate "__" concMods in
  let filePath = dir++mod++".dk" in
  do
    name <- createEtaExpandSymbol ()
    liftIO $
      ifM (((not (optDkRegen opts)) &&) <$> (doesFileExist filePath))
      (return (Skip ()))
      (do putStrLn $ "Generation of "++filePath
          return (Recompile name))

dkPostModule :: DkOptions -> DkModuleEnv -> IsMain -> ModuleName -> [DkCompiled] -> TCM ()
dkPostModule opts _ _ mods defs =
  let concMods = modName2DkModIdent mods in
  let dir = case optDkDir opts of Nothing -> ""
                                  Just s  -> s
  in
  let mod = intercalate "__" concMods in
  let filePath = dir++mod++".dk" in
  do
    -- We sort the file, to make sure that declarations and rules do not refer to formerly declared symbols.
    output <- orderDeclRules (catMaybes defs) concMods
    liftIO $
      do
        ss <- return $ show output
        writeFile filePath ss

orderDeclRules :: [(Int32,DkDefinition)] -> DkModName -> TCM Doc
orderDeclRules l = orderDeclRules' 0 empty empty [] (sortOn fst l)

-- mut is an integer to detect if two declarations are mutual.
-- accTy contains the declaration of types (which comes before the ones of constructors).
-- accTy is the "real" accumulator, ie once a mutual block is processed, the result is stored here.
-- accOther contains constructors declarations.
-- waitingRules contains rules.
-- In this function, we can rely on the mutuality, because a type constructor is considered mutual with its constructors.
orderDeclRules' :: Int32 -> Doc -> Doc -> [Doc] -> [(Int32,DkDefinition)] -> DkModName -> TCM Doc
orderDeclRules' mut accTy accOther waitingRules []         mods =
  return $ accTy <> accOther <> (hcat waitingRules)
orderDeclRules' mut accTy accOther waitingRules l@((m,d):tl) mods
  | m==mut =
      case staticity d of
        TypeConstr ->
          orderDeclRules' mut
            (accTy<>(printDecl mods d))
            accOther
            (waitingRules++(printRules mods d))
            tl mods
        _ ->
          orderDeclRules' mut
            accTy
            (accOther<>(printDecl mods d))
            (waitingRules++(printRules mods d))
            tl mods
  | otherwise =
      orderDeclRules' m (accTy<>accOther<>(hcat waitingRules)) empty [] l mods

------------------------------------------------------------------------------
-- The main function --
------------------------------------------------------------------------------

dkCompileDef :: DkOptions -> DkModuleEnv -> IsMain -> Definition -> TCM DkCompiled
dkCompileDef _ eta _ def@(Defn {defCopy=isCopy, defName=n, theDef=d, defType=t, defMutual=MutId m}) =
  if isCopy
  then return Nothing
  else
    do
      reportSDoc "toDk" 3 $ (text "Compiling definition of" <+>) <$> AP.prettyTCM n
      reportSDoc "toDk" 60 $ return $ text $ show def
      (nbPars,tExpand) <-
        case d of
          Constructor {conData=dat} -> do
            -- If dat is a Datatype, isRecord dat is Nothing
            recOrData <- isRecord dat
            case recOrData of
              Nothing -> defaultCase
              Just {} -> do
                Defn{theDef=Record{recPars=i}} <- getConstInfo dat
                -- In case of record constructor, because of the eta-rule,
                -- the return type must not be eta-expanded.
                (\x -> (i,x)) <$> etaExpOnlyInDomain eta t i i
          Function {funProjection=pr} ->
            case pr of
              Nothing -> defaultCase
              Just Projection{projProper=Nothing} -> defaultCase
                -- In case of record projector, symetrically, because of the eta-rule,
                -- the argument type must not be eta-expanded.
              Just Projection{projProper=Just recN} -> do
                Defn{theDef=Record{recPars=i}} <- getConstInfo recN
                (\x -> (i,x)) <$> etaExpOnlyInCodom eta t (i+1) i
          _ -> defaultCase
      reportSDoc "toDk.eta" 5 $ (text "tExpand is" <+>) <$> AP.pretty tExpand
      inTopContext $ do
        tParam  <- reconstructParametersInType' (etaExpandButInParamAction eta nbPars) tExpand
        typ     <- translateType eta tParam
        name    <- qName2DkName eta n
        kk      <- getKind eta t
        stat    <- extractStaticity n d
        rules   <- extractRules eta n d t
        return $ Just (m,DkDefinition
          { name      = name
          , staticity = stat
          , typ       = typ
          , kind      = kk
          , rules     = rules})

  where
    defaultCase = (\x -> (0,x)) <$> checkInternalType' (etaExpandAction eta) t

translateType :: DkModuleEnv -> Type -> TCM DkTerm
translateType eta (El {unEl=ty}) = translateTerm eta ty

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

extractRules :: DkModuleEnv -> QName -> Defn -> Type -> TCM [DkRule]
extractRules eta n (Function {funCovering=f}) ty =
  do
    l <- mapM (clause2rule eta n) f
    return $ catMaybes l
extractRules eta n (Datatype {dataCons=cons, dataClause=Just c, dataPars=i, dataIxs=j}) ty=
  do
    l <- sequence [clause2rule eta n c, Just <$> decodedVersion eta n (i+j)]
    (catMaybes l ++) <$> (etaIsId eta n i j cons)
extractRules eta n (Datatype {dataCons=cons, dataClause=Nothing, dataPars=i, dataIxs=j}) ty =
  do
    l <- sequence [Just <$> decodedVersion eta n (i+j)]
    (catMaybes l ++) <$> (etaIsId eta n i j cons)
extractRules eta n (Record {recClause=Just c, recPars=i, recConHead=hd, recFields=f}) ty =
  do
    l <- sequence [clause2rule eta n c, Just <$> decodedVersion eta n i, Just <$> etaExpansionDecl eta n i hd f]
    return $ catMaybes l
extractRules eta n (Record {recClause=Nothing, recPars=i, recConHead=hd, recFields=f}) ty =
  do
    l <- sequence [Just <$> decodedVersion eta n i, Just <$> etaExpansionDecl eta n i hd f]
    return $ catMaybes l
extractRules eta n (Primitive {primClauses=p}) ty =
  do
    recordCleaned <- mapM translateRecordPatterns p
    l <- mapM (clause2rule eta n) recordCleaned
    return $ catMaybes l
extractRules _ _ _ _                            = sequence []

decodedVersion :: DkModuleEnv -> QName -> Int -> TCM DkRule
decodedVersion eta nam i = do
  nn@(DkQualified mods pseudo n) <- qName2DkName eta nam
  let decodedName = DkQualified mods ("TYPE":pseudo) n
  let hd = DkQualified ["naiveAgda"] [] "Term"
  return $ DkRule
    { context   = genCtx i
    , headsymb  = hd
    , patts     = [DkJoker,DkFun nn (genVars i)]
    , rhs       = constructRhs (DkConst decodedName)
    }
  where
    genCtx = genCtxAux []
    genCtxAux acc 0 = acc
    genCtxAux acc j = genCtxAux (ind2DkIdent j:acc) (j-1)
    genVars = genVarsAux []
    genVarsAux acc 0 = acc
    genVarsAux acc j = genVarsAux ((DkVar (ind2DkIdent j) (j-1) []):acc) (j-1)
    constructRhs = constructRhsAux 0
    constructRhsAux j t =
      if i==j
      then t
      else constructRhsAux (j+1) (DkApp t (DkDB (ind2DkIdent (j+1)) j))
    ind2DkIdent j = "x"++ show j

clause2rule :: DkModuleEnv -> QName -> Clause -> TCM (Maybe DkRule)
clause2rule eta nam cc = do
  reportSDoc "agda2Dedukti" 5  $ ((text "We are treating:") <+>) <$> (AP.prettyTCM nam)
  reportSDoc "agda2Dedukti" 10 $ return $ (text "The clause is") <+> (pretty cc)
  reportSDoc "agda2Dedukti" 20 $ ((text "In the context:") <+> ) <$> (AP.prettyTCM (clauseTel cc))
  reportSDoc "agda2Dedukti" 20 $ return $ (text "The type is:") <+> (pretty (clauseType cc))
  reportSDoc "agda2Dedukti" 20 $ return $ (text "The body is:") <+> (pretty (clauseBody cc))
  reportSDoc "agda2Dedukti" 50 $ return $ text $ "More precisely:" ++ show (clauseBody cc)
  isProj <- isProjection nam
  c <-
    -- case isProj of
    --   Nothing ->
    --     translateRecordPatterns' AllRecordPatterns cc
    --   Just Projection{projProper=Nothing} ->
    --     translateRecordPatterns' AllRecordPatterns cc
    --   Just{} -> do
    --      reportSDoc "agda2Dedukti" 30 $ (<+> text " is considered as a projection") <$> (AP.prettyTCM nam)
         return cc
  reportSDoc "agda2Dedukti" 30 $ ((text "The new clause is") <+>) <$> (AP.prettyTCM c)
  reportSDoc "agda2Dedukti" 30 $ ((text "In the context:") <+> ) <$> (AP.prettyTCM (clauseTel c))
  reportSDoc "agda2Dedukti" 30 $ return $ (text "The new body is:") <+> (pretty (clauseBody c))
  reportSDoc "agda2Dedukti" 50 $ return $ text $ "More precisely:" ++ show (clauseBody c)
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
              r1 <- checkInternal' (etaExpandButInParamAction eta implicits) r (unArg t)
              reportSDoc "agda2Dedukti" 20 $ return $ (text "Eta expansion done")
              reconstructParameters' (etaExpandAction eta) (unArg t) r1
        reportSDoc "agda2Dedukti" 30 $ return $ text "Parameters reconstructed"
        reportSDoc "agda2Dedukti" 40 $ return $ (text "The final body is") <+> (pretty rr)
        (patts,_) <- extractPatterns eta (namedClausePats c)
        let impArgs = implicitArgs implicits (reverse ctx)
        rhs <- translateTerm eta rr
        headSymb <- qName2DkName eta nam
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

extractContext :: Context -> TCM DkCtx
extractContext = extractContextAux []

extractContextAux :: DkCtx -> Context -> TCM DkCtx
extractContextAux acc []                                    =
  return $ reverse acc
extractContextAux acc (Dom {unDom=(n,t)}:r) =
  extractContextAux (name2DkIdent n:acc) r

extractPatterns :: DkModuleEnv -> [NamedArg DeBruijnPattern] -> TCM ([DkPattern],LastUsed)
extractPatterns = auxPatt (-1) []

auxPatt ::  LastUsed -> [DkPattern] -> DkModuleEnv -> [NamedArg DeBruijnPattern] -> TCM ([DkPattern],LastUsed)
auxPatt n acc eta [] =
  return (reverse acc,n)
auxPatt n acc eta (p:patts) =
  do (t, nn) <- extractPattern eta n p
     auxPatt (max n nn) (t:acc) eta patts

extractPattern :: DkModuleEnv -> LastUsed -> NamedArg DeBruijnPattern -> TCM (DkPattern,LastUsed)
extractPattern eta n x =
  let pat = namedThing (unArg x) in
  case pat of
    VarP _ (DBPatVar {dbPatVarIndex=i}) ->
      do
        nam <- nameOfBV i
        return (DkVar (name2DkIdent nam) i [], max i n)
    DotP _ t                           ->
      do term <- translateTerm eta t
         return (DkBrackets term, n)
    ConP (ConHead {conName=h}) ci tl     ->
      do
        (patts, nn) <- auxPatt n [] eta tl
        mbNbParams <- getNumberOfParameters h
        nbParams <-
          case mbNbParams of
            Nothing -> error "Why no Parameters?"
            Just n  -> return n
        nam <- qName2DkName eta h
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
        dkNam <- qName2DkName eta nam
        let args = (replicate nbParams DkJoker)
        return (DkFun dkNam args, n)
    otherwise                           ->
      error "Unexpected pattern of HoTT"

translateElim :: DkModuleEnv -> DkTerm -> Term -> Elims -> TCM DkTerm
translateElim eta t tAg []                  = return t
translateElim eta t tAg (el@(Apply e):tl)      =
  do arg <- translateTerm eta (unArg e)
     translateElim eta (DkApp t arg) (addEl tAg el) tl
translateElim eta t tAg (el@(Proj _ qn):tl)    = do
  reportSDoc "agda2Dedukti" 2 $ AP.prettyTCM (applyE tAg [el])
  error "Unspining not performed!"
  -- let proj = DkConst $ qName2DkName qn in
  -- do
  --   reportSDoc "agda2Dedukti" 15 $ (AP.prettyTCM tAg) >>= (\x -> return $ (text "The term:") <+> x)
  --   reportSDoc "agda2Dedukti" 15 $ (AP.prettyTCM el) >>= (\x -> return $ (text "Is eliminated with:") <+> x)
  --   def <- getConstInfo qn
  --   let tyProj = defType def
  --   reportSDoc "agda2Dedukti" 15 $ (AP.prettyTCM tyProj) >>= (\x -> return $ (text "Of type:") <+> x)
  --   let nbPar = countHiddenArgs tyProj
  --   reportSDoc "agda2Dedukti" 16 $ return $ text $ "Hence has "++show nbPar++" parameters"
  --   res <-
  --     do
  --       ty <- infer tAg
  --       reportSDoc "agda2Dedukti" 2 $ (AP.prettyTCM ty) >>= (\x -> return $ (text "Inferred type:") <+> x)
  --       dkTy <-
  --         case unEl ty of
  --           Dummy _ _ -> appNbDummyHd nbPar
  --           _         -> translateType ty
  --       reportSDoc "agda2Dedukti" 2 $ return $ (text "Translated as:") <+> (prettyDk [] dkTy)
  --       return $ replaceHd proj dkTy
  --   translateElim (DkApp res t) (addEl tAg el) tl
translateElim eta t tAg ((IApply _ _ _):tl) = error "Unexpected IApply"


translateTerm :: DkModuleEnv -> Term -> TCM DkTerm
translateTerm eta (Var i elims) =
  do
    nam <- nameOfBV i
    translateElim eta (DkDB (name2DkIdent nam) i) (Var i []) elims
translateTerm eta (Lam _ ab) =
  do
    ctx <- getContext
    let n = freshStr ctx (absName ab)
    addContext n $
      do
        body <- translateTerm eta (unAbs ab)
        nam <- nameOfBV 0
        return $ DkLam (name2DkIdent nam) Nothing body
translateTerm eta (Lit l)            =
  return $ translateLiteral l
translateTerm eta (Def n elims)                    = do
  nam <- qName2DkName eta n
  translateElim eta (DkConst nam) (Def n []) elims
translateTerm eta (Con hh@(ConHead {conName=h}) i elims)        = do
  nam <- qName2DkName eta h
  translateElim eta (DkConst nam) (Con hh i []) elims
translateTerm eta (Pi d@(Dom {unDom=t}) (Abs{absName=n, unAbs=u})) =
  case t of
    El {unEl=Def h []} -> do
      dom <- qName2DkName eta h
      if dom == DkQualified ["Agda","Primitive"] [] "Level"
      then
        do
          ctx <- getContext
          let nn = freshStr ctx n
          addContext (nn,d) $
            do
              body <-translateType eta u
              ku <- getKind eta u
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
          dom <- translateType eta t
          body <- addContext (nn,d) $ translateType eta u
          kt <- getKind eta t
          ku <- addContext (nn,d) $ getKind eta u
          nam <- addContext (nn,d) $ nameOfBV 0
          return $ DkProd kt ku (name2DkIdent nam) dom body
translateTerm eta (Pi d@(Dom {unDom=t}) (NoAbs{absName=n, unAbs=u})) =
  do
    ctx <- getContext
    let nn = freshStr ctx n
    dom <- translateType eta t
    body <- translateType eta u
    kt <- getKind eta t
    ku <- getKind eta u
    nam <- addContext (nn,d) $ nameOfBV 0
    return $ DkProd kt ku (name2DkIdent nam) dom body
translateTerm eta (Sort s)                      =
  do ss <- extractSort eta s
     return $ DkSort ss
translateTerm eta (Level lev)                   =
  do lv <- lvlFromLevel eta lev
     return $ DkLevel lv
translateTerm eta (MetaV {})                    = error "Not implemented yet : MetaV"
translateTerm eta (DontCare t)                  = translateTerm eta t
translateTerm eta (Dummy _ _)                   = error "Not implemented yet : Dummy"

-- extractAsPattern :: DkModuleEnv -> Term -> TCM DkPattern
-- extractAsPattern eta (Var i elims) =
--   do
--     nam <- nameOfBV i
--     DkVar (name2DkIdent nam) i <$> elimAsPattern eta elims
-- extractAsPattern eta (Lam _ ab) =
--   do
--     ctx <- getContext
--     let n = freshStr ctx (absName ab)
--     addContext n $
--       do
--         body <- extractAsPattern eta (unAbs ab)
--         nam <- nameOfBV 0
--         return $ DkLambda (name2DkIdent nam) body
-- extractAsPattern eta (Lit l)            =
--   error "Litteral cannot be seen as pattern yet"
-- extractAsPattern eta (Def n elims)                    = do
--   nam <- qName2DkName eta n
--   DkFun nam <$> elimAsPattern eta elims
-- extractAsPattern eta (Con hh@(ConHead {conName=h}) i elims)        = do
--   nam <- qName2DkName eta h
--   DkFun nam <$> elimAsPattern eta elims

extractSort :: DkModuleEnv -> Sort -> TCM DkSort
extractSort eta (Type i)                  =
  do lv <- lvlFromLevel eta i
     return $ DkSet lv
extractSort eta (Prop i)                  =
  do lv <- lvlFromLevel eta i
     return $ DkProp lv
extractSort eta Inf                       = return DkSetOmega
extractSort eta SizeUniv                  = return $ DkSet [LvlInt 0]
extractSort eta (PiSort (Dom{unDom=s}) t) =
  do dom <- extractSort eta (_getSort s)
     codom <- extractSort eta (unAbs t)
     return $ DkPi dom codom
extractSort eta (UnivSort s)              =
  do ss <- extractSort eta s
     return $ DkUniv ss
extractSort _   _                         = return DkDefaultSort

lvlOf :: DkModuleEnv -> Sort -> TCM Lvl
lvlOf eta (Type i)                  = lvlFromLevel eta i
lvlOf eta (Prop i)                  = lvlFromLevel eta i

getKind :: DkModuleEnv -> Type -> TCM DkSort
getKind eta (El {_getSort=s}) = extractSort eta s

lvlFromLevel :: DkModuleEnv -> Level -> TCM Lvl
lvlFromLevel eta (Max l) = mapM (preLvlFromPlusLevel eta) l

preLvlFromPlusLevel :: DkModuleEnv -> PlusLevel -> TCM PreLvl
preLvlFromPlusLevel eta (ClosedLevel i)           =
  return $ LvlInt (fromInteger i)
preLvlFromPlusLevel eta (Plus i (BlockedLevel _ t)) =
  do tt <- translateTerm eta t
     return $ LvlPlus (fromInteger i) tt
preLvlFromPlusLevel eta (Plus i (NeutralLevel _ t)) =
  do tt <- translateTerm eta t
     return $ LvlPlus (fromInteger i) tt
preLvlFromPlusLevel eta (Plus i (UnreducedLevel t)) =
  do tt <- translateTerm eta t
     return $ LvlPlus (fromInteger i) tt

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


addEl :: Term -> Elim -> Term
addEl (Var i elims) e = Var i (elims++[e])
addEl (Def n elims) e = Def n (elims++[e])
addEl (Con h i elims) e = Con h i (elims++[e])
addEl _ _ = error "Those terms do not expect elimination"


--------------------------------------------------------------------------------
-- Translation of Name and QName function
--------------------------------------------------------------------------------

qName2DkName :: DkModuleEnv -> QName -> TCM DkName
qName2DkName eta qn@QName{qnameModule=mods, qnameName=nam}
  | qn == eta = return $ DkQualified ["naiveAgda"] [] "etaExpand"
  | otherwise = do
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

type LastUsed = Nat

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

------------------------------------------------------------------------------
-- All on the Eta expansion
------------------------------------------------------------------------------

createEtaExpandSymbol :: () -> TCM QName
createEtaExpandSymbol () =
  do
  -- The type of etaExpand (which is an identity in the Agda side.
    typeId <- hPi "a" (el primLevel) $
              nPi "A" (return . sort $ varSort 0) $
              (return $ El (varSort 1) (var 0)) -->
              (return $ El (varSort 1) (var 0))
  -- A new symbol etaExpand in the module etaExpand.
    name <- qnameFromList <$> sequence [freshName_ "etaExpand", freshName_ "etaExpand"]
    tele <- theTel <$> telView typeId
    let args = [
          defaultArg (namedDBVarP 2 "a"),
          defaultArg (namedDBVarP 1 "A"),
          defaultArg (namedDBVarP 0 "x")
          ]
    addConstant name $ defaultDefn defaultArgInfo name typeId emptyFunction{funClauses=[defaultClause{clauseTel=tele, namedClausePats=args, clauseBody=Just $ var 0, clauseType = Just $ defaultArg $ El (varSort 2) (var 1)}]}
    return name
  where
    defaultClause =
      Clause
      { clauseLHSRange    = NoRange
      , clauseFullRange   = NoRange
      , clauseTel         = EmptyTel
      , namedClausePats   = []
      , clauseBody        = Nothing
      , clauseType        = Nothing
      , clauseCatchall    = False
      , clauseUnreachable = Nothing
    }

etaExpandType :: DkModuleEnv -> Type -> TCM Type
etaExpandType eta (El s (Pi a@Dom{unDom=El sa u} b)) = do
  uu <- checkInternal' (etaExpandAction eta) u (sort sa)
  let dom = El sa uu
  addContext a $ do
    codom <- etaExpandType eta (absBody b)
    return $ El s (Pi a{unDom=dom} (Abs (absName b) codom))
etaExpandType eta (El s u) = do
  uu <- checkInternal' (etaExpandAction eta) u (sort s)
  return $ El s uu

etaExpOnlyInDomain :: DkModuleEnv -> Type -> Nat -> Nat -> TCM Type
etaExpOnlyInDomain eta (El s (Pi a@Dom{unDom=El sa u} b)) 0 k = do
  uu <- checkInternal' (etaExpandButInParamAction eta k) u (sort sa)
  let dom = El sa uu
  addContext a $ do
    codom <- etaExpOnlyInDomain eta (absBody b) 0 k
    return $ El s (Pi a{unDom=dom} (Abs (absName b) codom))
etaExpOnlyInDomain eta (El s (Pi a b)) j k = do
  addContext a $ do
    codom <- etaExpOnlyInDomain eta (absBody b) (j-1) k
    return $ El s (Pi a (Abs (absName b) codom))
etaExpOnlyInDomain _ u _ _ = return u

etaExpOnlyInCodom :: DkModuleEnv -> Type -> Nat -> Nat -> TCM Type
etaExpOnlyInCodom eta (El s u) 0 k = do
  reportSDoc "toDk.eta" 10 $ (text "Type to exp is" <+>) <$> AP.pretty u
  reportSDoc "toDk.eta" 10 $ return. text $ "And the ints are 0 and "++show k
  uu <- checkInternal' (etaExpandButInParamAction eta k) u (sort s)
  return $ El s uu
etaExpOnlyInCodom eta (El s (Pi a b)) j k = do
  reportSDoc "toDk.eta" 10 $ (text "Type is" <+>) <$> AP.pretty (Pi a b)
  reportSDoc "toDk.eta" 10 $ return. text $ "And the ints are "++show j++" and "++show k
  addContext a $ do
    codom <- etaExpOnlyInCodom eta (absBody b) (j-1) k
    return $ El s (Pi a (Abs (absName b) codom))

etaIsId :: DkModuleEnv -> QName -> Nat -> Nat -> [QName] -> TCM [DkRule]
etaIsId eta n i j cons = do
  reportSDoc "toDk.Eta" 3 $ (text "Eta is id of" <+>) <$> AP.prettyTCM n
  mapM oneCase cons

  where
    hd = DkQualified ["naiveAgda"] [] "etaExpand"
    oneCase f = do
      Defn{defType=tt} <- getConstInfo f
      TelV tele _ <- telView tt
      addContext tele $
        modifyContext separateVars $ do
        cc <- qName2DkName eta f
        nn <- qName2DkName eta n
        ctx <- getContext
        context <- extractContext ctx
        consArg <- pattCons cc ctx
        rhs <- constructRhsFields 0 (DkConst cc) ctx
        return $ DkRule
          { context   = context
          , headsymb  = hd
          , patts     = [DkJoker, DkFun nn (replicate (i+j) DkJoker), consArg]
          , rhs       = rhs
          }

    pattCons cc args =
      DkFun cc <$> nextIndex [] 0 args
    nextIndex acc j []     = return acc
    nextIndex acc j (_:tl) = do
      (vj,_) <- extractPattern eta 0 $ defaultArg $ unnamed $ varP (DBPatVar "_" j)
      nextIndex (vj:acc) (j+1) tl

    constructRhsFields _ t [] = return t
    constructRhsFields j t (Dom{unDom=(_,tt)}:tl) = do
      let ttGoodDB = raise (j+1) tt
      vEta <-
        -- if length tl <i
        -- then
        --   return $ Var j []
        -- else
          checkInternal' (etaExpandAction eta) (Var j []) ttGoodDB
      vParam <- reconstructParameters' (etaExpandAction eta) ttGoodDB vEta
      dkArg <- translateTerm eta vParam
      (`DkApp` dkArg) <$> constructRhsFields (j+1) t tl

etaExpansionDecl :: QName -> QName -> Int -> ConHead -> [Arg QName] -> TCM DkRule
etaExpansionDecl eta n nbPars ConHead{conName = cons} l = do
  reportSDoc "toDk.eta" 10 $ (text "[Decl]Eta expansion of" <+>) <$> AP.prettyTCM n
  let hd = DkQualified ["naiveAgda"] [] "etaExpand"
  Defn{defType=tt} <- getConstInfo n
  TelV tele _ <- telView tt
  addContext tele $
    modifyContext separateVars $ do
    nn <- qName2DkName eta n
    cc <- qName2DkName eta cons
    y <- (\ctx -> freshStr ctx "y") <$> getContext
    let ty = apply (Def n []) (teleArgs tele)
    s <- checkType' $ El Inf ty
    addContext (y,defaultDom $ El s ty) $ do
      ctx <- getContext
      context <- extractContext ctx
      tyArg <- pattTy nn ctx
      rhs <- constructRhs (DkConst cc) ctx y
      return $ DkRule
        { context   = context
        , headsymb  = hd
        , patts     = [DkJoker, tyArg, DkVar y 0 []]
        , rhs       = rhs
        }

  where
    pattTy cc args =
      DkFun cc <$> nextIndex [] 0 args
    nextIndex acc 0 (_:tl) = nextIndex acc 1 tl
    nextIndex acc j []     = return acc
    nextIndex acc j (_:tl) = do
      (vj,_) <- extractPattern eta 0 $ defaultArg $ unnamed $ varP (DBPatVar "_" j)
      nextIndex (vj:acc) (j+1) tl

    constructRhs t args y = do
      tParam <- constructRhsParams 0 t args
      constructRhsFields tParam args (map unArg l)
    constructRhsParams 0 t (_:tl) = constructRhsParams 1 t tl
    constructRhsParams _ t [] = return t
    constructRhsParams j t (_:tl) = do
      dkArg <- translateTerm eta (Var j [])
      (`DkApp` dkArg) <$> constructRhsParams (j+1) t tl

    rightType 0 u = u
    rightType j (El _ (Pi _ b)) = rightType (j-1) (absBody b)

    constructRhsFields t args [] = return t
    constructRhsFields t args (u:tl) = do
      reportSDoc "toDk.eta" 15 $ (text "Projector" <+>) <$> AP.prettyTCM u
      Defn{defType=tyProj} <- getConstInfo u
      reportSDoc "toDk.eta" 15 $ (text "tyProj" <+>) <$> AP.prettyTCM tyProj
      let tyRes = rightType (nbPars+1) tyProj
      reportSDoc "toDk.eta" 15 $ (text "tyRes" <+>) <$> AP.prettyTCM tyRes
      prEta <- etaExpansion eta nbPars tyRes (Var 0 [Proj ProjSystem u])
      reportSDoc "toDk.eta" 15 $ return $ text "Eta expansion done"
      reportSDoc "toDk.eta" 15 $ return $ pretty prEta
      prDkName <- qName2DkName eta u
      prDk <- studyEtaExpansion prEta args prDkName 0 tyRes (\x -> x)
      -- prDk <- translateTerm eta <$> reconstructParameters' (etaExpandAction eta) tyRes prEta
      constructRhsFields (DkApp t prDk) args tl

    studyEtaExpansion t args prName i tyRes clo = case t of
      Def nam ((Apply s):(Apply tyBis):_:[]) ->
        if nam == eta
        then do
          case unArg s of
            Level ss -> do
              tyBisRecons <- reconstructParameters' (etaExpandButInParamAction eta nbPars) (sort (Type ss)) (unArg tyBis)
              etaCtx <- translateTerm eta (Def nam [Apply s,Apply tyBis{unArg=tyBisRecons}])
              escapeContext i $ do
                v <- translateTerm eta (Var 0 [])
                DkApp etaCtx <$> clo <$> (`DkApp` v) <$> constructRhsParams 0 (DkConst prName) args
            otherwise -> __IMPOSSIBLE__
        else __IMPOSSIBLE__
      Var i _ -> do
        v <- translateTerm eta (Var i [])
        escapeContext i $
          clo <$> (`DkApp` v) <$> constructRhsParams 0 (DkConst prName) args
      Lam _ body -> do
        case unEl tyRes of
          Pi a b -> do
            reportSDoc "toDk.eta" 20 $ return $ text "We study a Lambda" <+> pretty (unAbs body)
            El s tDom <- reconstructParametersInType' (etaExpandButInParamAction eta nbPars) (unDom a)
            dkTDom <- translateTerm eta tDom
            dkL <- lvlOf eta s
            dkS <- extractSort eta s
            addContext (absName body,a) $
              modifyContext separateVars $ do
              x <- nameOfBV 0
              let clo2 rest = DkApp rest (DkApp (DkApp (DkApp (DkConst (DkQualified ["naiveAgda"] [] "etaExpand")) (DkLevel dkL)) dkTDom)  (DkDB (name2DkIdent x) 0))
              DkLam (name2DkIdent x) (Just (dkTDom,dkS)) <$> studyEtaExpansion (absBody body) args prName (i+1) (absBody b) (clo2 . clo)
          otherwise -> __IMPOSSIBLE__
      otherwise -> __IMPOSSIBLE__


etaExpandButInParamAction :: QName -> Int -> Action TCM
etaExpandButInParamAction eta i = defaultAction { preAction = etaContractFun , postAction = etaExpansion eta i}

etaExpandAction :: QName -> Action TCM
etaExpandAction = (`etaExpandButInParamAction` 0)

etaContractFun :: Type -> Term -> TCM Term
etaContractFun _ u = case u of
  Lam i (Abs x b) -> etaLam i x b
  otherwise -> return u

etaExpansion :: QName -> Int -> Type -> Term -> TCM Term
etaExpansion eta i t u = do
  reportSDoc "toDk.Eta" 3 <$> return $ text "Eta expansion of" <+> pretty u
  reportSDoc "toDk.eta" 3 <$> return $ text "   of type" <+> pretty t
  case u of
    Var j _ -> do
      n <- getContextSize
      if j >= n-i
        then return u
        else defaultCase t u
    otherwise -> defaultCase t u

  where

    defaultCase t u =
      case unEl t of
        Var _ _   -> etaExp t u
        Def n _   -> do
          nn <- qName2DkName eta n
          case nn of
            DkQualified ["Agda", "Primitive"] [] "Level" -> do
              return u
            otherwise -> do
              etaExp t u
        Pi (a@Dom{domInfo=info}) b -> do
          ctx <- getContext
          let n = freshStr ctx (absName b)
          addContext (n,a) $ do
            let s = raise 1 (getElimSort (unDom a))
            let theVar = Def eta [Apply s, Apply . defaultArg . (raise 1) . unEl . unDom $ a, Apply $ defaultArg (Var 0 [])]
            let appli = applyE (raise 1 u) [Apply (Arg info theVar)]
            body <- etaExpansion eta i (absBody b) appli
            return $ Lam info (Abs n body)
        Sort _ -> return u
        otherwise -> __IMPOSSIBLE__

    etaExp t u = do
      let s = getElimSort t
      let tExpand = checkInternalType' (etaExpandButInParamAction eta i) t
      ty <- defaultArg . unEl <$> tExpand
      let uu = defaultArg u
      return $ Def eta [Apply s, Apply ty, Apply uu]

    getElimSort t =
      case _getSort t of
        Type l -> Arg defaultArgInfo{argInfoHiding=Hidden} (Level l)
        otherwise -> __IMPOSSIBLE__
