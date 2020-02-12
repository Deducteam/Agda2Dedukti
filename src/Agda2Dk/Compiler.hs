{-# LANGUAGE BangPatterns #-}

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
import Agda.TypeChecking.Level
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
    [ Option [] ["dk"]     (NoArg compileDkFlag) "compile program using the Dk backend"
    , Option [] ["outDir"] (OptArg outp "DIR")   "output DIR"
    , Option [] ["regen"]  (NoArg forceRegenDk)  "regenerate the Dedukti file even if it already exists"
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
            (accTy<>(printDecl mods d)<>hcat (printRules mods d decoding))
            accOther
            (waitingRules++(printRules mods d (not . decoding)))
            tl mods
        _ ->
          orderDeclRules' mut
            accTy
            (accOther<>(printDecl mods d))
            (waitingRules++(printRules mods d (\x -> True)))
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
  else do
    reportSDoc "toDk" 3 $ (text "  Compiling definition of" <+>) <$> AP.prettyTCM n
    reportSDoc "toDk" 60 $ return $ text "    " <> pretty def
    (projPar,tParam) <-
      case d of
        Function {funProjection=pr} ->
          case pr of
            Nothing                               -> defaultCase
            Just Projection{projProper=Nothing}   -> defaultCase
            -- In case of record projector, symetrically, because of the eta-rule,
            -- the argument type must not be eta-expanded.
            Just Projection{projProper=Just recN} -> do
              dd@Defn{theDef=Record{recPars=i}} <- getConstInfo recN
              tExpand <- etaExpandType eta t
              tPar <- inTopContext $ do
                reconstructParametersInType' (etaExpandAction eta) tExpand
              return (Just i, tPar)
        _ -> defaultCase
    reportSDoc "toDk.eta" 35 $ (text "    tParam is" <+>) <$> AP.pretty tParam
    inTopContext $ do
      typ        <- translateType eta tParam projPar
      Right name <- qName2DkName eta n -- n is not a copy
      kind       <- getKind eta t
      stat       <- extractStaticity n d
      rules      <- extractRules eta n d t
      return $ Just (m,DkDefinition
        { name      = name
        , staticity = stat
        , typ       = typ
        , kind      = kind
        , rules     = rules})

  where
    defaultCase = do
      tExpand <- checkInternalType' (etaExpandAction eta) t
      tPar <- inTopContext $ do
        reconstructParametersInType' (etaExpandAction eta) tExpand
      return (Nothing, tPar)

translateType :: DkModuleEnv -> Type -> Maybe Nat -> TCM DkTerm
translateType eta (El {unEl=ty}) i = translateTerm' eta ty i

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
  reportSDoc "toDk" 5 $ return $ text "  Decoding" <+> pretty nam
  Right nn@(DkQualified mods pseudo n) <- qName2DkName eta nam -- nam is not a copy
  let decodedName = DkQualified mods ("TYPE":pseudo) n
  let hd = DkQualified ["Agda"] [] "Term"
  ty <- defType <$> getConstInfo nam
  tele <- theTel <$> (telView ty)
  reportSDoc "toDk" 15 $ ((text "    In the context:") <+> ) <$> (AP.prettyTCM tele)
  addContext tele $
    modifyContext separateVars $ do
    tel <- getContext
    ctx <- extractContext tel
    patVars <- sequence (genVars ctx)
    rhs <- constructRhs tel 0 return (DkConst decodedName)
    return $ DkRule
      { decoding  = True
      , context   = ctx
      , headsymb  = hd
      , patts     = [DkJoker,DkFun nn patVars]
      , rhs       = rhs
      }
  where
    genVars = genVarsAux [] 0
    genVarsAux acc i []     = acc
    genVarsAux acc i (a:tl) =
      genVarsAux (((\x -> DkVar x i []) <$> (name2DkIdent <$> (nameOfBV i))):acc) (i+1) tl
    constructRhs :: [Dom(Name,Type)] -> Nat -> (DkTerm -> TCM DkTerm) -> DkTerm -> TCM DkTerm
    constructRhs []                     _ clo t = clo t
    constructRhs (Dom{unDom=(a,ty)}:tl) i clo t = do
      va <- etaExpansion eta (raise (i+1) ty) (var i)
      vaPar <- reconstructParameters (raise (i+1) ty) va
      constructRhs tl (i+1) (\x -> clo =<< (DkApp x <$> translateTerm eta vaPar)) t

clause2rule :: DkModuleEnv -> QName -> Clause -> TCM (Maybe DkRule)
clause2rule eta nam c = do
  reportSDoc "toDk.clause" 5  $ ((text "  We are treating:") <+>) <$> (AP.prettyTCM nam)
  reportSDoc "toDk.clause" 10 $ return $ (text "  The clause is") <+> (pretty c)
  reportSDoc "toDk.clause" 20 $ ((text "  In the context:") <+> ) <$> (AP.prettyTCM (clauseTel c))
  reportSDoc "toDk.clause" 20 $ return $ (text "  The type is:") <+> (pretty (clauseType c))
  reportSDoc "toDk.clause" 20 $ return $ (text "  The body is:") <+> (pretty (clauseBody c))
  reportSDoc "toDk.clause" 50 $ return $ text $ "    More precisely:" ++ show (clauseBody c)
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
            Nothing -> do
              reportSDoc "toDk.clause" 25 $ return $ text "    Clause without type !"
              return r
            Just t  -> do
              r1 <- checkInternal' (etaExpandAction eta) r (unArg t)
              reconstructParameters' (etaExpandAction eta) (unArg t) r1
        reportSDoc "toDk.clause" 30 $ return $ text "    Parameters reconstructed"
        reportSDoc "toDk.clause" 40 $ return $ text "    The final body is" <+> pretty rr
        tyHd <- defType <$> getConstInfo nam
        rhs <- translateTerm eta rr
        let impArgs = implicitArgs implicits (reverse ctx)
        (patts,_) <- extractPatterns eta (namedClausePats c) (drop implicits tyHd) (reverse impArgs)
        Right headSymb <- qName2DkName eta nam -- nam is not a copy
        return $ Just DkRule
          { decoding  = False
          , context   = ctx
          , headsymb  = headSymb
          , patts     = patts
          , rhs       = rhs
          }

    where
      implicitArgs 0 locCtx = []
      implicitArgs n (h:tl) =
        (DkVar h (length tl) [], varP (DBPatVar h (length tl))):(implicitArgs (n-1) tl)

      drop 0 t = t
      drop i (El _ (Pi _ u)) = drop (i-1) (absBody u)

extractContext :: Context -> TCM DkCtx
extractContext = extractContextAux []

extractContextAux :: DkCtx -> Context -> TCM DkCtx
extractContextAux acc []                                    =
  return $ reverse acc
extractContextAux acc (Dom {unDom=(n,t)}:r) =
  extractContextAux (name2DkIdent n:acc) r

extractPatterns :: DkModuleEnv -> [NamedArg DeBruijnPattern] -> Type -> [(DkPattern, DeBruijnPattern)] -> TCM ([DkPattern],LastUsed)
extractPatterns eta patts ty acc = do
  normTy <- normalise ty
  auxPatt (-1) eta patts normTy acc

auxPatt ::  LastUsed -> DkModuleEnv -> [NamedArg DeBruijnPattern] -> Type -> [(DkPattern, DeBruijnPattern)] -> TCM ([DkPattern],LastUsed)
auxPatt n eta []         _                           acc =
  return (reverse (map fst acc),n)
auxPatt n eta (p:patts) (El _ (Pi (Dom{unDom=t}) u)) acc = do
  (t, nn) <- extractPattern eta acc n p t
  normTy <- normalise (absBody u)
  auxPatt (max n nn) eta patts normTy ((t,namedThing (unArg p)):acc)
auxPatt  n eta (p:patts) ty                          acc = do
  (t, nn) <- extractPattern eta acc n p __DUMMY_TYPE__
  auxPatt (max n nn) eta patts __DUMMY_TYPE__ ((t,namedThing (unArg p)):acc)

extractPattern :: DkModuleEnv -> [(DkPattern, DeBruijnPattern)] -> LastUsed -> NamedArg DeBruijnPattern -> Type -> TCM (DkPattern,LastUsed)
extractPattern eta ctx n x ty =
  let pat = namedThing (unArg x) in
  case pat of
    VarP _ (DBPatVar {dbPatVarIndex=i})  -> do
      nam <- nameOfBV i
      return (DkVar (name2DkIdent nam) i [], max i n)
    DotP _ t                             -> do
      term <- translateTerm eta t
      return (DkGuarded term, n)
    ConP (ConHead {conName=h}) ci tl     -> do
      tyLoc <- normalise =<< defType <$> getConstInfo h
      nbParams <- fromMaybe (error "Why no Parameters?") <$> getNumberOfParameters h
      reportSDoc "toDk.clause" 30 $ return $ text "    The type of this applied constructor is" <+> pretty ty
      reportSDoc "toDk.clause" 30 $ return $ text "      in context" <+> hsep (punctuate (char ',') (map ((printPattern Top []) . fst) ctx))
      reportSDoc "toDk.clause" 50 $ return $ text "    Type of the constructor is" <+>  pretty tyLoc
      reportSDoc "toDk.clause" 30 $ return $ text "    We investigate for" <+>int nbParams<+>text "params"
      (tyArgs,argsParam) <-
            case ty of
              El _ (Def _ l) ->
                 caseParamFun tyLoc (take nbParams l)
              otherwise      ->  return $ (__DUMMY_TYPE__,replicate nbParams DkJoker)
      (patts, nn) <- auxPatt n eta tl tyArgs []
      let args = argsParam ++ patts
      Right nam <- qName2DkName eta h
      return (DkFun nam args, max n nn)
    LitP l                              ->
      return (DkBuiltin (translateLiteral l),n)
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
        Right dkNam <- qName2DkName eta nam
        let args = (replicate nbParams DkJoker)
        return (DkFun dkNam args, n)
    otherwise                           ->
      error "Unexpected pattern of HoTT"
  where

    caseParamFun :: Type -> Elims -> TCM (Type,[DkPattern])
    caseParamFun tyCons els = caseParamFun' tyCons els []

    caseParamFun' tyCons [] acc = do
      return (tyCons, reverse acc)
    caseParamFun' tyCons ((Apply (Arg _ (Var i []))):tl) acc =
      case fst (ctx !! i) of
        DkVar h j [] -> do
          ctxGlob <- getContext
          let (_,ty) = unDom (ctxGlob !! j)
          tEta <- etaExpansion eta (raise (j+1) ty) (var j)
          tPar <- reconstructParameters' (etaExpandAction eta) (raise (j+1) ty) tEta
          tt <- translateTerm eta tPar
          caseParamFun' (piApply tyCons [defaultArg (patternToTerm (snd (ctx !! i)))]) tl (DkGuarded tt:acc)
        otherwise ->
          caseParamFun'  (piApply tyCons [defaultArg (patternToTerm (snd (ctx !! i)))]) tl (DkJoker:acc)
    caseParamFun' tyCons@(El _ (Pi (Dom {unDom=tyArg}) _)) ((Apply (Arg _ t)):tl) acc = do
      let tt = applySubst (parallelS (map (patternToTerm . snd) ctx)) t
      tyNorm <- normalise tyArg
      case unEl tyNorm of
        Pi _ _    -> do
          tEta <- checkInternal' (etaExpandAction eta) tt tyArg
          tPar <- reconstructParameters' (etaExpandAction eta) tyArg tEta
          tDk <- translateTerm eta tPar
          caseParamFun' (piApply tyCons [defaultArg tt]) tl (DkGuarded tDk:acc)
        otherwise ->
          caseParamFun' (piApply tyCons [defaultArg tt]) tl (DkJoker:acc)

substi :: [DkPattern] -> DkTerm -> DkTerm
substi l (DkSort s)               =
  DkSort (substiSort l s)
substi l (DkProd s1 s2 x a b)     =
  DkProd (substiSort l s1) (substiSort l s2) x (substi l a) (substi l b)
substi l (DkProjProd s1 s2 x a b) =
  DkProjProd (substiSort l s1) (substiSort l s2) x (substi l a) (substi l b)
substi l (DkQuantifLevel s x a)   =
  DkQuantifLevel (substiSort l s) x (substi l a)
substi _ t@(DkConst _)            = t
substi l (DkApp t u)              =
  DkApp (substi l t) (substi l u)
substi l (DkLam x _ t)            =
  DkLam x Nothing (substi l t)
substi l (DkDB _ i)               =
  termOfPattern (l !! i)
substi l (DkLevel lv)             =
  DkLevel (substiLvl l lv)

substiLvl l lv = map (substiPreLvl l) lv

substiPreLvl _ lv@(LvlInt _) = lv
substiPreLvl l (LvlPlus i t) = LvlPlus i (substi l t)

substiSort l (DkSet lv)    = DkSet (substiLvl l lv)
substiSort l (DkProp lv)   = DkProp (substiLvl l lv)
substiSort _ DkSetOmega    = DkSetOmega
substiSort l (DkUniv s)    = DkUniv (substiSort l s)
substiSort l (DkPi s1 s2)  = DkPi (substiSort l s1) (substiSort l s2)
substiSort _ DkDefaultSort = DkDefaultSort

translateElim :: DkModuleEnv -> DkTerm -> Elims -> TCM DkTerm
translateElim eta t []                  = return t
translateElim eta t (el@(Apply e):tl)      = do
  arg <- translateTerm eta (unArg e)
  translateElim eta (DkApp t arg) tl
translateElim eta t (el@(Proj _ qn):tl)    = do
  reportSDoc "toDk" 2 $ ((text "    Pb with:" <+> printTerm Top [] t <+>)<$> AP.prettyTCM el)
  error "Unspining not performed!"
translateElim eta t ((IApply _ _ _):tl) = error "Unexpected IApply"

translateTerm' :: DkModuleEnv -> Term -> Maybe Nat -> TCM DkTerm
translateTerm' eta (Var i elims) Nothing = do
  nam <- nameOfBV i
  translateElim eta (DkDB (name2DkIdent nam) i) elims
translateTerm' eta (Lam _ ab) Nothing = do
  ctx <- getContext
  let n = freshStr ctx (absName ab)
  addContext n $
    do
      body <- translateTerm eta (unAbs ab)
      nam <- nameOfBV 0
      return $ DkLam (name2DkIdent nam) Nothing body
translateTerm' eta (Lit l) Nothing =
  return $ translateLiteral l
translateTerm' eta (Def n elims) Nothing = do
  nn <- qName2DkName eta n
  case nn of
    Right nam -> translateElim eta (DkConst nam) elims
    Left tt -> translateTerm eta (tt `applyE` elims)
translateTerm' eta (Con hh@(ConHead {conName=h}) i elims) Nothing = do
  nn <- qName2DkName eta h
  case nn of
    Right nam -> translateElim eta (DkConst nam) elims
    Left tt -> translateTerm eta (tt `applyE` elims)
translateTerm' eta (Pi d@(Dom {unDom=a}) bb) mb_j = do
  ctx <- getContext
  let nn = freshStr ctx (absName bb)
  dom <- translateType eta a Nothing
  ka <- getKind eta a
  case bb of
    Abs n b ->
      addContext (nn,d) $ do
        body <- translateType eta b (pred mb_j)
        kb <- getKind eta b
        nam <- nameOfBV 0
        case a of
          El {unEl=Def h []} -> do
            hd <- qName2DkName eta h
            if hd == Right (DkQualified ["Agda","Primitive"] [] "Level")
            then return $ DkQuantifLevel kb (name2DkIdent nam) body
            else return $ (sp_prod mb_j) ka kb (name2DkIdent nam) dom body
          otherwise ->
            return $ (sp_prod mb_j) ka kb (name2DkIdent nam) dom body
    NoAbs n b -> do
      body <- translateType eta b (pred mb_j)
      kb <- getKind eta b
      nam <- addContext (nn,d) $ nameOfBV 0
      return $ (sp_prod mb_j) ka kb (name2DkIdent nam) dom body
  where
    pred Nothing  = Nothing
    pred (Just 0) = Nothing
    pred (Just j) = Just (j-1)
    sp_prod (Just 0) = DkProjProd
    sp_prod _        = DkProd
translateTerm' eta (Sort s) Nothing = do
  ss <- extractSort eta s
  return $ DkSort ss
translateTerm' eta (Level lev) Nothing = do
  lv <- lvlFromLevel eta lev
  return $ DkLevel lv
translateTerm' eta (MetaV {}) Nothing = error "Not implemented yet : MetaV"
translateTerm' eta (DontCare t) Nothing = translateTerm eta t
translateTerm' eta (Dummy _ _) Nothing = error "Not implemented yet : Dummy"

translateTerm eta t = translateTerm' eta t Nothing

extractSort :: DkModuleEnv -> Sort -> TCM DkSort
extractSort eta (Type i)                  =
  DkSet <$> lvlFromLevel eta i
extractSort eta (Prop i)                  =
  DkProp <$> lvlFromLevel eta i
extractSort eta Inf                       =
  return DkSetOmega
extractSort eta SizeUniv                  =
  return $ DkSet [LvlInt 0]
extractSort eta (PiSort (Dom{unDom=s}) t) = do
  dom <- extractSort eta (_getSort s)
  codom <- extractSort eta (unAbs t)
  return $ DkPi dom codom
extractSort eta (UnivSort s)              =
  DkUniv <$> extractSort eta s
extractSort _   _                         =
  return DkDefaultSort

lvlOf :: DkModuleEnv -> Sort -> TCM Lvl
lvlOf eta (Type i)                  = lvlFromLevel eta i
lvlOf eta (Prop i)                  = lvlFromLevel eta i

getKind :: DkModuleEnv -> Type -> TCM DkSort
getKind eta (El {_getSort=s}) = extractSort eta s

lvlFromLevel :: DkModuleEnv -> Level -> TCM Lvl
lvlFromLevel eta (Max l) = mapM (preLvlFromPlusLevel eta) l

preLvlFromPlusLevel :: DkModuleEnv -> PlusLevel -> TCM PreLvl
preLvlFromPlusLevel eta (ClosedLevel i)                =
  return $ LvlInt (fromInteger i)
preLvlFromPlusLevel eta (Plus i (BlockedLevel _ t))    =
  LvlPlus (fromInteger i) <$> translateTerm eta t
preLvlFromPlusLevel eta (Plus i (NeutralLevel a t))    =
  LvlPlus (fromInteger i) <$> translateTerm eta t
preLvlFromPlusLevel eta lv@(Plus i (UnreducedLevel t)) =
  preLvlFromPlusLevel eta =<< reduce lv

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

qName2DkName :: DkModuleEnv -> QName -> TCM (Either Term DkName)
qName2DkName eta qn@QName{qnameModule=mods, qnameName=nam}
  | qn == eta = return $ Right $ DkQualified ["Agda"] [] "etaExpand"
  | otherwise = do
      topMod <- topLevelModuleName mods
      def <- getConstInfo qn
      if defCopy def
      then do
        let ty = defType def
        -- this first step is just to eta-expand, in order to trigger reduction
        tChk <- checkInternal' (etaExpandAction eta) (Def qn []) ty
        tRed <- normalise tChk
        -- We have to do it again since normalise eliminated it
        tChk2 <- checkInternal' (etaExpandAction eta) tRed ty
        tRecons <- reconstructParameters' (etaExpandAction eta) ty tChk2
        return $ Left tRecons
      else
        let otherMods = stripPrefix (mnameToList topMod) (mnameToList mods) in
        return $ Right $
          DkQualified (modName2DkModIdent topMod) (maybe [] (map name2DkIdent) otherMods) (name2DkIdent nam)

  -- where
  --   addMissingLam = addMissingLam' []

  --   addMissingLam' iList l@(Lam ArgInfo{argInfoHiding=NotHidden} _) (El _ (Pi Dom{domInfo=infPi@ArgInfo{argInfoHiding=Hidden}} b)) =
  --     Lam infPi (Abs (absName b) (addMissingLam' (iList++[infPi]) (raise 1 l) (unAbs b)))
  --   addMissingLam' iList t _ = addApp iList t

  --   addApp iList l@(Lam infLam t) = Lam infLam (Abs (absName t) (addApp iList (absBody t)))
  --   addApp iList (Def qn es) = Def qn $ (mapi (\i -> \inf -> Apply (Arg inf (Var i []))) iList) ++ (raise (length iList) es)

  --   mapi :: (Nat -> a -> b) -> [a] -> [b]
  --   mapi = mapi' 0
  --   mapi' i f [] = []
  --   mapi' i f (x:tl) = (f i x):(mapi' (i+1) f tl)

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
  addContext (absName b,a) $ do
    codom <- etaExpandType eta (absBody b)
    escapeContext 1 $ return $ El s (Pi a{unDom=dom} (Abs (absName b) codom))
etaExpandType eta (El s u) = do
  uu <- checkInternal' (etaExpandAction eta) u (sort s)
  return $ El s uu

etaIsId :: DkModuleEnv -> QName -> Nat -> Nat -> [QName] -> TCM [DkRule]
etaIsId eta n i j cons = do
  reportSDoc "toDk.eta" 5 $ (text "  Eta is id of" <+>) <$> AP.prettyTCM n
  mapM oneCase cons

  where
    hd = DkQualified ["Agda"] [] "etaExpand"
    oneCase f = do
      Defn{defType=tt} <- getConstInfo f
      TelV tele _ <- telView tt
      addContext tele $
        modifyContext separateVars $ do
        -- We do have the information that n is not a copy,
        -- otherwise it would not have gone through compileDef
        Right cc <- qName2DkName eta f
        Right nn <- qName2DkName eta n
        ctx <- getContext
        context <- extractContext ctx
        consArg <- pattCons cc ctx
        rhs <- constructRhsFields 0 (DkConst cc) ctx
        return $ DkRule
          { decoding  = False
          , context   = context
          , headsymb  = hd
          , patts     = [DkJoker, DkFun nn (replicate (i+j) DkJoker), consArg]
          , rhs       = rhs
          }

    pattCons cc args =
      DkFun cc <$> nextIndex [] 0 args
    nextIndex acc j []     = return acc
    nextIndex acc j (_:tl) = do
      (vj,_) <- extractPattern eta [] 0 (defaultArg $ unnamed $ varP (DBPatVar "_" j)) __DUMMY_TYPE__
      nextIndex (vj:acc) (j+1) tl

    constructRhsFields _ t [] = return t
    constructRhsFields j t (Dom{unDom=(_,tt)}:tl) = do
      let ttGoodDB = raise (j+1) tt
      vEta <- checkInternal' (etaExpandAction eta) (Var j []) ttGoodDB
      vParam <- reconstructParameters' (etaExpandAction eta) ttGoodDB vEta
      dkArg <- translateTerm eta vParam
      (`DkApp` dkArg) <$> constructRhsFields (j+1) t tl

etaExpansionDecl :: QName -> QName -> Int -> ConHead -> [Arg QName] -> TCM DkRule
etaExpansionDecl eta n nbPars ConHead{conName = cons} l = do
  reportSDoc "toDk.eta" 5 $ (text "  Declaration of eta-expansion of" <+>) <$> AP.prettyTCM n
  let hd = DkQualified ["Agda"] [] "etaExpand"
  Defn{defType=tt} <- getConstInfo n
  TelV tele _ <- telView tt
  addContext tele $
    modifyContext separateVars $ do
    -- We do have the information that n is not a copy,
    -- otherwise it would not have gone through compileDef
    Right nn <- qName2DkName eta n
    Right cc <- qName2DkName eta cons
    y <- (\ctx -> freshStr ctx "y") <$> getContext
    let ty = apply (Def n []) (teleArgs tele)
    s <- checkType' $ El Inf ty
    addContext (y,defaultDom $ El s ty) $ do
      ctx <- getContext
      context <- extractContext ctx
      tyArg <- pattTy nn ctx
      rhs <- constructRhs (DkConst cc) ctx y
      return $ DkRule
        { decoding  = False
        , context   = context
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
      (vj,_) <- extractPattern eta [] 0 (defaultArg $ unnamed $ varP (DBPatVar "_" j)) __DUMMY_TYPE__
      nextIndex (vj:acc) (j+1) tl
    constructRhs :: DkTerm -> [Dom (Name, Type)] -> DkIdent -> TCM DkTerm
    constructRhs t args y = do
      tParam <- constructRhsParams t args
      constructRhsFields tParam args (map unArg l)

    constructRhsParams t (_:tl) = constructRhsParams' 1 t tl return
    constructRhsParams t []     = return t
    constructRhsParams' _ t []                     clo = clo t
    constructRhsParams' j t (Dom{unDom=(a,ty)}:tl) clo = do
      va <- etaExpansion eta (raise (j+1) ty) (var j)
      vaPar <- reconstructParameters (raise (j+1) ty) va
      constructRhsParams' (j+1) t tl (\x -> clo =<< (DkApp x <$> translateTerm eta vaPar))

    rightType 0 u = u
    rightType j (El _ (Pi _ b)) = rightType (j-1) (absBody b)

    constructRhsFields :: DkTerm -> [Dom (Name,Type)] -> [QName] -> TCM DkTerm
    constructRhsFields t args [] = return t
    constructRhsFields t args (u:tl) = do
      reportSDoc "toDk.eta" 25 $ (text "  Projector" <+>) <$> AP.prettyTCM u
      Defn{defType=tyProj} <- getConstInfo u
      reportSDoc "toDk.eta" 35 $ (text "  tyProj" <+>) <$> AP.prettyTCM tyProj
      let tyRes = rightType (nbPars+1) tyProj
      reportSDoc "toDk.eta" 35 $ (text "  tyRes" <+>) <$> AP.prettyTCM tyRes
      prEta <- checkInternal' (etaExpandAction eta) (Var 0 [Proj ProjSystem u]) tyRes
      reportSDoc "toDk.eta" 35 $ return $ text "  Eta expansion done"
      reportSDoc "toDk.eta" 35 $ return $ text "    " <> pretty prEta
      Right prDkName <- qName2DkName eta u
      prDk <- studyEtaExpansion prEta args prDkName 0 tyRes (\x -> x)
      constructRhsFields (DkApp t prDk) args tl

    studyEtaExpansion t args prName i tyRes clo = case t of
      Def nam ((Apply s):(Apply tyBis):_:[]) ->
        if nam == eta
        then do
          case unArg s of
            Level ss -> do
              tyRecons <- reconstructParameters' (etaExpandAction eta) (sort (Type ss)) (unArg tyBis)
              etaCtx <- translateTerm eta (Def nam [Apply s,Apply tyBis{unArg=tyRecons}])
              escapeContext i $ do
                v <- translateTerm eta (Var 0 [])
                DkApp etaCtx <$> clo <$> (`DkApp` v) <$> constructRhsParams (DkConst prName) args
            otherwise -> __IMPOSSIBLE__
        else __IMPOSSIBLE__
      Var i _ -> do
        v <- translateTerm eta (Var i [])
        escapeContext i $
          clo <$> (`DkApp` v) <$> constructRhsParams (DkConst prName) args
      Lam _ body -> do
        case unEl tyRes of
          Pi a b -> do
            reportSDoc "toDk.eta" 40 $ return $ text "    We study a Lambda" <+> pretty (unAbs body)
            El s tDom <- reconstructParametersInType' (etaExpandAction eta) (unDom a)
            dkTDom <- translateTerm eta tDom
            dkL <- lvlOf eta s
            dkS <- extractSort eta s
            addContext (absName body,a) $
              modifyContext separateVars $ do
              x <- nameOfBV 0
              let clo2 rest = DkApp rest (DkApp (DkApp (DkApp (DkConst (DkQualified ["Agda"] [] "etaExpand")) (DkLevel dkL)) dkTDom)  (DkDB (name2DkIdent x) 0))
              DkLam (name2DkIdent x) (Just (dkTDom,dkS)) <$> studyEtaExpansion (absBody body) args prName (i+1) (absBody b) (clo2 . clo)
          otherwise -> __IMPOSSIBLE__
      otherwise -> __IMPOSSIBLE__

etaExpandAction :: DkModuleEnv -> Action TCM
etaExpandAction eta = defaultAction { preAction = \y -> etaContractFun , postAction = etaExpansion eta}

etaContractFun :: Term -> TCM Term
etaContractFun u = case u of
  Lam i (Abs x b) -> etaLam i x b
  otherwise -> return u

etaExpansion :: DkModuleEnv -> Type -> Term -> TCM Term
etaExpansion eta t u@(Lam _ _)  = return u -- No need to eta-expand a lambda
etaExpansion eta t u = do
  reportSDoc "toDk.eta" 35 $ (text "    Eta expansion of" <+>) <$> AP.prettyTCM u
  reportSDoc "toDk.eta" 50 $ (text "      of type" <+>) <$> AP.prettyTCM t
  case unEl t of
    Var _ _   -> etaExp t u
    Def n _   -> do
      ifM (isLevel n) (return u) (etaExp t u)
    Pi (a@Dom{domInfo=info}) b -> do
      reportSDoc "toDk.eta" 40 $ (text "    In the product" <+>) <$> AP.prettyTCM t
      ctx <- getContext
      let n = freshStr ctx (absName b)
      aExp <- etaExpandType eta (unDom a)
      aIsLevel <-
        case aExp of
          El _ (Def n _) -> isLevel n
          otherwise      -> return False
      addContext (n,a) $ do
        let s = raise 1 (getElimSort (unDom a))
        let varLong = Def eta [Apply s, Apply . defaultArg . (raise 1) . unEl $ aExp, Apply $ defaultArg (Var 0 [])]
        let theVar = if aIsLevel then Var 0 [] else varLong
        let appli = applyE (raise 1 u) [Apply (Arg info theVar)]
        body <- etaExpansion eta (absBody b) appli
        return $ Lam info (Abs n body)
    Sort _ -> return u
    otherwise -> __IMPOSSIBLE__

  where

    etaExp t u = do
      let s = getElimSort t
      tPar <- etaExpandType eta t
      let ty = defaultArg (unEl tPar)
      let uu = defaultArg u
      return $ Def eta [Apply s, Apply ty, Apply uu]

    getElimSort t =
      case _getSort t of
        Type l -> Arg defaultArgInfo{argInfoHiding=Hidden} (Level l)
        otherwise -> __IMPOSSIBLE__

    isLevel :: QName -> TCM Bool
    isLevel qn@QName{qnameModule=mods, qnameName=nam} =
      return $ (map name2DkIdent (mnameToList mods)) == ["Agda", "Primitive"] && (name2DkIdent nam) == "Level"
