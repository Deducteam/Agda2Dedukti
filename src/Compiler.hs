{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}


module Compiler where

-- hides (<>), as there was a conflit with the (<>) defined here
import Prelude hiding ((<>))

import Control.Monad.State
import Control.Exception
import Data.Maybe
import System.Directory (doesFileExist)
import Data.Int
import Data.List (sortOn, stripPrefix, intercalate, (++))
import Text.PrettyPrint
import Debug.Trace
import Data.List.NonEmpty (fromList, toList, NonEmpty( (:|) ))
import Data.Text (unpack)
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

-- needed for detecting the requires on the output
import Text.Regex.TDFA ((=~), getAllTextMatches)
import Data.List.Unique (sortUniq)

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

import DkSyntax

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
      -- ^ Flag which enables the Dedukti Backend
  , preCompile            = \opts -> return opts
      -- ^ Called after type checking completes, but before compilation starts.  
  , postCompile           = \_ _ _ -> return ()
      -- ^ Called after module compilation has completed. The @IsMain@ argument
      --   is @NotMain@ if the @--no-main@ flag is present.  
  , preModule             = dkPreModule
      -- ^ Called before compilation of each module. Gets the path to the
      --   @.agdai@ file to allow up-to-date checking of previously written
      --   compilation results. Should return @Skip m@ if compilation is not
      --   required.  
  , postModule            = dkPostModule
      -- ^ Called after all definitions of a module have been compiled.  
  , compileDef            = dkCompileDef
      -- ^ Compile a single definition.  
  , scopeCheckingSuffices = False
      -- ^ True if the backend works if @--only-scope-checking@ is used.  
  , mayEraseType          = \_ -> return True
      -- ^ The treeless compiler may ask the Backend if elements
      --   of the given type maybe possibly erased.
      --   The answer should be 'False' if the compilation of the type
      --   is used by a third party, e.g. in a FFI binding.  
  }

------------------------------------------------------------------------------
--- Options ---
------------------------------------------------------------------------------

type DkCompiled = Maybe (Int32,DkDocs)


data DkOptions = DkOptions
  { optDkCompile :: Bool
  , optDkFlags   :: [String]
  , optDkDir     :: Maybe String
  , optDkRegen   :: Bool
  , optDkModeLp  :: Bool
  , optDkEtaMode :: Bool
  } deriving Generic

instance NFData DkOptions


defaultDkOptions :: DkOptions
defaultDkOptions = DkOptions
  { optDkCompile = False
  , optDkFlags   = []
  , optDkDir     = Nothing
  , optDkRegen   = False
  , optDkModeLp  = False
  , optDkEtaMode = False
  }


-- Each OptDescr describes an option of flag. Its constructor is Option
-- The arguments to Option are:
--    - list of short option characters
--    - list of long option strings (without "--")
--    - argument descriptor, of type Flag DkOptions (Flag x = x -> OptM x, where OptM is a monad transformation,
-- so it is basically a function to change the default options)
--    - explanation of option for user 
dkCommandLineFlags :: [OptDescr (Flag DkOptions)]
dkCommandLineFlags =
    [ Option [] ["dk"]      (NoArg compileDkFlag) "compile program using the Dk backend"
    , Option [] ["outDir"]  (OptArg outp "DIR")   "output DIR"
    , Option [] ["regen"]   (NoArg forceRegenDk)  "regenerate the Dedukti file even if it already exists"
    , Option [] ["lp"]      (NoArg setLpModeOn)   "change to lp mode"
    , Option [] ["etaMode"] (NoArg setEtaModeOn)  "enables eta expansion and annotations"    
    ]
  where
    compileDkFlag o = return $ o { optDkCompile = True}
    outp d o        = return $ o { optDkDir = d}
    forceRegenDk o  = return $ o { optDkRegen = True}
    setLpModeOn o   = return $ o { optDkModeLp = True}
    setEtaModeOn o  = return $ o { optDkEtaMode = True}
    
type EtaMode = Bool

------------------------------------------------------------------------------
--- Module compilation ---
------------------------------------------------------------------------------

-- This is the name of the module and the one of "etaExpand" function --
type DkModuleEnv = (ModuleName, QName)

dkPreModule :: DkOptions -> IsMain -> ModuleName -> Maybe FilePath -> TCM (Recompile DkModuleEnv ())
dkPreModule opts _ mods _ =
  let path = filePath opts mods in
  let doNotRecompileFile = not (optDkRegen opts) in
  let sizeTypesFile = (modName2DkModIdent mods == ["Agda", "Builtin", "Size"]) in
  do
    name <- createEtaExpandSymbol ()
    fileAlreadyCompiled <- liftIO $ doesFileExist path
    if (fileAlreadyCompiled && doNotRecompileFile) || sizeTypesFile
    then return $ Skip ()
    else do liftIO $ putStrLn $ "Generation of " ++ path
            return $ Recompile (mods, name)

dkPostModule :: DkOptions -> DkModuleEnv -> IsMain -> ModuleName -> [DkCompiled] -> TCM ()
dkPostModule opts _ _ mods defs =
  let concMods = modName2DkModIdent mods in
-- We sort the file, to make sure that declarations and rules
-- do not refer to formerly declared symbols.    
  let output = show $ orderDeclRules (catMaybes defs) concMods in
  let outLp = addRequires opts output in
  liftIO $ writeFile (filePath opts mods) (if (optDkModeLp opts) then outLp else output)


-- this functions goes through the text that is going to be printed in the .lp file
-- and seee which modules it uses and add a require for them. using regular
-- expressions, it matches names of the form '(NAME.', ' NAME.', '↪Name' and ',Name.'
-- which are then included with a require on the begining of the file. this might
-- not be the cleanest way of adding the requires, but it seems to work well
-- at least right now
addRequires :: DkOptions -> String -> String
addRequires opts s =
  let moduleRegex = "[ (↪,][a-zA-Z0-9_']*\\." in
  let removeFirstAndLastChars s = reverse $ tail $ reverse $ tail s in
  let allmods = map removeFirstAndLastChars $
                getAllTextMatches (s =~moduleRegex) :: [String] in
  let filteredmods = filter (\s -> not $ or [s == "Agda", s == "univ"]) allmods in
  let uniquemods = sortUniq filteredmods in
  let reqBase = if optDkEtaMode opts
                then "require open AgdaTheory.eta.Base;"
                else "require open AgdaTheory.noEta.Base;" in
  let reqList = ([reqBase, "require open AgdaTheory.Levels;", ""] ++) $
                map (\s -> "require tests." ++ s ++ " as " ++ s ++ ";") uniquemods in
  let requires = intercalate "\n" reqList in
  requires ++ "\n" ++  s


filePath :: DkOptions -> ModuleName -> String
filePath opts mods =
  let concMods = modName2DkModIdent mods in
  -- If a directory is not given by the user, we just use the current one.
  let dir = case optDkDir opts of Nothing -> ""
                                  Just s  -> s  in
  let mod = dropAll (intercalate "__" concMods) in
  let extension = case optDkModeLp opts of False -> ".dk"
                                           True  -> ".lp" in
  dir ++ mod ++ extension

orderDeclRules :: [(Int32,DkDocs)] -> DkModName -> Doc
orderDeclRules l mods = orderDeclRules' 0 mods empty empty empty (sortOn fst l)

-- mut is an integer to detect if two declarations are mutual.
-- accTy contains the declaration of types (which comes before the ones of constructors).
-- accTy is the "real" accumulator, ie once a mutual block is processed, the result is stored here.
-- accOther contains constructors declarations.
-- accRules contains rules.
-- In this function, we can rely on the mutuality, because a type constructor is considered mutual with its constructors.
orderDeclRules' :: Int32 -> DkModName -> Doc -> Doc -> Doc -> [(Int32,DkDocs)] -> Doc
orderDeclRules' mut mods accTy accOther accRules []                 =
  accTy <> accOther <> accRules
orderDeclRules' mut mods accTy accOther accRules l@((m,(a,b,c)):tl)
  | m==mut =
      orderDeclRules' mut mods
            (accTy    <> a)
            (accOther <> b)
            (accRules <> c)
            tl
  | otherwise =
      orderDeclRules' m mods (accTy <> accOther <> accRules) empty empty l

------------------------------------------------------------------------------
-- The main function --
------------------------------------------------------------------------------

dkCompileDef :: DkOptions -> DkModuleEnv -> IsMain -> Definition -> TCM DkCompiled
dkCompileDef dkOpts env@(mod,eta) _ def@(Defn {defCopy=isCopy, defName=n, theDef=d, defType=t, defMutual=MutId m}) =
  if isCopy
  then do
    reportSDoc "toDk" 8 $ (\x -> text "  No compilation of"<+>x<+>text "which is a copy") <$> AP.prettyTCM n
    return Nothing
  else do
    reportSDoc "toDk" 3 $ (text "  Compiling definition of" <+>) <$> AP.prettyTCM n
    reportSDoc "toDk" 10 $ return $ text "    of type" <+> pretty t
    reportSDoc "toDk" 60 $ return $ text "    " <> pretty def

    let dkMode = case (optDkModeLp dkOpts) of False -> DkMode
                                              True  -> LpMode

    let etaMode = optDkEtaMode dkOpts
    
    (projPar,tParam) <-
      case d of
        Function {funProjection=pr} ->
          case pr of
            Nothing                               -> defaultCase etaMode
            Just Projection{projProper=Nothing}   -> defaultCase etaMode
            -- In case of record projector, symetrically, because of the eta-rule,
            -- the argument type must not be eta-expanded.
            Just Projection{projProper=Just recN} -> do
              dd@Defn{theDef=Record{recPars=i}} <- getConstInfo recN
              tExpand <- if etaMode then etaExpandType eta t else return t
              tPar <- inTopContext $ do
                reconstructParametersInType' (etaExpandAction eta etaMode) tExpand
              return (Just i, tPar)
        _ -> defaultCase etaMode
    reportSDoc "toDk.eta" 35 $ (text "    tParam is" <+>) <$> AP.pretty tParam

    inTopContext $ do
      reportSDoc "toDk" 15 $ return $ text "Getting type"
      typ        <- translateType env etaMode tParam projPar
      reportSDoc "toDk" 15 $ return $ text "Getting name"      
      Right name <- qName2DkName env etaMode n -- n is not a copy
      reportSDoc "toDk" 15 $ return $ text "Getting kind"
      kind       <- getKind env etaMode t
      reportSDoc "toDk" 15 $ return $ text "Getting staticity"
      stat       <- extractStaticity n d
      reportSDoc "toDk" 15 $ return $ text "Getting rules of " <+> pretty d
      rules      <- extractRules env etaMode n d t

      let dkDef = DkDefinition
            { name      = name
            , staticity = stat
            , typ       = typ
            , kind      = kind
            , rules     = rules}
      let printedDef = toDkDocs (modName2DkModIdent mod) dkMode dkDef
      return $ Just (m, printedDef)

  where
    defaultCase etaMode = do
      tExpand <- checkInternalType' (etaExpandAction eta etaMode) t

      reportSDoc "toDk.eta" 35 $ return (text " t1")
      tPar <- inTopContext $ do
        reconstructParametersInType' (etaExpandAction eta etaMode) tExpand
      reportSDoc "toDk.eta" 35 $ return (text " t2")
      return (Nothing, tPar)

translateType :: DkModuleEnv -> EtaMode -> Type -> Maybe Nat -> TCM DkTerm
-- a type is a term with a sort annotation (as in nat : Set0)
-- to translate it, we extract the term and ignore the sort
translateType env etaMode (El {unEl=ty}) i = translateTerm' env etaMode ty i

extractStaticity :: QName -> Defn -> TCM IsStatic
extractStaticity _ (Axiom _)         = return Static
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
-- trying to guess the following ones, not sure
extractStaticity _ (PrimitiveSort {})    = return Defin
extractStaticity _ (AbstractDefn {})    = return Static


  
extractRules :: DkModuleEnv -> EtaMode -> QName -> Defn -> Type -> TCM [DkRule]
extractRules env etaMode n (funDef@Function {}) ty =
  do
    -- if this is an alias function, it does not go through the covering checker,
    -- the only way to know if this is the case is to check if funCovering is empty
    -- and funClauses is not
    let getFunCovering = 
          if (length (funCovering funDef) == 0 && length (funClauses funDef) /= 0)
          then funClauses funDef 
          else funCovering funDef
                           
    
    -- gets the clauses to be translated
    clauses <- case funProjection funDef of
        Nothing -> do
        -- not a projection, we get the clauses after the covering checker          
          reportSDoc "toDk.clause" 20 $
            (text " taking clauses from funCovering : " <+>) <$>
            (return $ pretty $ getFunCovering )            
          return $ getFunCovering  
        Just proj  -> case projProper proj of
        -- this function is projection-like, but is it a real projection
        -- from a record?
          Nothing -> do
        -- not a record projection, we get clauses from funCovering
            reportSDoc "toDk.clause" 20 $
              (text " taking clauses from funCovering : " <+>) <$>
              (return $ pretty $ getFunCovering )            
            return $ getFunCovering
          Just _ -> do
        -- record projection, we take funClauses because projections don't go
        -- throught the covering checker          
            reportSDoc "toDk.clause" 20 $
              (text " taking clauses from funClauses : " <+>) <$>
              (return $ pretty $ funClauses funDef )
            return $ funClauses funDef

    l  <- mapM (clause2rule env etaMode n) clauses
    return $ catMaybes l

extractRules env etaMode n (Datatype {dataCons=cons, dataClause=dataClauses, dataPars=i, dataIxs=j}) ty=
  do
    l <- case dataClauses of
           Just c  -> sequence [clause2rule env etaMode n c, Just <$> decodedVersion env etaMode n (i+j)]
           Nothing -> sequence [Just <$> decodedVersion env etaMode n (i+j)]
    if etaMode
      then (catMaybes l ++) <$> (etaIsId env n i j cons)
      else return $ catMaybes l
extractRules env etaMode n (t@Record {recClause=clauses, recPars=i, recConHead=hd, recFields=f}) ty =
  do
    translatedClauses <- maybe (return []) (\c -> sequence [clause2rule env etaMode n c]) clauses
    decodedVers <- sequence [Just <$> decodedVersion env etaMode n i]
    if etaMode
      then do
      let hasEta =
            case (theEtaEquality $ recEtaEquality' t) of
              YesEta  -> True
              NoEta _ -> False
      etaExpDecl <- if hasEta
                    then sequence [Just <$> etaExpansionDecl env n i hd f]
                    else sequence [Just <$> doesNotEtaExpand env n i hd f]
      return $ catMaybes $ translatedClauses ++ decodedVers ++ etaExpDecl

      else return $ catMaybes $ translatedClauses ++ decodedVers
    
extractRules env etaMode n (Primitive {primClauses=p}) ty =
  do
    recordCleaned <- mapM translateRecordPatterns p
    l <- mapM (clause2rule env etaMode n) recordCleaned
    return $ catMaybes l
extractRules _ _ _ _ _                            = sequence []

decodedVersion :: DkModuleEnv -> EtaMode -> QName -> Int -> TCM DkRule
decodedVersion env@(_,eta) etaMode nam i = do
  reportSDoc "toDk" 5 $ return $ text "  Decoding" <+> pretty nam
  Right nn@(DkQualified mods pseudo n) <- qName2DkName env etaMode nam -- nam is not a copy
  let decodedName = DkQualified mods ("TYPE":pseudo) n
  let hd = DkSpecial TermSymb
  ty <- defType <$> getConstInfo nam
  tele <- theTel <$> (telView ty)
  reportSDoc "toDk" 15 $ ((text "    In the context:") <+> ) <$> (AP.prettyTCM tele)
  addContext tele $
    unsafeModifyContext separateVars $ do
    tel <- getContext
    ctx <- extractContextNames tel
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
      va <- if etaMode then etaExpansion eta (raise (i+1) ty) (var i) else return $ var i
      vaPar <- reconstructParameters (raise (i+1) ty) va
      constructRhs tl (i+1) (\x -> clo =<< (DkApp x <$> translateTerm env etaMode vaPar)) t

clause2rule :: DkModuleEnv -> EtaMode -> QName -> Clause -> TCM (Maybe DkRule)
clause2rule env@(_,eta) etaMode nam c = do
  reportSDoc "toDk.clause" 5  $ ((text "  We are treating:") <+>) <$> (AP.prettyTCM nam)
  reportSDoc "toDk.clause" 10 $ return $ (text "  The clause is") <+> (pretty c)
  reportSDoc "toDk.clause" 20 $ ((text "  In the context:") <+> ) <$> (AP.prettyTCM (clauseTel c))
  reportSDoc "toDk.clause" 20 $ return $ (text "  The type is:") <+> (pretty (clauseType c))
  reportSDoc "toDk.clause" 20 $ return $ (text "  The body is:") <+> (pretty (clauseBody c))
  reportSDoc "toDk.clause" 50 $ return $ text $ "    More precisely:" ++ show (clauseBody c)
  case (clauseBody c) of
    -- Nothing means this is an absurd clause, with () at the end, so it has no body
    Nothing  -> return Nothing
    Just r   ->
      -- adds to the context the bound variables of the clause
      addContext (clauseTel c) $
      unsafeModifyContext separateVars $
      do
        reportSDoc "toDk2" 3 $ return $ text "On a changé le contexte"
        tele <- getContext
        ctx <- extractContextNames tele

        -- record projections clauses don't go throught the covering checker, so in
        -- particular the clauses do not contain the implicit arguments (which in
        -- this case are simply the record parameters), which are inserted by the
        -- covering checker. therefore, we get the number of implicit arguments, so we
        -- generate joker in order to fill the implicit arguments.
        -- for the othe functions, they already have the implicit arguments, as they
        -- have already went trough the covering checker
        imp <- isProjection nam        
        implicits <-
          case imp of
            Nothing                             -> return 0
            Just Projection{projProper=Nothing} -> return 0
            Just Projection{projProper=Just n}  ->
              (fromMaybe __IMPOSSIBLE__) <$> getNumberOfParameters n
        let impArgs = implicitArgs implicits (reverse ctx)
        
        reportSDoc "toDk2" 3 $ return $ text "On a les implicites"

        -- eta expands the rhs and reconstructs the parameters
        rhsExpanded <-
          case clauseType c of
            Nothing -> do
              -- No type stored in this clause (why?), so we don't eta expand
              reportSDoc "toDk.clause" 25 $ return $ text "    Clause without type !"
              return r
            Just t  -> do
              -- We use the type to eta expand
              reportSDoc "toDk2" 3 $ return $ text "On a bien un type"
              r1 <- checkInternal' (etaExpandAction eta etaMode) r CmpLeq (unArg t)
              reportSDoc "toDk2" 3 $ return $ text "On a fait le premier chkIn"
              reconstructParameters' (etaExpandAction eta etaMode) (unArg t) r1
        reportSDoc "toDk.clause" 30 $ return $ text "    Parameters reconstructed"
        reportSDoc "toDk.clause" 40 $ return $ text "    The final body is" <+> pretty rhsExpanded
        reportSDoc "toDk2" 3 $ return $ text "On a reconstruit les paramètres"

        -- translates rhs
        rhsDk <- translateTerm env etaMode rhsExpanded

        -- gets the type of the name nam
        tyHd <- defType <$> getConstInfo nam

        
        reportSDoc "toDk2" 3 $ return $ text "On a traduit à droite"
        let tyInst = piApply tyHd (map (defaultArg . patternToTerm . snd) impArgs)
        reportSDoc "toDk2" 3 $ return $ text "On extrait les patterns"


        Right headSymb <- qName2DkName env etaMode nam -- nam is not a copy

        (headSymb, patts) <- extractPatterns env etaMode (namedClausePats c) tyInst (map fst impArgs) headSymb

        reportSDoc "toDk2" 3 $ return $ text "On a extrait les patterns"
        reportSDoc "toDk2" 3 $ return $ text "On a extrait les p " <+> pretty (namedClausePats c)
        reportSDoc "toDk2" 3 $ return $ text "On a extrait les p " <+> pretty nam

        return $ Just DkRule
          { decoding  = False
          , context   = ctx
          , headsymb  = headSymb
          , patts     = patts
          , rhs       = rhsDk
          }

    where
      implicitArgs 0 locCtx = []
      implicitArgs n (h:tl) =
        (DkVar h (length tl) [], varP (DBPatVar h (length tl))):(implicitArgs (n-1) tl)

-- gets the names of the types in the context
extractContextNames :: Context -> TCM DkCtx
extractContextNames = extractContextAux []

extractContextAux :: DkCtx -> Context -> TCM DkCtx
extractContextAux acc [] = return $ reverse acc
extractContextAux acc (Dom {unDom=(n,t)}:r) = extractContextAux (name2DkIdent n:acc) r


extractPatterns ::  DkModuleEnv ->
                    EtaMode ->
                    [NamedArg DeBruijnPattern] -> --patterns p1 .. pk to be translated
                    Type -> -- type of already translated part
                    [DkPattern] -> -- already translated part
                    DkName -> -- head of the already translated part
                    TCM (DkName, [DkPattern])
extractPatterns env etaMode [] typ dkPatts dkHead = do
  reportSDoc "toDk.pattern" 15 $ return $ text $ "    Finished extraction, the result is " ++ show (dkHead, dkPatts)
  return (dkHead, dkPatts)

extractPatterns env etaMode (p:patts) typ dkPatts dkHead = do
  reportSDoc "toDk.pattern" 15 $ return $ text $ "    The current state is  " ++ show (dkHead, dkPatts)
  reportSDoc "toDk.pattern" 15 $ return $ text "    Now we begin translating  " <+> pretty p
  
  typ <- normalise typ
  (translatedPattern, newType) <- extractPattern env etaMode p typ
  
  case namedArg p of
    ProjP _ _ -> do
      -- the application of f e1 ... en to the projection p should be translated as
      -- p a1 .. ak (f e1 .. en), where the a1 .. ak are the parameters of the record

      -- gets the head symbol and the arguments
      DkFun head args <- return translatedPattern

      extractPatterns env etaMode patts newType (args ++ [DkFun dkHead dkPatts]) head

    _ -> do
      extractPatterns env etaMode patts newType (dkPatts ++ [translatedPattern]) dkHead


-- if we are translating a pattern p which is applied to f e1 .. ek, then we need
-- the type of f e1 .. ek. we return the translation of p and the type
-- of f e1 .. ek p
extractPattern :: DkModuleEnv -> EtaMode -> NamedArg DeBruijnPattern -> Type ->
                  TCM (DkPattern, Type)
extractPattern env@(_,eta) etaMode p applyingType = do
  reportSDoc "toDk.pattern" 15 $ return $ text "    Extraction of the pattern" <+> pretty p

  let patt = namedThing (unArg p)
  case patt of
    VarP _ (DBPatVar {dbPatVarIndex=i})  -> do
      reportSDoc "toDk2" 3 $ return $ text "VarP"
      nam <- nameOfBV i

      -- gets type of f e1 ... ek p
      let finalTy = piApply applyingType [defaultArg (patternToTerm (namedArg p))]

      return $ (DkVar (name2DkIdent nam) i [], finalTy)

    DotP _ t                             -> do
      reportSDoc "toDk2" 3 $ return $ text "DotP"
      
      let patternType = case applyingType of
                          El _ (Pi (Dom{unDom=domainType}) _) -> domainType
                          _ -> __DUMMY_TYPE__
 
      tChk <- checkInternal' (etaExpandAction eta etaMode) t CmpLeq patternType
      tRecons <- reconstructParameters' (etaExpandAction eta etaMode) patternType tChk
      term <- translateTerm env etaMode tRecons

      -- gets type of f e1 ... ek p
      let finalTy = piApply applyingType [defaultArg (patternToTerm (namedArg p))]
      
      return $ (DkGuarded term, finalTy)
--      return $ (DkJoker, finalTy)

    ConP (ConHead {conName=h}) ci tl     -> do
      reportSDoc "toDk2" 3 $ return $ text "ConP" <+> pretty h

      -- let f e1 ... ek the part of the patterns already translated and applyingType
      -- its type. the pattern p we are translating applies to the right of it
      -- so applyingType must be a product (x:domainType) -> coDomainType.
      -- therefore, domainType gives the type of the pattern p we are translating.

      let patternType = case applyingType of
                          El _ (Pi (Dom{unDom=domainType}) _) -> domainType
                          _ -> __DUMMY_TYPE__

      -- let p = g a1 ... ak be the pattern we are translating. As g is a
      -- constructor of an inductive type, its type is of the form
      -- g : {x1 : X1} -> ... -> {xl : Xl} ->
      --     (a1 : A1) -> ... -> (ak : Ak) -> T x1 ... xl i1 ... ij
      -- where the x are the params and i the indices of the inductive type. The
      -- parameters are implicit in agda, and thus we need to recover them to
      -- translate p correctly. To do this, we look at the domainType, which will be
      -- T x1 ... xl i1 ... ij and we extract the parameters

      -- gets head symbol type
      headType <- normalise =<< defType <$> getConstInfo h

      -- gets num of params of head symbol
      numParams <- fromMaybe (error "Why no Parameters?") <$> getNumberOfParameters h

      reportSDoc "toDk.clause" 30 $ return
        $ text "    The type of this applied constructor is" <+> pretty patternType
      reportSDoc "toDk.clause" 50 $ return
        $ text "    Type of the constructor is" <+>  pretty headType
      reportSDoc "toDk.clause" 30 $ return
        $ text "    We investigate for" <+>int numParams<+>text "params"


      -- gets the parameters
      (tyArgs, params) <-
        case patternType of
          El _ (Def _ l) -> do
            reportSDoc "toDk.clause" 30 $ return
              $ text "    Found parameters"
            caseParamFun headType (take numParams l)
          otherwise      ->  do
            reportSDoc "toDk.clause" 30 $ return
              $ text "    Parameters not found, the type is not a Def _ l"
            return $ (__DUMMY_TYPE__, replicate numParams DkJoker)

      -- now we have the parameters which are applied to the head symbol g. it's left
      -- to translate the a1 ... ak which are applied to them

      -- translates head symbol
      Right head <- qName2DkName env etaMode h

      -- translates the arguments
      (head, args) <- extractPatterns env etaMode tl tyArgs params head

      let translatedPatt = DkFun head args

      -- gets type of f e1 ... ek p
      let finalTy = piApply applyingType [defaultArg (patternToTerm (namedArg p))]
      
      return $ (translatedPatt, finalTy)

    LitP _ l                            -> do
      reportSDoc "toDk2" 3 $ return $ text "LitP"
      -- gets type of f e1 ... ek p
      let finalTy = piApply applyingType [defaultArg (patternToTerm (namedArg p))]
      return $ (DkPattBuiltin (translateLiteral l), finalTy)
    ProjP _ nam                         -> do
      reportSDoc "toDk2" 3 $ return $ text "ProjP"

      -- we are translating a projection p which is applied to the term f e1 .. ek of
      -- type applyingType. the term f e1 ... ek must be of a record type, so we
      -- should translate this application as p (f e1 .. ek). however, we also need
      -- to translate the parameters of the record, as the type of p is actually
      -- p : {x1 : X1} -> ... -> {xn : Xn} -> Rec x1 .. xn. so the translation
      -- should be p x1 .. xn (f e1 .. ek).
      -- we therefore extract the parameters x1 .. xn from the type of (f e1 .. ek)
      
      -- gets projection def
      imp <- isProjection nam

      -- gets head symbol type
      headType <- normalise =<< defType <$> getConstInfo nam

      -- gets number of parameters
      numParams <-
        case imp of
          Just Projection{projProper = Just _, projFromType = Arg _ nn}  -> do
                maybeNumParams <- getNumberOfParameters nn
                case maybeNumParams of Just n -> return n
                                       _      -> error "Why no params?"
          _ -> error "What is this projection?"
      
      -- gets the parameters
      (tyArgs, params) <-
        case applyingType of
          El _ (Def _ l) -> do
            reportSDoc "toDk.clause" 30 $ return
              $ text "    Found parameters"
            caseParamFun headType (take numParams l)
          otherwise      ->  do
            reportSDoc "toDk.clause" 30 $ return
              $ text "    Parameters not found, the type is not a Def _ l"
            return $ (__DUMMY_TYPE__, replicate numParams DkJoker)
      
      Right dkNam <- qName2DkName env etaMode nam

      -- gets type of p x1 .. xn (f e1 .. ek)
      -- HYPOTHESIS: If proj : {x1:X1} -> .. -> {xn:Xn} -> (rec:Rec x1 .. xn) -> field
      -- is a projection, then field does not depend on rec

      finalTy <- case tyArgs of
                   (El _ (Pi _ u)) -> return $ unAbs u
                   _ -> do
                     reportSDoc "toDk.clause" 30 $ return
                       $ text "    Not an elim, continuing with a dummy "
                       <+> pretty tyArgs
                     return __DUMMY_TYPE__
                                
      return $ (DkFun dkNam params, finalTy)

    otherwise                           ->
      error "Unexpected pattern of HoTT"
  where

    caseParamFun :: Type -> Elims -> TCM (Type,[DkPattern])
    caseParamFun tyCons els = do
      reportSDoc "toDk2" 3 $ return $ text "ELIMS ARE ..."
      caseParamFun' tyCons els []

    caseParamFun' tyCons [] acc = do
      return (tyCons, reverse acc)
    caseParamFun' tyCons@(El _ (Pi (Dom {unDom=tyArg}) _)) ((Apply (Arg _ t)):tl) acc = do
      reportSDoc "toDk2" 3 $ return $ text "We start caseParamFun' with ..."
      reportSDoc "toDk2" 3 $ return $ text "The type is ..."
      ctxHere <- getContext
      reportSDoc "toDk2" 3 $ return $ text "The context is ..."
      tEta <- checkInternal' (etaExpandAction eta etaMode) t CmpLeq tyArg
      reportSDoc "toDk2" 3 $ return $ text "Eta-expansion done"
      tPar <- reconstructParameters' (etaExpandAction eta etaMode) tyArg tEta
      reportSDoc "toDk2" 3 $ return $ text "params reconstructed"
      tDk <- translateTerm env etaMode tPar
      reportSDoc "toDk2" 3 $ return $ text "term translated"
      caseParamFun' (piApply tyCons [defaultArg t]) tl (DkGuarded tDk:acc)

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

substiLvl l (LvlMax n preLvls) = LvlMax n $ map (substiPreLvl l) preLvls

substiPreLvl l (LvlPlus i t) = LvlPlus i (substi l t)

substiSort l (DkSet lv)    = DkSet (substiLvl l lv)
substiSort l (DkProp lv)   = DkProp (substiLvl l lv)
substiSort _ DkSetOmega    = DkSetOmega
substiSort l (DkUniv s)    = DkUniv (substiSort l s)
substiSort l (DkPi s1 s2)  = DkPi (substiSort l s1) (substiSort l s2)
substiSort _ DkDefaultSort = DkDefaultSort

translateElim :: DkModuleEnv -> EtaMode -> DkTerm -> Elims -> TCM DkTerm
-- empty elimination, return the applying term
translateElim env etaMode t []                  = return t
-- we have t applied to el = (e tl). the translation is given by translating
-- e, applying it to t and the callind translateElim env (t e) tl
translateElim env etaMode t (el@(Apply e):tl)      = do
  arg <- translateTerm env etaMode (unArg e)
  translateElim env etaMode (DkApp t arg) tl
-- elimination have gone through unspining, so we cannot have proj eliminations
translateElim env etaMode t (el@(Proj _ qn):tl)    = do
  reportSDoc "toDk" 2 $ ((text "    Pb with:" <+> printTerm Top [] DkMode [] t <+>)<$> AP.prettyTCM el)
  error "Unspining not performed!"
translateElim env etaMode t ((IApply _ _ _):tl) = error "Unexpected IApply"

translateTerm' :: DkModuleEnv -> EtaMode -> Term -> Maybe Nat -> TCM DkTerm
-- Var is a variable possibly applied to a sequence of eliminations (x es)
translateTerm' env etaMode (Var i elims) Nothing = do
  -- gets name of bound variable
  nam <- nameOfBV i
  -- the result is the name of the variable applied to the translation
  -- of the elimination
  translateElim env etaMode (DkDB (name2DkIdent nam) i) elims

translateTerm' env etaMode (Lam _ ab) Nothing = do
  ctx <- getContext
  -- n will be name of the abstracting variable
  let n = freshStr ctx (absName ab)
  -- (adds the name n to the context permanently or just does an action
  -- with n in the context?)
  addContext n $
    do
      -- translates the term inside the abstraction, on this new context
      body <- translateTerm env etaMode (unAbs ab)
      -- gets name of debrunji index 0 (why isn't this always n?)
      nam <- nameOfBV 0
      return $ DkLam (name2DkIdent nam) Nothing body

-- builtin things, like strings, integers, etc
translateTerm' env etaMode (Lit l) Nothing =
  return $ translateLiteral l

-- a function symbol n applied to a list of eliminations
translateTerm' env etaMode (Def n elims) Nothing = do
  -- translate the function symbol
  nn <- qName2DkName env etaMode n
  case nn of
    -- if we get a constant name, we return it applied to the translation of the elim
    Right nam -> translateElim env etaMode (DkConst nam) elims
    -- if we get a term (why?) we translate it applied to the elim
    Left tt -> translateTerm env etaMode (tt `applyE` elims)

translateTerm' env etaMode (Con hh@(ConHead {conName=h}) i elims) Nothing = do
  nn <- qName2DkName env etaMode h
  case nn of
    Right nam -> translateElim env etaMode (DkConst nam) elims
    Left tt -> translateTerm env etaMode (tt `applyE` elims)

translateTerm' env etaMode (Pi d@(Dom {unDom=a}) bb) mb_j = do
  ctx <- getContext
  -- nn is the name of the abstracting variable (Pi nn : a. bb)
  let nn = freshStr ctx (absName bb)
  -- translates the domain type
  dom <- translateType env etaMode a Nothing
  -- gets kind s_a of the domain type
  ka <- getKind env etaMode a
  case bb of
    -- this is a real dependent product, we need to add nn : d to the context
    -- before calculating the domain type
    Abs n b ->
      addContext (nn,d) $ do
        -- translates codomain type
        body <- translateType env etaMode b (pred mb_j)
        -- gets codomain sort
        kb <- getKind env etaMode b
        -- gets name of type parameter (is it different from nn?)
        nam <- nameOfBV 0
        -- analyse the codomain type
        case a of
          -- is it a constant type?
          El {unEl=Def h []} -> do
            hd <- qName2DkName env etaMode h
            -- is it Level?
            if hd == Right (DkQualified ["Agda","Primitive"] [] "Level")
              -- yes! this is a a level quantification
            then return $ DkQuantifLevel kb (name2DkIdent nam) body
              -- no! this is a normal product
            else return $ (sp_prod mb_j) ka kb (name2DkIdent nam) dom body
          -- also a normal product
          otherwise ->
            return $ (sp_prod mb_j) ka kb (name2DkIdent nam) dom body
    -- not a real dependent product, just a regular function arrow a -> bb
    NoAbs n b -> do
      -- translate the codomain type
      body <- translateType env etaMode b (pred mb_j)
      -- gets codomain sort
      kb <- getKind env etaMode b
      -- gets name of type parameter (is it different from nn?)
      nam <- addContext (nn,d) $ nameOfBV 0
      return $ (sp_prod mb_j) ka kb (name2DkIdent nam) dom body
  where
    pred Nothing  = Nothing
    pred (Just 0) = Nothing
    pred (Just j) = Just (j-1)
    sp_prod (Just 0) = DkProjProd
    sp_prod _        = DkProd

translateTerm' env etaMode (Sort s) Nothing = do
  ss <- extractSort env etaMode s
  return $ DkSort ss
  
translateTerm' env etaMode (Level lev) Nothing = do
  lv <- lvlFromLevel env etaMode lev
  return $ DkLevel lv
  
translateTerm' env etaMode (MetaV {}) Nothing = error "Not implemented yet : MetaV"
translateTerm' env etaMode (DontCare t) Nothing = translateTerm env etaMode t
translateTerm' env etaMode (Dummy _ _) Nothing = error "Not implemented yet : Dummy"

translateTerm env etaMode t = translateTerm' env etaMode t Nothing

extractSort :: DkModuleEnv -> EtaMode -> Sort -> TCM DkSort
extractSort env etaMode (Type i)                  =
  DkSet <$> lvlFromLevel env etaMode i
extractSort env etaMode (Prop i)                  =
  DkProp <$> lvlFromLevel env etaMode i
-- for the time beeing we translate all the SetOmegai to the same sort
-- this clearly makes the theory inconsistent, but it should work for now
extractSort env etaMode (Inf _ _)                 =
  return DkSetOmega
extractSort env etaMode SizeUniv                  =
  return $ DkSizeUniv

-- not sure about the following change

extractSort env etaMode (PiSort _ s t) = do
  dom <- extractSort env etaMode s
  codom <- extractSort env etaMode (unAbs t)
  return $ DkPi dom codom

--extractSort env (PiSort (Dom{unDom=s}) t) = do
--  dom <- extractSort env (_getSort s)
--  codom <- extractSort env (unAbs t)
--  return $ DkPi dom codom
extractSort env etaMode (UnivSort s)              =
  DkUniv <$> extractSort env etaMode s
extractSort _ _ _                         =
  return DkDefaultSort

lvlOf :: DkModuleEnv -> EtaMode -> Sort -> TCM Lvl
lvlOf env etaMode (Type i) = lvlFromLevel env etaMode i
lvlOf env etaMode (Prop i) = lvlFromLevel env etaMode i

getKind :: DkModuleEnv -> EtaMode -> Type -> TCM DkSort
getKind env etaMode (El {_getSort=s}) = extractSort env etaMode s

-- the two functions were modified to account for the new representation of
-- levels in agda
lvlFromLevel :: DkModuleEnv -> EtaMode -> Level -> TCM Lvl
lvlFromLevel env etaMode (Max i l) =
  do
    preLvls <- mapM (preLvlFromPlusLevel env etaMode) l
    return $ LvlMax (fromInteger i) preLvls

preLvlFromPlusLevel :: DkModuleEnv -> EtaMode -> PlusLevel -> TCM PreLvl
preLvlFromPlusLevel env etaMode (Plus i t) = LvlPlus (fromInteger i) <$> translateTerm env etaMode t

translateLiteral :: Literal -> DkTerm
translateLiteral (LitNat    i)   = DkBuiltin (DkNat (fromInteger i))
translateLiteral (LitWord64 _)   = error "Unexpected literal Word64"
translateLiteral (LitFloat  _)   = error "Unexpected literal Float"
translateLiteral (LitString s)   = DkBuiltin (DkString (unpack s))
translateLiteral (LitChar   c)   = DkBuiltin (DkChar c)
translateLiteral (LitQName  _)   = error "Unexpected literal QName"
translateLiteral (LitMeta   _ _) = error "Unexpected literal Meta"

addEl :: Term -> Elim -> Term
addEl (Var i elims) e = Var i (elims++[e])
addEl (Def n elims) e = Def n (elims++[e])
addEl (Con h i elims) e = Con h i (elims++[e])
addEl _ _ = error "Those terms do not expect elimination"


--------------------------------------------------------------------------------
-- Translation of Name and QName function
--------------------------------------------------------------------------------

qName2DkName :: DkModuleEnv -> EtaMode -> QName -> TCM (Either Term DkName)
qName2DkName env@(_,eta) etaMode qn@QName{qnameModule=mods, qnameName=nam}
  | qn == eta = return $ Right $ DkSpecial EtaExpandSymb
  | otherwise = do
      topMod <- topLevelModuleName mods
      def <- getConstInfo qn
      if defCopy def
      then do
        let ty = defType def
        -- why do we need to do etaExpansion here? why do we need to do this
        -- only to get the name?
        reportSDoc "toDk2" 3 $ return $ text "ty Here" <+> pretty ty
        -- this first step is just to eta-expand, in order to trigger reduction
        tChk <- checkInternal' (etaExpandAction eta etaMode) (Def qn []) CmpLeq ty
        reportSDoc "toDk2" 3 $ return $ text "tChk OK"
        tRed <- normalise tChk
        reportSDoc "toDk2" 3 $ return $ text "tRed OK"
        -- We have to do it again since normalise eliminated it
        tChk2 <- checkInternal' (etaExpandAction eta etaMode) tRed CmpLeq ty
        reportSDoc "toDk2" 3 $ return $ text "tChk2 OK"
        tRecons <- reconstructParameters' (etaExpandAction eta etaMode) ty tChk2
        reportSDoc "toDk2" 3 $ return $ text "tRecons OK"
        return $ Left tRecons
      else
        let otherMods = stripPrefix (mnameToList topMod) (mnameToList mods) in
        return $ Right $
          DkQualified (modName2DkModIdent topMod) (maybe [] (map name2DkIdent) otherMods) (name2DkIdent nam)

name2DkIdent :: Name -> DkIdent
name2DkIdent (Name {nameId=NameId id _, nameConcrete=CN.Name {CN.nameNameParts=n}}) =
  let list = toList n in
  let s = concat (map namePart2String list) in
  if s == ".absurdlambda"
  then s ++ ('-' : show id) -- .absurdlambda is not a user written name, it happens to be not unique in some files.
  else s
name2DkIdent (Name {nameConcrete=CN.NoName {}}) =
  "DEFAULT"

namePart2String :: CN.NamePart -> String
namePart2String CN.Hole  = "_"
namePart2String (CN.Id s) = s

modName2DkModIdent :: ModuleName -> DkModName
modName2DkModIdent (MName {mnameToList=l}) = map name2DkIdent l

separateVars :: Context -> Context
separateVars = separateAux ["_"]

separateAux used [] = []
--separateAux used ((d@Dom{unDom=(n@Name{nameConcrete=cn@CN.Name{CN.nameNameParts=l}},ty)}):tl) =
separateAux used ((d@Dom{unDom=(n@Name{nameConcrete=cn},ty)}):tl) =
  let s= name2DkIdent n in
  let ss = computeUnused used (-1) s in
  let ns = (CN.Id ss) :| [] in
  d {unDom=(n {nameConcrete= cn {CN.nameNameParts=ns}},ty)}:(separateAux (ss:used) tl)

-- gets the list of names used in the context
usedVars :: Context -> [String]
usedVars = map (name2DkIdent . fst . unDom)

-- used by freshStr
computeUnused used i s =
  let ss = if i==(-1) then s else s++(show i) in
  if elem ss used
  then computeUnused used (i+1) s
  else ss

-- freshStr ctx name returns either name or nameX for some integer X,
-- such that the returned string is not used in the context
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
    list <- sequence [freshName_ "etaExpand", freshName_ "etaExpand"]
    let name = qnameFromList $ fromList list
    tele <- theTel <$> telView typeId
    let args = [
          defaultArg (namedDBVarP 2 "a"),
          defaultArg (namedDBVarP 1 "A"),
          defaultArg (namedDBVarP 0 "x")
          ]
    -- currently we consider we don't need K for this def, may be changed on the future?
    addConstant name $ defaultDefn defaultArgInfo name typeId WithoutK emptyFunction{funClauses=[defaultClause{clauseTel=tele, namedClausePats=args, clauseBody=Just $ var 0, clauseType = Just $ defaultArg $ El (varSort 2) (var 1)}]}
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
      -- guessing the following parammeters
      , clauseEllipsis    = NoEllipsis
      , clauseExact       = Nothing
      , clauseRecursive   = Nothing
    }

etaExpandType :: QName -> Type -> TCM Type
etaExpandType eta (El s (Pi a@Dom{unDom=El sa u} b)) = do
  uu <- checkInternal' (etaExpandAction eta True) u CmpLeq (sort sa)
  let dom = El sa uu
  addContext (absName b,a) $ do
    codom <- etaExpandType eta (absBody b)
    unsafeEscapeContext 1 $ return $ El s (Pi a{unDom=dom} (Abs (absName b) codom))
etaExpandType eta (El s u) = do
  uu <- checkInternal' (etaExpandAction eta True) u CmpLeq (sort s)
  return $ El s uu

etaIsId :: DkModuleEnv -> QName -> Nat -> Nat -> [QName] -> TCM [DkRule]
etaIsId env@(_,eta) n i j cons = do
  reportSDoc "toDk.eta" 5 $ (text "  Eta is id of" <+>) <$> AP.prettyTCM n
  mapM oneCase cons

  where
    hd = DkSpecial EtaExpandSymb
    oneCase f = do
      Defn{defType=tt} <- getConstInfo f
      TelV tele _ <- telView tt
      addContext tele $
        unsafeModifyContext separateVars $ do
        -- We do have the information that n is not a copy,
        -- otherwise it would not have gone through compileDef
        Right cc <- qName2DkName env True f
        Right nn <- qName2DkName env True n
        ctx <- getContext
        context <- extractContextNames ctx
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
      (vj, _) <- extractPattern env True (defaultArg $ unnamed $ varP (DBPatVar "_" j))
                 __DUMMY_TYPE__
      nextIndex (vj:acc) (j+1) tl

    constructRhsFields _ t [] = return t
    constructRhsFields j t (Dom{unDom=(_,tt)}:tl) = do
      let ttGoodDB = raise (j+1) tt
      vEta <- checkInternal' (etaExpandAction eta True) (Var j []) CmpLeq ttGoodDB
      vParam <- reconstructParameters' (etaExpandAction eta True) ttGoodDB vEta
      dkArg <- translateTerm env True vParam
      (`DkApp` dkArg) <$> constructRhsFields (j+1) t tl

etaExpansionDecl :: DkModuleEnv -> QName -> Int -> ConHead -> [Dom QName] -> TCM DkRule
etaExpansionDecl env@(_,eta) n nbPars ConHead{conName = cons} l = do
  reportSDoc "toDk.eta" 5 $ (text "  Declaration of eta-expansion of" <+>) <$> AP.prettyTCM n
  let hd = DkSpecial EtaExpandSymb
  Defn{defType=tt} <- getConstInfo n
  TelV tele _ <- telView tt
  addContext tele $
    unsafeModifyContext separateVars $ do
    -- We do have the information that n is not a copy,
    -- otherwise it would not have gone through compileDef
    Right nn <- qName2DkName env True n
    Right cc <- qName2DkName env True cons
    y <- (\ctx -> freshStr ctx "y") <$> getContext
    let ty = apply (Def n []) (teleArgs tele)
    s <- checkType' $ El (Inf IsFibrant 0) ty
    addContext (y,defaultDom $ El s ty) $ do
      ctx <- getContext
      context <- extractContextNames ctx
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
      (vj, _) <- extractPattern env True (defaultArg $ unnamed $ varP (DBPatVar "_" j))
                 __DUMMY_TYPE__
      nextIndex (vj:acc) (j+1) tl
    constructRhs :: DkTerm -> [Dom (Name, Type)] -> DkIdent -> TCM DkTerm
    constructRhs t args y = do
      tParam <- constructRhsParams t args
      constructRhsFields tParam args (map unDom l)

    constructRhsParams t (_:tl) = constructRhsParams' 1 t tl return
    constructRhsParams t []     = return t
    constructRhsParams' _ t []                     clo = clo t
    constructRhsParams' j t (Dom{unDom=(a,ty)}:tl) clo = do
      va <- etaExpansion eta (raise (j+1) ty) (var j)
      vaPar <- reconstructParameters (raise (j+1) ty) va
      constructRhsParams' (j+1) t tl (\x -> clo =<< (DkApp x <$> translateTerm env True vaPar))

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
      prEta <- checkInternal' (etaExpandAction eta True) (Var 0 [Proj ProjSystem u]) CmpLeq tyRes
      reportSDoc "toDk.eta" 35 $ return $ text "  Eta expansion done"
      reportSDoc "toDk.eta" 35 $ return $ text "    " <> pretty prEta
      Right prDkName <- qName2DkName env True u
      prDk <- studyEtaExpansion prEta args prDkName 0 tyRes (\x -> x)
      constructRhsFields (DkApp t prDk) args tl

    studyEtaExpansion t args prName i tyRes clo = case t of
      Def nam ((Apply s):(Apply tyBis):_:[]) ->
        if nam == eta
        then do
          case unArg s of
            Level ss -> do
              tyRecons <- reconstructParameters' (etaExpandAction eta True) (sort (Type ss)) (unArg tyBis)
              etaCtx <- translateTerm env True (Def nam [Apply s,Apply tyBis{unArg=tyRecons}])
              unsafeEscapeContext i $ do
                v <- translateTerm env True (Var 0 [])
                DkApp etaCtx <$> clo <$> (`DkApp` v) <$> constructRhsParams (DkConst prName) args
            otherwise -> __IMPOSSIBLE__
        else __IMPOSSIBLE__
      Var i _ -> do
        v <- translateTerm env True (Var i [])
        unsafeEscapeContext i $
          clo <$> (`DkApp` v) <$> constructRhsParams (DkConst prName) args
      Lam _ body -> do
        case unEl tyRes of
          Pi a b -> do
            reportSDoc "toDk.eta" 40 $ return $ text "    We study a Lambda" <+> pretty (unAbs body)
            El s tDom <- reconstructParametersInType' (etaExpandAction eta True) =<< etaExpandType eta (unDom a)
            dkTDom <- translateTerm env True tDom
            dkL <- lvlOf env True s
            dkS <- extractSort env True s
            addContext (absName body,a) $
              unsafeModifyContext separateVars $ do
              x <- nameOfBV 0
              let clo2 rest = DkApp rest (DkApp (DkApp (DkApp (DkConst (DkSpecial EtaExpandSymb)) (DkLevel dkL)) dkTDom)  (DkDB (name2DkIdent x) 0))
              DkLam (name2DkIdent x) (Just (dkTDom,dkS)) <$> studyEtaExpansion (absBody body) args prName (i+1) (absBody b) (clo2 . clo)
          otherwise -> __IMPOSSIBLE__
      otherwise -> __IMPOSSIBLE__

doesNotEtaExpand :: DkModuleEnv -> QName -> Int -> ConHead -> [Dom QName] -> TCM DkRule
doesNotEtaExpand env@(_,eta) n nbPars ConHead{conName = cons} l = do
  reportSDoc "toDk.eta" 5 $ (text "  Declaration of non eta-expansion of" <+>) <$> AP.prettyTCM n
  let hd = DkSpecial EtaExpandSymb
  Defn{defType=tt} <- getConstInfo n
  TelV tele _ <- telView tt
  addContext tele $
    unsafeModifyContext separateVars $ do
    -- We do have the information that n is not a copy,
    -- otherwise it would not have gone through compileDef
    Right nn <- qName2DkName env True n
    Right cc <- qName2DkName env True cons
    y <- (\ctx -> freshStr ctx "y") <$> getContext
    let ty = apply (Def n []) (teleArgs tele)
    s <- checkType' $ El (Inf IsFibrant 0) ty
    addContext (y,defaultDom $ El s ty) $ do
      ctx <- getContext
      context <- extractContextNames ctx
      tyArg <- pattTy nn ctx
      return $ DkRule
        { decoding  = False
        , context   = context
        , headsymb  = hd
        , patts     = [DkJoker, tyArg, DkVar y 0 []]
        , rhs       = DkDB y 0
        }

  where
    pattTy cc args =
      DkFun cc <$> nextIndex [] 0 args
    nextIndex acc 0 (_:tl) = nextIndex acc 1 tl
    nextIndex acc j []     = return acc
    nextIndex acc j (_:tl) = do
      (vj, _) <- extractPattern env True (defaultArg $ unnamed $ varP (DBPatVar "_" j))
                 __DUMMY_TYPE__
      nextIndex (vj:acc) (j+1) tl


etaExpandAction :: QName -> Bool -> Action TCM
etaExpandAction eta True = defaultAction { preAction = \y -> etaContractFun , postAction = etaExpansion eta}
etaExpandAction eta False = defaultAction

etaContractFun :: Term -> TCM Term
etaContractFun u = case u of
  Lam i (Abs x b) -> etaLam i x b
  otherwise -> return u

etaExpansion :: QName -> Type -> Term -> TCM Term
etaExpansion eta t u@(Lam _ _)  = return u -- No need to eta-expand a lambda
etaExpansion eta t u = do
  reportSDoc "toDk.eta" 35 $ (text "    Eta expansion of" <+>) <$> AP.prettyTCM u
  reportSDoc "toDk.eta" 50 $ (text "      of type" <+>) <$> AP.prettyTCM t
  reportSDoc "toDk.eta" 50 $ (text "      of sort" <+>) <$> AP.prettyTCM (_getSort t)
  case _getSort t of
    Type _ -> defaultCase
    _ -> return u
  where
    defaultCase =
      case unEl t of
        Var _ _   -> etaExp t u
        Def n _ -> do
          defin <- getConstInfo n
          reportSDoc "toDk.eta" 70 $ (text "     theDef" <+>) <$> (return $ text $ show $ theDef defin)
          case (theDef $ defin) of
            Record {recEtaEquality' = withEta} ->
              case theEtaEquality withEta of
                YesEta  -> ifM (isLevel n) (return u) (etaExp t u)
                NoEta _ -> return u
            _  -> ifM (isLevel n) (return u) (etaExp t u)

        Pi (a@Dom{domInfo=info}) b -> do
          reportSDoc "toDk.eta" 40 $ (text "    In the product" <+>) <$> AP.prettyTCM t
          ctx <- getContext
          let n = freshStr ctx (absName b)

          case _getSort $ unDom a of
            Type _ -> do
              aExp <- etaExpandType eta (unDom a)
              aIsLevel <- case aExp of
                            El _ (Def n _) -> isLevel n
                            otherwise      -> return False
              addContext (n,a) $ do
                let s = raise 1 (getElimSort (unDom a))
                let varLong = Def eta [Apply s, Apply . defaultArg . (raise 1) . unEl $ aExp, Apply $ defaultArg (Var 0 [])]
                let theVar = if aIsLevel then Var 0 [] else varLong
                let appli = applyE (raise 1 u) [Apply (Arg info theVar)]
                body <- etaExpansion eta (absBody b) appli
                return $ Lam info (Abs n body)
            _ -> do
              let aExp = unDom a
              addContext (n,a) $ do
                let theVar = Var 0 []
                let appli = applyE (raise 1 u) [Apply (Arg info theVar)]
                body <- etaExpansion eta (absBody b) appli
                return $ Lam info (Abs n body)

        Sort _ -> return u
        otherwise ->
          do
            reportSDoc "toDk.eta" 3 $ (text "    Eta expansion of" <+>) <$> AP.prettyTCM u
            reportSDoc "toDk.eta" 3 $ (text "      of type" <+>) <$> AP.prettyTCM t
            __IMPOSSIBLE__

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
