
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
                        , getDirectoryContents, copyFile
                        )
import Data.List as L
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
import Agda.Utils.FileName
import Agda.Utils.Pretty
import Agda.Utils.IO.Directory
import Agda.Utils.Lens
import Agda.Utils.Monad

import Agda.Compiler.Common
import Agda.Compiler.Backend

import Agda.Utils.Impossible

import Agda2Dk.DkSyntax

-- Backend callbacks ------------------------------------------------------

dkBackend :: Backend
dkBackend = Backend dkBackend'

dkBackend' :: Backend' DkOptions DkOptions DkModuleEnv () DkDefinition
dkBackend' = Backend'
  { backendName           = "Dk"
  , backendVersion        = Nothing
  , options               = defaultDkOptions
  , commandLineFlags      = dkCommandLineFlags
  , isEnabled             = optDkCompile
  , preCompile            = \opts -> return opts
  , postCompile           = \_ _ _ -> return ()
  , preModule             = \_ _ _ _ -> return (Recompile ())
  , postModule            = dkPostModule
  , compileDef            = dkCompileDef
  , scopeCheckingSuffices = False
  , mayEraseType          = \_ -> return True
  }

--- Options ---

data DkOptions = DkOptions
  { optDkCompile :: Bool
  , optDkFlags   :: [String]
  }

defaultDkOptions :: DkOptions
defaultDkOptions = DkOptions
  { optDkCompile = False
  , optDkFlags   = []
  }

dkCommandLineFlags :: [OptDescr (Flag DkOptions)]
dkCommandLineFlags =
    [ Option []     ["dk"] (NoArg compileDkFlag) "compile program using the Dk backend"
    ]
  where
    compileDkFlag o      = return $ o { optDkCompile = True}

--- Module compilation ---

type DkModuleEnv = ()

dkPostModule :: DkOptions -> DkModuleEnv -> IsMain -> ModuleName -> [DkDefinition] -> TCM ()
dkPostModule opts _ _ _ l =
  let output = hcat (map prettyDk l) in
  liftIO $ writeFile "output.dk" (show output)

-- The main function --

dkCompileDef :: DkOptions -> DkModuleEnv -> IsMain -> Definition -> TCM (DkDefinition)
dkCompileDef _ _ _ (Defn {defName=n, theDef=d, defType=t}) =
  let name = qname2DkName n in
  return DkDefinition
    { name = name
    , staticity = extractStaticity d
    , typ = translateType t
    , rules = extractRules name d}

-- TODO: All the zeros are randomly put.

translateType :: Type -> DkTerm
translateType (El {_getSort=_, unEl=x}) = translateTerm x

extractStaticity :: Defn -> IsStatic
extractStaticity Axiom             = True
extractStaticity (DataOrRecSig {}) = True
extractStaticity GeneralizableVar  = True
extractStaticity (Function {})     = False
extractStaticity (Datatype {})     = True
extractStaticity (Record {})       = True
extractStaticity (Constructor {})  = True
extractStaticity (Primitive {})    = False

extractRules :: DkName -> Defn -> [DkRule]
extractRules n Axiom                            = []
extractRules n (DataOrRecSig {})                = []
extractRules n GeneralizableVar                 = []
extractRules n (Function {funClauses=f})        = map (clause2rule n) f
extractRules n (Datatype {dataClause=Nothing})  = []
extractRules n (Datatype {dataClause=Just c})   = [clause2rule n c]
extractRules n (Record {recClause=Nothing})     = []
extractRules n (Record {recClause=Just c})      = [clause2rule n c]
extractRules n (Constructor {})                 = []
extractRules n (Primitive {primClauses=p})      = map (clause2rule n) p

clause2rule :: DkName -> Clause -> DkRule
clause2rule n c =
  DkRule
  { context  = extractContext (clauseTel c)
  , headsymb = n
  , patts    = map extractPattern (namedClausePats c)
  , rhs      =
    case (clauseBody c) of
      Nothing  -> DkFake ""
      Just rhs -> translateTerm rhs
  }

extractContext :: Telescope -> DkCtx
extractContext EmptyTel                                              = DkCtx []
extractContext (ExtendTel (Dom {unDom=t}) (Abs {absName=n,unAbs=r})) =
  let DkCtx tl = extractContext r in
  DkCtx ((defaultId n, translateType t):tl)

-- TODO --
extractPattern :: NamedArg DeBruijnPattern -> DkPattern
extractPattern x =
  let pat = namedThing (unArg x) in
  case pat of
    VarP _ (DBPatVar {dbPatVarName=n,dbPatVarIndex=i}) ->
      DkVar (defaultId n) i []
    DotP _ t                                           -> DkBrackets (translateTerm t)
    ConP (ConHead {conName=h}) _ l                     ->
      DkFun (qname2DkName h) (map extractPattern l)
    otherwise                                          -> DkBrackets (DkFake "")

translateTerm :: Term -> DkTerm
translateTerm (Var i [])                    = DkDB (defaultId "") i
translateTerm (Var i (e:elims))             =
  DkApp (DkDB (defaultId "") i) (translateElim e) (map translateElim elims)
translateTerm (Lam _ (Abs {absName=n,unAbs=a})) =
  DkLam (defaultId n) Nothing (translateTerm a)
translateTerm (Lit _)                       = DkFake ""
translateTerm (Def n [])                    = DkConst (qname2DkName n)
translateTerm (Def n (e:elims))             =
  DkApp (DkConst (qname2DkName n)) (translateElim e) (map translateElim elims)
translateTerm (Con (ConHead {conName=h}) _ [])        =
  DkConst (qname2DkName h)
translateTerm (Con (ConHead {conName=h}) _ (e:elims)) =
  DkApp (DkConst (qname2DkName h)) (translateElim e) (map translateElim elims)
translateTerm (Pi (Dom {unDom=t}) (Abs{absName=n,unAbs=u}))                =
  DkProd (DkSet 0) (DkSet 0) (defaultId n) (translateType t) (translateType u)
translateTerm (Pi (Dom {unDom=t}) (NoAbs{absName=n,unAbs=u}))               =
  DkProd (DkSet 0) (DkSet 0) (defaultId n) (translateType t) (translateType u)
translateTerm (Sort (Type l))               = DkSort (DkSet (intFromLevel l))
translateTerm (Sort (Prop l))               = DkSort (DkSet (intFromLevel l))
translateTerm (Sort Inf)                    = DkSort DkSetOmega
translateTerm (Sort _)                      = DkSort DkDefaultSort
translateTerm (Level _)                     = DkFake ""
translateTerm (MetaV {})                     = DkFake ""
translateTerm (DontCare t)                  = translateTerm t
translateTerm (Dummy _ _)                   = DkFake ""

translateElim :: Elim -> DkTerm
translateElim (Apply e)      = translateTerm (unArg e)
translateElim (Proj _ qn)    = DkFake ""
translateElim (IApply _ _ _) = DkFake ""

intFromLevel :: Level -> Int
intFromLevel (Max [])                  = 0
intFromLevel (Max ((ClosedLevel i):t)) = max (fromInteger i) (intFromLevel (Max t))
intFromLevel (Max ((Plus i _):t))      = max (fromInteger i) (intFromLevel (Max t))

qname2DkName :: QName -> DkName
qname2DkName n = DkQualified (modName2DkModIdent (qnameModule n)) (name2DkIdent (qnameName n))

name2DkIdent :: Name -> DkIdent
name2DkIdent (Name {nameId=NameId w64 _,nameConcrete=CN.Name {CN.nameNameParts=n}}) =
  DkIdent {w64 = w64, concrete = concat (map namePart2String n)}
name2DkIdent (Name {nameId=NameId w64 _,nameConcrete=CN.NoName {}}) =
  DkIdent {w64 = w64, concrete = "DEFAULT"}

namePart2String :: CN.NamePart -> String
namePart2String CN.Hole  = "_"
namePart2String (CN.Id s) = s

modName2DkModIdent :: ModuleName -> DkModName
modName2DkModIdent (MName {mnameToList=l}) = map name2DkIdent l

defaultId :: String -> DkIdent
defaultId s = DkIdent {w64=toEnum 0,concrete=s}
