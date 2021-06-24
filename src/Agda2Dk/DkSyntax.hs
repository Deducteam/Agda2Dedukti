module Agda2Dk.DkSyntax where

import Data.Word
import Data.List (sort)
import Data.List.Extra (nubOrd)
-- This next line needs the package Unique, install it from Cabal
import Data.List.Unique
import Data.Int
import Data.Char

-- hides (<>), as there was a conflit with the (<>) defined here
import Prelude hiding ((<>))

import Text.PrettyPrint

import Agda.Syntax.Internal
import qualified Agda.Syntax.Concrete.Name as CN
import Agda.Utils.Impossible


type DkModName = [String]

type DkIdent = String

class PrettyDk a where
  prettyDk :: DkModName -> DkMode -> DkCtx -> a -> Doc

data DkMode = DkMode | LpMode deriving (Show, Eq)

data DkDefinition =
   DkDefinition
    { name      :: DkName
    , staticity :: IsStatic
    , typ       :: DkTerm
    , kind      :: DkSort
    , rules     :: [DkRule]
    } deriving (Show)


etaExpandSymb :: DkName
etaExpandSymb = DkSpecial EtaExpandSymb
--etaExpandSymb = DkQualified ["Agda"] [] "etaExpand"

printDecl :: DkModName -> DkMode -> DkDefinition -> Doc
printDecl mods dkMode
  (DkDefinition {name=defName, staticity=defStat, typ=defType, kind=defSort}) =
  let specialDefRules =
        case defName of
          DkQualified ["Agda", "Primitive"] [] "Level" ->
            pRewRule dkMode (text "[]") (pEl dkMode <+> text "_ Level") (pLvl dkMode)
          DkQualified ["Agda", "Primitive"] [] "lzero" ->
            pRewRule dkMode (text "[]") (text "lzero") (pZero dkMode)
          DkQualified ["Agda", "Primitive"] [] "lsuc"  ->
            pRewRule dkMode (text "[]") (text "lsuc") (pSucc dkMode)
          DkQualified ["Agda", "Primitive"] [] "_⊔_"   ->
            pRewRule dkMode (text "[]") (text "{|_⊔_|}") (pMax dkMode)
          otherwise                                    -> empty
  in
  let defHead = case defStat of
                  Defin      -> pSymb dkMode
                  TypeConstr -> printDecodedDecl mods defName dkMode defType
                                <> pCons dkMode
                  Static     -> pCons dkMode
  in
  let transType = printTerm Nested mods dkMode [] defType in 
  let transSort = printSort Nested mods dkMode [] defSort in
  defHead <> -- symbol + decoded declaration if we are declaring a type
  prettyDk mods dkMode [] defName <+> -- definition name
  text ":" <+> 
  pEl dkMode <+> -- El or Agda.Term
  transSort <+> -- sort of the def
  transType <> -- type of the def
  pEndDef dkMode <> -- .\n or ;\n
  specialDefRules -- extra rule declarations for special definitions

printDecodedDecl :: DkModName -> DkName -> DkMode -> DkTerm -> Doc
printDecodedDecl mods (DkQualified _ pseudo id) dkMode defType =
  let defName = "TYPE__" ++ (concat (map (++ "__") pseudo)) ++ id in
  pCons dkMode <> -- constant symbol or empty
  printIdent dkMode [] defName <+> -- definition name
  char ':' <+>
  decodedType mods dkMode defType <> -- type of the def
  pEndDef dkMode -- .\n or ;\n

decodedType :: DkModName -> DkMode -> DkTerm -> Doc
decodedType mods dkMode (DkSort _)              = pType dkMode
decodedType mods dkMode (DkProd domSort _ id dom coDom)    =
  let transSort = printSort Nested mods dkMode [] domSort in
  let transType = printTerm Nested mods dkMode [] dom in
  pProd dkMode (printIdent dkMode [] id) (Just $ pEl dkMode <+> transSort <+> transType) <+>
  decodedType mods dkMode coDom
decodedType mods dkMode (DkQuantifLevel _ id coDomType) =
  pProd dkMode (printIdent dkMode [] id) (Just $ pLvl dkMode) <+>
  decodedType mods dkMode coDomType

printRules :: DkModName -> (DkRule -> Bool) -> DkMode -> DkDefinition -> [Doc]
printRules mods f dkMode (DkDefinition {rules=l}) =
  map (printRule mods dkMode) (filter f l)

-- a level is a max of a closed level and various pre-levels
data Lvl = LvlMax Int [PreLvl]  deriving (Show)

printLvl :: DkModName -> DkMode -> DkCtx -> Lvl -> Doc
printLvl mods dkMode boundCtx (LvlMax n []) = unary dkMode n
printLvl mods dkMode boundCtx (LvlMax 0 [a]) = prettyDk mods dkMode boundCtx a
printLvl mods dkMode boundCtx (LvlMax n l) =
  parens $ pMax dkMode <+> unary dkMode n <+> printPreLvlList mods dkMode boundCtx l

printPreLvlList :: DkModName -> DkMode -> DkCtx -> [PreLvl] -> Doc
printPreLvlList mods dkMode boundCtx (a:[]) = prettyDk mods dkMode boundCtx a
printPreLvlList mods dkMode boundCtx (a:tl) =
  parens $ pMax dkMode <+>
  prettyDk mods dkMode boundCtx a <+>
  printPreLvlList mods dkMode boundCtx tl

-- a pre-level is an integer and a level expression
data PreLvl = LvlPlus Int DkTerm  deriving (Show)

instance PrettyDk PreLvl where
  prettyDk mods dkMode boundCtx (LvlPlus i t) = iterateSuc dkMode i $ printTerm Nested mods dkMode boundCtx t

iterateSuc :: DkMode -> Int -> Doc -> Doc
iterateSuc dkMode x s
  | x == 0 = s
  | x >  0 = parens $ pSucc dkMode <+> (iterateSuc dkMode (x - 1) s)

unary :: DkMode -> Int -> Doc
unary dkMode x = iterateSuc dkMode x $ pZero dkMode

data DkSort =
    DkSet Lvl
  | DkProp Lvl
  | DkSetOmega
  -- uncomputed successor sort (Axiom)
  | DkUniv DkSort
  -- uncomputed product sort (Rule)
  | DkPi DkSort DkSort
  | DkDefaultSort
  deriving (Show)

printSort :: Position -> DkModName -> DkMode -> DkCtx -> DkSort -> Doc
printSort pos mods dkMode boundCtx (DkSet lvl)     =
  paren pos $ pSet dkMode  <+> printLvl mods dkMode boundCtx lvl
printSort pos mods dkMode boundCtx (DkProp lvl)    =
  paren pos $ pProp dkMode <+> printLvl mods dkMode boundCtx lvl
printSort pos _ dkMode _ DkSetOmega    =
  pOmega dkMode
printSort pos mods dkMode boundCtx (DkUniv sort)    =
  paren pos $ pAxiom dkMode <+> printSort pos mods dkMode boundCtx sort
printSort pos mods dkMode boundCtx (DkPi domSort coDomSort)    =
  paren pos $
    pRule dkMode <+> printSort pos mods dkMode boundCtx domSort
    <+> printSort pos mods dkMode boundCtx coDomSort
printSort pos _ _ _    DkDefaultSort =
  text "DEFAULT_SORT"

data DkRule =
   DkRule
    { decoding :: Bool
    , context  :: DkCtx
    , headsymb :: DkName
    , patts    :: [DkPattern]
    , rhs      :: DkTerm
    }  deriving (Show)


printRule :: DkModName -> DkMode -> DkRule -> Doc
printRule mods dkMode
  (DkRule {context=ctx, headsymb=hdSymb, patts=patts, rhs=rhs}) =
  let varList = concat (map usedIndex patts) in
  let boundCtx = extractRealCtx varList ctx in    
  let lhs = prettyDk mods dkMode boundCtx hdSymb <+>
            hsep (map (printPattern Nested mods dkMode boundCtx) patts) in
  let printedRhs = printTerm Top mods dkMode boundCtx rhs in
  let printedCtx = 
        brackets (hsep (punctuate (char ',')
                        (map (printIdent dkMode []) (reverse boundCtx)))) in
  pRewRule dkMode printedCtx lhs printedRhs

-- takes a full ctx and indices of variables in the real ctx
-- returns the part of the full ctx whose indices are among the supplied ones
extractRealCtx :: [Int] -> DkCtx -> DkCtx
extractRealCtx used l =
  extractIndex 0 (sortUniq used) l
  where
    extractIndex _ []     _        = []
    extractIndex a (b:tl) (x:vars)
    -- if a == b, then this we put x on the list
      | a==b      = x:(extractIndex (a+1) tl vars)
    -- otherwise we ignore x and continue
      | otherwise = extractIndex (a+1) (b:tl) vars

usedIndex :: DkPattern -> [Int]
-- gets the debruijn indices of the free vars in a pattern of the lhs
-- all the indices <= 0 are the bound vars
usedIndex (DkVar _ i l)  = i:(concat (map usedIndex l))
usedIndex (DkFun f l)  = concat (map usedIndex l)
usedIndex (DkLambda _ p) = map (\n -> n-1) (usedIndex p)
usedIndex _              = []

data DkTerm =
  -- name of sort
    DkSort DkSort
  -- Product: Pi @3 : El @1 @4. El @2 @5
  | DkProd DkSort DkSort DkIdent DkTerm DkTerm
  -- Product: Pi @3 : El @1 @4. El @2 @5
  | DkProjProd DkSort DkSort DkIdent DkTerm DkTerm
  -- Lvl quantification: Forall (\@2. @1) (\@2. @3)
  | DkQuantifLevel DkSort DkIdent DkTerm
  -- name of constant
  | DkConst DkName
  -- Application: @1 @2
  | DkApp DkTerm DkTerm
  -- Abstraction: \ @1 : @2 . @3
  | DkLam DkIdent (Maybe (DkTerm,DkSort)) DkTerm
  -- Variable: @1
  | DkDB DkIdent Int
  -- Level expression
  | DkLevel Lvl
  -- Builtin
  | DkBuiltin DkBuiltin
   deriving (Show)

printTerm :: Position -> DkModName -> DkMode -> DkCtx -> DkTerm -> Doc
printTerm pos mods dkMode boundCtx (DkSort s)               =
  paren pos $
    pCode dkMode <+> printSort Nested mods dkMode boundCtx s
printTerm pos mods dkMode boundCtx (DkProd domSort coDomSort varName domTy coDomTy) =
  let trDomSort   = printSort Nested mods dkMode boundCtx domSort in    
  let trCoDomSort = printSort Nested mods dkMode boundCtx coDomSort in
  let trDomTy     = printTerm Nested mods dkMode boundCtx domTy in    
  let trCoDomTy   = printTerm Nested mods dkMode boundCtx coDomTy in
  let coDom       = parens (pAbs dkMode (printIdent dkMode boundCtx varName) Nothing
                            <+> trCoDomTy) in
  paren pos $ pPi dkMode <+> trDomSort <+> trCoDomSort <+> trDomTy <+> coDom
printTerm pos mods dkMode boundCtx
  (DkProjProd domSort coDomSort varName domTy coDomTy) =
  let trDomSort   = printSort Nested mods dkMode boundCtx domSort in    
  let trCoDomSort = printSort Nested mods dkMode boundCtx coDomSort in
  let trDomTy     = printTerm Nested mods dkMode boundCtx domTy in    
  let trCoDomTy   = printTerm Nested mods dkMode boundCtx coDomTy in
  let coDom       = parens (pAbs dkMode (printIdent dkMode boundCtx varName) Nothing <+>
                            trCoDomTy) in
  paren pos $ pProjPi dkMode <+> trDomSort <+> trCoDomSort <+> trDomTy <+> coDom

printTerm pos mods dkMode boundCtx (DkQuantifLevel sort varName coDom)   =
  let trSort     = printSort Top mods dkMode boundCtx sort in
  let trCoDom    = printTerm Top mods dkMode boundCtx coDom in    
  let trAbsSort  = parens $
                   pAbs dkMode (printIdent dkMode boundCtx varName) Nothing <+> trSort in
  let trAbsCoDom = parens $
                   pAbs dkMode (printIdent dkMode boundCtx varName) Nothing <+> trCoDom in
  paren pos $ pForall dkMode <+> trAbsSort <+> trAbsCoDom

printTerm pos mods dkMode boundCtx (DkConst name)        =
  prettyDk mods dkMode boundCtx name
printTerm pos mods dkMode boundCtx (DkApp t u)           =
  case t of
    DkApp (DkApp (DkConst n) s) ty | n == etaExpandSymb ->
      case u of
        DkApp (DkApp (DkApp (DkConst n2) s2) ty2) v | n2 == etaExpandSymb ->
          printTerm pos mods dkMode boundCtx $
          DkApp (DkApp (DkApp (DkConst n) s) ty) v
        otherwise -> defaultCase
    otherwise -> defaultCase
  where
    -- Beta-redices can be created by the expansion of copies.
    defaultCase =
      let tPos =
            case t of
              DkLam _ _ _-> Nested
              otherwise -> Top
      in
      paren pos $
        printTerm tPos mods dkMode boundCtx t <+>
        printTerm Nested mods dkMode boundCtx u

printTerm pos mods dkMode boundCtx (DkLam varName Nothing coDom)      =
  paren pos $
    pAbs dkMode (printIdent dkMode boundCtx varName) Nothing <+>
    printTerm Top mods dkMode boundCtx coDom

printTerm pos mods dkMode boundCtx (DkLam varName (Just (domTy, domSort)) coDom) =
  let trDomTy   = printTerm Nested mods dkMode boundCtx domTy in
  let trDomSort = printSort Nested mods dkMode boundCtx domSort in
  let trDom     = pEl dkMode <+> trDomSort <+> trDomTy in
  paren pos $
    pAbs dkMode (printIdent dkMode boundCtx varName) (Just trDom) <+>
    printTerm Top mods dkMode boundCtx coDom

printTerm pos mods dkMode boundCtx (DkDB n _)               =
  printIdent dkMode boundCtx n
printTerm pos mods dkMode boundCtx (DkLevel l)              =
  printLvl mods dkMode boundCtx l
printTerm pos mods dkMode boundCtx (DkBuiltin b)            =
  printBuiltin pos mods dkMode boundCtx b

data DkBuiltin =
    DkNat    Int
  | DkChar   Char
  | DkString String
   deriving (Show)

printBuiltin :: Position -> DkModName -> 
                DkMode -> DkCtx -> DkBuiltin -> Doc
printBuiltin pos mods dkMode boundCtx (DkNat i) =
  printTerm pos mods dkMode boundCtx (fromBuiltinNat i)
printBuiltin pos mods dkMode boundCtx (DkChar c) =
  printTerm pos mods dkMode boundCtx (fromBuiltinChar c)
printBuiltin pos mods dkMode boundCtx (DkString s) =
  printTerm pos mods dkMode boundCtx (fromBuiltinString s)

fromBuiltinNat :: Int -> DkTerm
fromBuiltinNat i =
  let zero = DkConst $ DkQualified ["Agda", "Builtin", "Nat"] ["Nat"] "zero" in
  let suc = DkConst $ DkQualified ["Agda", "Builtin", "Nat"] ["Nat"] "suc" in
  iterate (\x -> DkApp suc x) zero !! i

fromBuiltinChar :: Char -> DkTerm
fromBuiltinChar c =
  let converter = DkConst $ DkQualified ["Agda", "Builtin", "Char"] [] "primNatToChar" in
  DkApp converter (fromBuiltinNat (fromEnum c))

fromBuiltinString :: String -> DkTerm
fromBuiltinString s =
  let converter = DkConst $ DkQualified ["Agda", "Builtin", "String"] [] "primStringFromList" in
  DkApp converter (fromBuiltinListOfChar s)

fromBuiltinListOfChar []     =
  let nil = DkConst $ DkQualified ["Agda", "Builtin", "List"] ["List"] "[]" in
  let lvl0 = DkConst $ DkQualified ["univ"] [] "0" in
  let char_type = DkConst $ DkQualified ["Agda", "Builtin", "Char"] [] "Char" in
  DkApp (DkApp nil lvl0) char_type
fromBuiltinListOfChar (c:tl) =
  let cons = DkConst $ DkQualified ["Agda", "Builtin", "List"] ["List"] "_∷_" in
  let lvl0 = DkConst $ DkQualified ["univ"] [] "0" in
  let char_type = DkConst $ DkQualified ["Agda", "Builtin", "Char"] [] "Char" in
  DkApp (DkApp (DkApp (DkApp cons lvl0) char_type) (fromBuiltinChar c)) (fromBuiltinListOfChar tl)

paren :: Position -> Doc -> Doc
paren pos =
  case pos of
    Top    -> id
    Nested -> parens

data DkPattern =
    DkVar DkIdent Int [DkPattern]
  | DkFun DkName [DkPattern]
  | DkLambda DkIdent DkPattern
  | DkPattBuiltin DkTerm
  | DkGuarded DkTerm
  | DkJoker
   deriving (Show)

printPattern ::   Position -> DkModName -> DkMode -> DkCtx -> DkPattern -> Doc
printPattern pos mods dkMode boundCtx (DkVar n _ [])  =
  printIdent dkMode boundCtx n
printPattern pos mods dkMode boundCtx (DkVar n _ l)  =
  paren pos $
    printIdent dkMode boundCtx n <+> hsep (map (printPattern Nested mods dkMode boundCtx) l)
printPattern pos mods dkMode boundCtx (DkFun n [])    =
  prettyDk mods dkMode boundCtx n
printPattern pos mods dkMode boundCtx (DkFun n l)    =
  paren pos $
    prettyDk mods dkMode boundCtx n <+>
    hsep (map (printPattern Nested mods dkMode boundCtx) l)
printPattern pos mods dkMode boundCtx (DkLambda n t) =
  paren pos $
    pAbs dkMode (printIdent dkMode boundCtx n) Nothing <+>
    printPattern Top mods dkMode boundCtx t
printPattern pos mods dkMode boundCtx (DkPattBuiltin t) =
  printTerm pos mods dkMode boundCtx t
-- We do not guard variables, since non-linear rules are more efficient.
printPattern pos mods dkMode boundCtx (DkGuarded (DkDB n _)) =
  printIdent dkMode boundCtx n
printPattern pos mods dkMode boundCtx (DkGuarded t) =
  case dkMode of
    DkMode -> braces (printTerm Top mods dkMode boundCtx t)
    LpMode -> text "_" -- no brace patterns in lambdapi
printPattern pos mods dkMode boundCtx DkJoker =
  char '_'

type DkCtx = [DkIdent]


data DkSpecial =
    TermSymb
  | EtaExpandSymb
  deriving (Eq, Show)

data DkName =
    -- local identifier
    DkLocal DkIdent
    -- qualified identifier
  | DkQualified DkModName DkModName DkIdent
  | DkSpecial DkSpecial
  deriving (Eq, Show)

instance PrettyDk DkName where
  prettyDk mods dkMode boundCtx (DkSpecial TermSymb)       = pEl dkMode
  prettyDk mods dkMode boundCtx (DkSpecial EtaExpandSymb)  = pEta dkMode  
  prettyDk mods dkMode boundCtx (DkLocal n)            = printIdent dkMode boundCtx n
  prettyDk mods dkMode boundCtx (DkQualified qualif pseudo n) =
    let modName =
          if mods == qualif
          then empty
          else hcat (punctuate (text "__") (map (text . dropAll) qualif)) <> char '.'
    in
    let symName = printIdent dkMode boundCtx $ (concat (map (++ "__") pseudo)) ++ n in
    modName <> symName

printIdent :: DkMode -> DkCtx -> DkIdent -> Doc
printIdent dkMode boundCtx name =
  let newName = map (\c -> if c == '.' then '\'' else c) name in
  if (dkMode == LpMode) && (elem name boundCtx)
  then text $ "$" ++ (encapsulate newName)
  else text $ (encapsulate newName)
  
data IsStatic = Static | Defin | TypeConstr deriving (Show)

keywords = ["Type", "def", "thm", "injective", "defac", "defacu", "symbol", "constant",
            "TYPE", "rule", "with", "builtin", "notation", "infix", "right", "left",
            "associative", "commutative", "compute", "assert"]

encapsulate :: String -> String
encapsulate l =
  if all (`elem` ['a'..'z']++['A'..'Z']++['0'..'9']++['_']) l && not (elem l keywords)
  then l
  else "{|"++l++"|}"

dropAll :: String -> String
dropAll []    = []
dropAll (h:t) =
  if elem h (['a'..'z']++['A'..'Z']++['0'..'9']++['_'])
  then h:(dropAll t)
  else dropAll t

data Position = Nested | Top  deriving (Show)

termOfPattern :: DkPattern -> DkTerm
termOfPattern (DkVar x i l)  = multiApp (DkDB x i) (map termOfPattern l)
termOfPattern (DkFun f l)    = multiApp (DkConst f) (map termOfPattern l)
termOfPattern (DkLambda x p) = DkLam x Nothing (termOfPattern p)
termOfPattern (DkPattBuiltin t)  = t
termOfPattern (DkGuarded t)  = t

multiApp :: DkTerm -> [DkTerm] -> DkTerm
multiApp t []     = t
multiApp t (x:tl) = multiApp (DkApp t x) tl

type DkDocs = (Doc, Doc, Doc)

toDkDocs ::  DkModName -> DkMode -> DkDefinition -> DkDocs
toDkDocs mods dkMode def =
  case staticity def of
    TypeConstr -> 
      ( printDecl mods dkMode def <> hcat (printRules mods decoding dkMode def)
      , empty
      , (hcat $ printRules mods (not . decoding) dkMode def) <+> text "\n")
    _ ->
      ( empty
      , printDecl mods dkMode def
      , (hcat $ printRules mods (\x -> True) dkMode def) <+> text "\n")

------- Printing funcitons -------

pEl :: DkMode -> Doc
pEl DkMode = text "Agda.Term"
pEl LpMode = text "El"

pCode :: DkMode -> Doc
pCode DkMode = text "Agda.code"
pCode LpMode = text "⋄"

pPi :: DkMode -> Doc
pPi DkMode = text "Agda.prod"
pPi LpMode = text "⇝"

pProjPi :: DkMode -> Doc
pProjPi DkMode = text "Agda.proj_prod"
pProjPi LpMode = text "⇝proj"

pForall :: DkMode -> Doc
pForall DkMode = text "Agda.qLevel"
pForall LpMode = text "∀"

pAxiom :: DkMode -> Doc
pAxiom DkMode = text "Agda.axiom"
pAxiom LpMode = text "□"

pAbs :: DkMode -> Doc -> Maybe Doc -> Doc
pAbs DkMode var mayAbsType = var <+>
                             maybe empty (\x -> text ":" <+> x) mayAbsType <+>
                             text "=>"
pAbs LpMode var mayAbsType = text "λ" <+>
                             var <+>
                             maybe empty (\x -> text ":" <+> x) mayAbsType <>
                             text ","

pProd :: DkMode -> Doc -> Maybe Doc -> Doc
pProd DkMode var mayCoDomType = parens (var <+>
                                maybe empty (\x -> text ":" <+> x) mayCoDomType) <+>
                                text "->"
pProd LpMode var mayCoDomType = text "Π" <+>
                                var <+>
                                maybe empty (\x -> text ":" <+> x) mayCoDomType <>
                                text ","

pRewrites :: DkMode -> Doc
pRewrites DkMode = text "-->"
pRewrites LpMode = text "↪"

pEndDef :: DkMode -> Doc
pEndDef DkMode = text ".\n"
pEndDef LpMode = text ";\n"

pMax :: DkMode -> Doc
pMax DkMode = text "univ.max"
pMax LpMode = text "⊔"

pRule :: DkMode -> Doc
pRule DkMode = text "Agda.rule"
pRule LpMode = text "∨"

pLvl :: DkMode -> Doc
pLvl DkMode = text "univ.Lvl"
pLvl LpMode = text "L"

pZero :: DkMode -> Doc
pZero DkMode = text "univ.0"
pZero LpMode = text "o"

pSucc :: DkMode -> Doc
pSucc DkMode = text "univ.s"
pSucc LpMode = text "s"

pSet :: DkMode -> Doc
pSet DkMode = text "Agda.set"
pSet LpMode = text "set"

pProp :: DkMode -> Doc
pProp DkMode = text "Agda.prop"
pProp LpMode = text "prop"

pOmega :: DkMode -> Doc
pOmega DkMode = text "Agda.sortOmega"
pOmega LpMode = text "setω"

pEta :: DkMode -> Doc
pEta DkMode = text "Agda.etaExpand"
pEta LpMode = text "η"

pSymb :: DkMode -> Doc
pSymb DkMode = text "def "
pSymb LpMode = text "symbol "

pCons :: DkMode -> Doc
pCons DkMode = empty
pCons LpMode = text "constant symbol "

pRewRule :: DkMode -> Doc -> Doc -> Doc -> Doc
pRewRule DkMode ruleCtx lhs rhs = ruleCtx <+>
                                  lhs <+>
                                  text "-->" <+>
                                  rhs <>
                                  text ".\n"
pRewRule LpMode ruleCtx lhs rhs = text "rule" <+>
                                  lhs <+>
                                  text "↪" <+>
                                  rhs <>
                                  text ";\n"

pType :: DkMode -> Doc
pType DkMode = text "Type"
pType LpMode = text "TYPE"
