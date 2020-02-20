module Agda2Dk.DkSyntax where

import Data.Word
import Data.List
import Data.List.Unique
import Data.Int
import Data.Char

import Text.PrettyPrint

import Agda.Syntax.Internal
import qualified Agda.Syntax.Concrete.Name as CN
import Agda.Utils.Impossible

class PrettyDk a where
  prettyDk :: DkModName -> a -> Doc

data DkDefinition =
   DkDefinition
    { name      :: DkName
    , staticity :: IsStatic
    , typ       :: DkTerm
    , kind      :: DkSort
    , rules     :: [DkRule]
    }

etaExpandSymb :: DkName
etaExpandSymb = DkQualified ["Agda"] [] "etaExpand"

printDecl :: DkModName -> DkDefinition -> Doc
printDecl mods (DkDefinition {name=n, staticity=b, typ=t, kind=k}) =
  let special =
        case n of
          DkQualified ["Agda", "Primitive"] [] "Level" ->
            text "[] Agda.Term _ Level --> univ.Lvl.\n"
          DkQualified ["Agda", "Primitive"] [] "lzero" ->
            text "[] lzero --> univ.0.\n"
          DkQualified ["Agda", "Primitive"] [] "lsuc"  ->
            text "[] lsuc --> univ.s.\n"
          DkQualified ["Agda", "Primitive"] [] "_⊔_"   ->
            text "[] {|_⊔_|} --> univ.max.\n"
          otherwise                                    -> empty
  in
  let kw =
        case b of
          Defin      -> text "def "
          TypeConstr -> printDecodedDecl mods n t
          Static     -> empty
  in
  let typDecl = printSort Nested mods k <+> printTerm Nested mods t in
  kw <> prettyDk mods n <+> text ": Agda.Term" <+> typDecl <> text ".\n" <> special

printDecodedDecl :: DkModName -> DkName -> DkTerm -> Doc
printDecodedDecl mods (DkQualified _ pseudo id) t =
  let ident = "TYPE__" ++ (concat (map (++ "__") pseudo)) ++ id in
  printIdent ident <+> char ':' <+> decodedType mods t <> text ".\n"

decodedType :: DkModName -> DkTerm -> Doc
decodedType mods (DkSort _)              = text "Type"
decodedType mods (DkProd s1 _ id t u)    =
  let domDecl = printSort Nested mods s1 <+> printTerm Nested mods t in
  parens (printIdent id <+> text ": Agda.Term" <+> domDecl) <+> text "->" <+> decodedType mods u
decodedType mods (DkQuantifLevel _ id t) =
  parens (printIdent id <+> text ": univ.Lvl") <+> text "->" <+> decodedType mods t

printRules :: DkModName -> DkDefinition -> (DkRule -> Bool) -> [Doc]
printRules mods (DkDefinition {rules=l}) f = map (prettyDk mods) (filter f l)

type Lvl = [PreLvl]

printLvl :: DkModName -> Lvl -> Doc
printLvl mods l =
  printPreLvlList mods l

printPreLvlList mods []     = text "univ.0"
printPreLvlList mods (a:[]) = prettyDk mods a
printPreLvlList mods (a:tl) =
  parens $ text "univ.max" <+> prettyDk mods a <+> printPreLvlList mods tl

data PreLvl =
    LvlInt Int
  | LvlPlus Int DkTerm

instance PrettyDk PreLvl where
 prettyDk mods (LvlInt i)    =
   unary i
 prettyDk mods (LvlPlus i t) =
   applyN i (parens . (text "univ.s" <+>)) (printTerm Nested mods t)
  where applyN i f x = iterate f x !! i

unary :: Int -> Doc
unary x
  | x==0 = text "univ.0"
  | x>0  = parens $ (text "univ.s")<+> (unary (x-1))

data DkSort =
    DkSet Lvl
  | DkProp Lvl
  | DkSetOmega
  | DkUniv DkSort
  | DkPi DkSort DkSort
  | DkDefaultSort

printSort :: Position -> DkModName -> DkSort -> Doc
printSort pos mods (DkSet i)     =
  paren pos $ text "Agda.set"  <+> printLvl mods i
printSort pos mods (DkProp i)    =
  paren pos $ text "Agda.prop" <+> printLvl mods i
printSort pos _    DkSetOmega    =
  text "Agda.sortOmega"
printSort pos mods (DkUniv s)    =
  paren pos $ text "Agda.axiom" <+> printSort pos mods s
printSort pos mods (DkPi s t)    =
  paren pos $
    text "Agda.rule" <+> printSort pos mods s <+> printSort pos mods t
printSort pos _    DkDefaultSort =
  text "DEFAULT_SORT"

data DkRule =
   DkRule
    { decoding :: Bool
    , context  :: DkCtx
    , headsymb :: DkName
    , patts    :: [DkPattern]
    , rhs      :: DkTerm
    }

instance PrettyDk DkRule where
  prettyDk mods (DkRule {context=c, headsymb=hd, patts=patts, rhs=rhs}) =
    let varList = concat (map usedIndex patts) in
    let lhs = prettyDk mods hd <+> hsep (map (printPattern Nested mods) patts) in
    printContext varList c <+> lhs <+> text "-->" <+> printTerm Top mods rhs <> text ".\n"

usedIndex :: DkPattern -> [Int]
usedIndex (DkVar _ i l)  = i:(concat (map usedIndex l))
usedIndex (DkFun f l)  = concat (map usedIndex l)
usedIndex (DkLambda _ p) = map (\n -> n-1) (usedIndex p)
usedIndex _              = []

data DkTerm =
    DkSort DkSort
  | DkProd DkSort DkSort DkIdent DkTerm DkTerm
  | DkProjProd DkSort DkSort DkIdent DkTerm DkTerm
  | DkQuantifLevel DkSort DkIdent DkTerm
  | DkConst DkName
  | DkApp DkTerm DkTerm
  | DkLam DkIdent (Maybe (DkTerm,DkSort)) DkTerm
  | DkDB DkIdent Int
  | DkLevel Lvl
  | DkBuiltin DkBuiltin

printTerm :: Position -> DkModName -> DkTerm -> Doc
printTerm pos mods (DkSort s)               =
  paren pos $
    text "Agda.code" <+> printSort Nested mods s
printTerm pos mods (DkProd s1 s2 n t u)     =
  let sorts = printSort Nested mods s1 <+> printSort Nested mods s2 in
  let domain =  printTerm Nested mods t in
  let codomain = parens (printIdent n <+> text "=>" <+> printTerm Top mods u) in
  paren pos $
    text "Agda.prod" <+> sorts <+> domain <+> codomain
printTerm pos mods (DkProjProd s1 s2 n t u)     =
  let sorts = printSort Nested mods s1 <+> printSort Nested mods s2 in
  let domain =  printTerm Nested mods t in
  let codomain = parens (printIdent n <+> text "=>" <+> printTerm Top mods u) in
  paren pos $
    text "Agda.proj_prod" <+> sorts <+> domain <+> codomain
printTerm pos mods (DkQuantifLevel s n u)   =
  let sorts = parens (printIdent n <+> text "=>" <+> printSort Top mods s) in
  let codomain = parens (printIdent n <+> text "=>" <+> printTerm Top mods u) in
  paren pos $
    text "Agda.qLevel" <+> sorts <+> codomain
printTerm pos mods  (DkConst f)             =
  prettyDk mods f
printTerm pos mods (DkApp t u)              =
  case t of
    DkApp (DkApp (DkConst n) s) ty | n == etaExpandSymb ->
      case u of
        DkApp (DkApp (DkApp (DkConst n2) s2) ty2) v | n2 == etaExpandSymb ->
          printTerm pos mods $ DkApp (DkApp (DkApp (DkConst n) s) ty) v
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
        printTerm tPos mods t <+> printTerm Nested mods u
printTerm pos mods (DkLam n Nothing t)      =
  paren pos $
    printIdent n <+> text "=>" <+> printTerm Top mods t
printTerm pos mods (DkLam n (Just (a,s)) t) =
  let typCode = printTerm Nested mods a in
  let annot = text "Agda.Term" <+> printSort Nested mods s <+> typCode in
  paren pos $
    printIdent n <+> char ':' <+> annot <+> text "=>" <+> printTerm Top mods t
printTerm pos mods (DkDB n _)               =
  printIdent n
printTerm pos mods (DkLevel l)              =
  printPreLvlList mods l
printTerm pos mods (DkBuiltin b)            =
  printBuiltin pos mods b

data DkBuiltin =
    DkNat    Int
  | DkChar   Char
  | DkString String

printBuiltin :: Position -> DkModName -> DkBuiltin -> Doc
printBuiltin pos mods (DkNat i) =
  printTerm pos mods (fromBuiltinNat i)
printBuiltin pos mods (DkChar c) =
  printTerm pos mods (fromBuiltinChar c)
printBuiltin pos mods (DkString s) =
  printTerm pos mods (fromBuiltinString s)

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

printPattern ::   Position -> DkModName -> DkPattern -> Doc
printPattern pos mods (DkVar n _ [])  =
  printIdent n
printPattern pos mods (DkVar n _ l)  =
  paren pos $
    printIdent n <+> hsep (map (printPattern Nested mods) l)
printPattern pos mods (DkFun n [])    =
  prettyDk mods n
printPattern pos mods (DkFun n l)    =
  paren pos $
    prettyDk mods n <+> hsep (map (printPattern Nested mods) l)
printPattern pos mods (DkLambda n t) =
  paren pos $
    printIdent n <+> text "=>" <+> printPattern Top mods t
printPattern pos mods (DkPattBuiltin t) =
  printTerm pos mods t
-- We do not guard variables, since non-linear rules are more efficient.
printPattern pos mods (DkGuarded (DkDB n _)) =
  printIdent n
printPattern pos mods (DkGuarded t) =
  braces (printTerm Top mods t)
printPattern pos mods DkJoker =
  char '_'

type DkCtx = [DkIdent]

printContext :: [Int] -> DkCtx -> Doc
printContext used l =
  let ll = extractIndex 0 (sortUniq used) l in
  brackets (hsep (punctuate (char ',') (map printIdent (reverse ll))))
  where
    extractIndex _ []     _        = []
    extractIndex a (b:tl) (x:vars)
      | a==b      = x:(extractIndex (a+1) tl vars)
      | otherwise = extractIndex (a+1) (b:tl) vars

data DkName =
    DkLocal DkIdent
  | DkQualified DkModName DkModName DkIdent
  deriving (Eq, Show)

instance PrettyDk DkName where
  prettyDk mods (DkLocal n)            = printIdent n
  prettyDk mods (DkQualified qualif pseudo n) =
    let modName =
          if mods == qualif
          then empty
          else hcat (punctuate (text "__") (map (text . dropAll) qualif)) <> char '.'
    in
    let symName = printIdent $ (concat (map (++ "__") pseudo)) ++ n in
    modName <> symName

type DkModName = [String]

type DkIdent = String

printIdent n=
    text $ encapsulate n

data IsStatic = Static | Defin | TypeConstr

keywords = ["Type", "def", "thm", "injective", "defac", "defacu"]

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

data Position = Nested | Top

termOfPattern :: DkPattern -> DkTerm
termOfPattern (DkVar x i l)  = multiApp (DkDB x i) (map termOfPattern l)
termOfPattern (DkFun f l)    = multiApp (DkConst f) (map termOfPattern l)
termOfPattern (DkLambda x p) = DkLam x Nothing (termOfPattern p)
termOfPattern (DkPattBuiltin t)  = t
termOfPattern (DkGuarded t)  = t

multiApp :: DkTerm -> [DkTerm] -> DkTerm
multiApp t []     = t
multiApp t (x:tl) = multiApp (DkApp t x) tl
