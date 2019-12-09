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

printDecl :: DkModName -> DkDefinition -> Doc
printDecl mods (DkDefinition {name=n, staticity=b, typ=t, kind=k}) =
  let special =
        case n of
          DkQualified ["Agda", "Primitive"] [] "Level" ->
            text "[] naiveAgda.Term _ Level --> universeLevel.Lvl.\n"
          DkQualified ["Agda", "Primitive"] [] "lzero" ->
            text "[] lzero --> universeLevel.0.\n"
          DkQualified ["Agda", "Primitive"] [] "lsuc"  ->
            text "[] lsuc --> universeLevel.s.\n"
          DkQualified ["Agda", "Primitive"] [] "_⊔_"  ->
            text "[] {|_⊔_|} --> universeLevel.max.\n"
          otherwise                                            -> empty
  in
  let kw =
        case b of
          Defin      -> text "def "
          TypeConstr -> printDecodedDecl mods n t
          Static     -> empty
  in
  let typDecl = printSort Nested mods k <+> printTerm Nested mods t in
  kw <> prettyDk mods n <+> text ": naiveAgda.Term" <+> typDecl <> text ".\n" <> special

printDecodedDecl :: DkModName -> DkName -> DkTerm -> Doc
printDecodedDecl mods (DkQualified _ pseudo id) t =
  let ident = "TYPE__" ++ (concat (map (++ "__") pseudo)) ++ id in
  printIdent ident <+> char ':' <+> decodedType mods t <> text ".\n"

decodedType :: DkModName -> DkTerm -> Doc
decodedType mods (DkSort _)              = text "Type"
decodedType mods (DkProd s1 _ id t u)    =
  let domDecl = printSort Nested mods s1 <+> printTerm Nested mods t in
  parens (printIdent id <+> text ": naiveAgda.Term" <+> domDecl) <+> text "->" <+> decodedType mods u
decodedType mods (DkQuantifLevel _ id t) =
  parens (printIdent id <+> text ": universeLevel.Lvl") <+> text "->" <+> decodedType mods t

printRules :: DkModName -> DkDefinition -> [Doc]
printRules mods (DkDefinition {rules=l}) = map (prettyDk mods) l

type Lvl = [PreLvl]

printLvl :: DkModName -> Lvl -> Doc
printLvl mods l =
  printPreLvlList mods l

printPreLvlList mods []     = text "universeLevel.0"
printPreLvlList mods (a:[]) = prettyDk mods a
printPreLvlList mods (a:tl) =
  parens $ text "universeLevel.max" <+> prettyDk mods a <+> printPreLvlList mods tl

data PreLvl =
    LvlInt Int
  | LvlPlus Int DkTerm

instance PrettyDk PreLvl where
 prettyDk mods (LvlInt i)    =
   unary i
 prettyDk mods (LvlPlus i t) =
   applyN i (parens . (text "universeLevel.s" <+>)) (printTerm Nested mods t)
  where applyN i f x = iterate f x !! i

unary :: Int -> Doc
unary x
  | x==0 = text "universeLevel.0"
  | x>0  = parens $ (text "universeLevel.s")<+> (unary (x-1))

data DkSort =
    DkSet Lvl
  | DkProp Lvl
  | DkSetOmega
  | DkUniv DkSort
  | DkPi DkSort DkSort
  | DkDefaultSort

printSort :: Position -> DkModName -> DkSort -> Doc
printSort pos mods (DkSet i)     =
  paren pos $ text "naiveAgda.set"  <+> printLvl mods i
printSort pos mods (DkProp i)    =
  paren pos $ text "naiveAgda.prop" <+> printLvl mods i
printSort pos _    DkSetOmega    =
  text "naiveAgda.setOmega"
printSort pos mods (DkUniv s)    =
  paren pos $ text "naiveAgda.succ" <+> printSort pos mods s
printSort pos mods (DkPi s t)    =
  paren pos $
    text "naiveAgda.rule" <+> printSort pos mods s <+> printSort pos mods t
printSort pos _    DkDefaultSort =
  text "DEFAULT_SORT"

data DkRule =
   DkRule
    { context   :: DkCtx
    , headsymb  :: DkName
    , patts     :: [DkPattern]
    , rhs       :: DkTerm
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
  | DkQuantifLevel DkSort DkIdent DkTerm
  | DkConst DkName
  | DkApp DkTerm DkTerm
  | DkLam DkIdent (Maybe (DkTerm,DkSort)) DkTerm
  | DkDB DkIdent Int
  | DkLevel Lvl

printTerm :: Position -> DkModName -> DkTerm -> Doc
printTerm pos mods (DkSort s)               =
  paren pos $
    text "naiveAgda.univ" <+> printSort Nested mods s
printTerm pos mods (DkProd s1 s2 n t u)     =
  let sorts = printSort Nested mods s1 <+> printSort Nested mods s2 in
  let domain =  printTerm Nested mods t in
  let codomain = parens (printIdent n <+> text "=>" <+> printTerm Top mods u) in
  paren pos $
    text "naiveAgda.prod" <+> sorts <+> domain <+> codomain
printTerm pos mods (DkQuantifLevel s n u)   =
  let sorts = parens (printIdent n <+> text "=>" <+> printSort Top mods s) in
  let codomain = parens (printIdent n <+> text "=>" <+> printTerm Top mods u) in
  paren pos $
    text "naiveAgda.qLevel" <+> sorts <+> codomain
printTerm pos mods  (DkConst f)             =
  prettyDk mods f
printTerm pos mods (DkApp t u)              =
  paren pos $
    printTerm Top mods t <+> printTerm Nested mods u
printTerm pos mods (DkLam n Nothing t)      =
  paren pos $
    printIdent n <+> text "=>" <+> printTerm Top mods t
printTerm pos mods (DkLam n (Just (a,s)) t) =
  let typCode = printTerm Nested mods a in
  let annot = text "naiveAgda.Term" <+> printSort Nested mods s <+> typCode in
  paren pos $
    printIdent n <+> char ':' <+> annot <+> text "=>" <+> printTerm Top mods t
printTerm pos mods (DkDB n _)               =
  printIdent n
printTerm pos mods (DkLevel l)              =
  printPreLvlList mods l

paren :: Position -> Doc -> Doc
paren pos =
  case pos of
    Top    -> id
    Nested -> parens

data DkPattern =
    DkVar DkIdent Int [DkPattern]
  | DkFun DkName [DkPattern]
  | DkLambda DkIdent DkPattern
  | DkBuiltin DkTerm
  | DkBrackets DkTerm
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
printPattern pos mods (DkBuiltin t) =
  printTerm pos mods t
printPattern pos mods (DkBrackets t) =
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
          else hcat (punctuate (text "__") (map text qualif)) <> char '.'
    in
    let symName = printIdent $ (concat (map (++ "__") pseudo)) ++ n in
    modName <> symName

type DkModName = [String]

type DkIdent = String

printIdent n=
    text $ encapsulate n

data IsStatic = Static | Defin | TypeConstr

keywords = ["Type", "def", "thm"]

encapsulate :: String -> String
encapsulate l =
  if all (`elem` ['a'..'z']++['A'..'Z']++['0'..'9']++['_']) l && not (elem l keywords)
  then l
  else "{|"++l++"|}"

data Position = Nested | Top
