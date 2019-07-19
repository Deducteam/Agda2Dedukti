module Agda2Dk.DkSyntax where

import Data.Word
import Data.List
import Data.List.Unique
import Data.Int

import Text.PrettyPrint

import qualified Agda.Syntax.Concrete.Name as CN

import Agda2Dk.ConvUnicode

class PrettyDk a where
  prettyDk :: DkModName -> a -> Doc

data DkDefinition =
   DkDefinition
    { name      :: DkName
    , mut       :: Int32
    , staticity :: IsStatic
    , typ       :: DkTerm
    , kind      :: DkSort
    , rules     :: [DkRule]
    }

printDecl :: DkModName -> DkDefinition -> Doc
printDecl mods (DkDefinition {name=n, staticity=b, typ=t, kind=k}) =
  let special =
        case n of
          DkQualified ["Agda", "Primitive"] (Nothing, "Level") ->
            text "[] naiveAgda.Term _ Level --> naiveAgda.Nat.\n"
          DkQualified ["Agda", "Primitive"] (Nothing, "lzero") ->
            text "[] lzero --> naiveAgda.0.\n"
          DkQualified ["Agda", "Primitive"] (Nothing, "lsuc")  ->
            text "[] lsuc --> naiveAgda.s.\n"
          DkQualified ["Agda", "Primitive"] (Nothing, "_⊔_")  ->
            text "[] _$\\sqcup$_ --> naiveAgda.max.\n"
          otherwise                                            -> empty
  in
  let kw =
        case b of
          Defin      -> text "def "
          TypeConstr -> printDecodedDecl mods n t
          Static     -> empty
  in
  let typDecl = parens (prettyDk mods k) <+> parens (prettyDk mods t) in
  kw <> prettyDk mods n <+> text ": naiveAgda.Term" <+> typDecl <> text ".\n" <> special

printDecodedDecl :: DkModName -> DkName -> DkTerm -> Doc
printDecodedDecl mods (DkQualified _ id) t =
  text "TYPE__" <> printIdent id <+> char ':' <+> decodedType mods t <> text ".\n"

decodedType :: DkModName -> DkTerm -> Doc
decodedType mods (DkSort _)              = text "Type"
decodedType mods (DkProd s1 _ id t u)    =
  let domDecl = parens (prettyDk mods s1) <+> parens (prettyDk mods t) in
  parens (printIdent id <+> text ": naiveAgda.Term" <+> domDecl) <+> text "->" <+> decodedType mods u
decodedType mods (DkQuantifLevel _ id t) =
  parens (printIdent id <+> text ": naiveAgda.Nat") <+> text "->" <+> decodedType mods t

printRules :: DkModName -> DkDefinition -> [Doc]
printRules mods (DkDefinition {rules=l}) = map (prettyDk mods) l

data Lvl =
    LvlInt Int
  | LvlTerm DkTerm
  | LvlMax Lvl Lvl
  | LvlPlus Lvl Lvl

instance PrettyDk Lvl where
 prettyDk mods (LvlInt i)    = unary i
 prettyDk mods (LvlTerm t)   = prettyDk mods t
 prettyDk mods (LvlMax a b)  =
   text "naiveAgda.max" <+> parens (prettyDk mods a) <+> parens (prettyDk mods b)
 prettyDk mods (LvlPlus a b) =
   text "naiveAgda.plus" <+> parens (prettyDk mods a) <+> parens (prettyDk mods b)

unary :: Int -> Doc
unary x
  | x==0 = text "naiveAgda.0"
  | x>0  = parens $ (text "naiveAgda.s")<+> (unary (x-1))

data DkSort =
    DkSet Lvl
  | DkProp Lvl
  | DkSetOmega
  | DkUniv DkSort
  | DkPi DkSort DkSort
  | DkDefaultSort

instance PrettyDk DkSort where
  prettyDk mods (DkSet i)     = text "naiveAgda.set"  <+> parens (prettyDk mods i)
  prettyDk mods (DkProp i)    = text "naiveAgda.prop" <+> parens (prettyDk mods i)
  prettyDk _    DkSetOmega    = text "naiveAgda.setOmega"
  prettyDk mods (DkUniv s)    = text "naiveAgda.succ" <+> parens (prettyDk mods s)
  prettyDk mods (DkPi s t)    = text "naiveAgda.rule" <+> parens (prettyDk mods s) <+> parens (prettyDk mods t)
  prettyDk _    DkDefaultSort = text "DEFAULT_SORT"

data DkRule =
   DkRule
    { context   :: DkCtx
    , headsymb  :: DkName
    , implicits :: Int
    , patts     :: [DkPattern]
    , rhs       :: DkTerm
    }

instance PrettyDk DkRule where
  prettyDk mods (DkRule {context=c, headsymb=hd, patts=l, rhs=t, implicits=imp}) =
    let varList = concat (map usedIndex l) in
    let lhs = prettyDk mods hd <+> text (concat (replicate imp "_ ")) <> hsep (map (parens . (prettyDk mods)) l) in
    printContext varList c <+> lhs <+> text "-->" <+> prettyDk mods t <> text ".\n"

usedIndex :: DkPattern -> [Int]
usedIndex (DkVar _ i l)  = i:(concat (map usedIndex l))
usedIndex (DkFun _ _ l)    = concat (map usedIndex l)
usedIndex (DkLambda _ p) = map (\n -> n-1) (usedIndex p)
usedIndex (DkBrackets _) = []

data DkTerm =
    DkSort DkSort
  | DkProd DkSort DkSort DkIdent DkTerm DkTerm
  | DkQuantifLevel DkSort DkIdent DkTerm
  | DkConst DkName
  | DkApp DkTerm DkTerm
  | DkLam DkIdent (Maybe (DkTerm,DkSort)) DkTerm
  | DkDB DkIdent Int
  | DkLevel Lvl

instance PrettyDk DkTerm where
  prettyDk mods (DkSort s)               =
    text "naiveAgda.univ"<+>parens (prettyDk mods s)
  prettyDk mods (DkProd s1 s2 n t u)     =
    let sorts = parens (prettyDk mods s1) <+> parens (prettyDk mods s2) in
    let domain =  parens (prettyDk mods t) in
    let codomain = parens (printIdent n <+> text "=>" <+> prettyDk mods u) in
    text "naiveAgda.prod" <+> sorts <+> domain <+> codomain
  prettyDk mods (DkQuantifLevel s n u)   =
    let sorts = parens (printIdent n <+> text "=>" <+> prettyDk mods s) in
    let codomain = parens (printIdent n <+> text "=>" <+> prettyDk mods u) in
    text "naiveAgda.qLevel" <+> sorts <+> codomain
  prettyDk mods  (DkConst f)             =
    prettyDk mods f
  prettyDk mods (DkApp t u)            =
    parens (prettyDk mods t) <+> parens (prettyDk mods u)
  prettyDk mods (DkLam n Nothing t)      =
    printIdent n <+> text "=>" <+> prettyDk mods t
  prettyDk mods (DkLam n (Just (a,s)) t) =
    let typCode = parens (prettyDk mods a) in
    let annot = text "naiveAgda.Term" <+> parens (prettyDk mods s) <+> typCode in
    printIdent n <+> char ':' <+> annot <+> text "=>" <+> prettyDk mods t
  prettyDk mods (DkDB n _)               =
    printIdent n
  prettyDk mods (DkLevel l)              =
    prettyDk mods l

data DkPattern =
    DkVar DkIdent Int [DkPattern]
  | DkFun DkName Int [DkPattern]
  | DkLambda DkIdent DkPattern
  | DkBrackets DkTerm

instance PrettyDk DkPattern where
  prettyDk mods (DkVar n _ l)  =
    printIdent n <+> hsep (map (parens . (prettyDk mods)) l)
  prettyDk mods (DkFun n params l)    =
    prettyDk mods n <+> text (concat (replicate params "_ ")) <> hsep (map (parens . (prettyDk mods)) l)
  prettyDk mods (DkLambda n t) =
    printIdent n <+> text "=>" <+> prettyDk mods t
  prettyDk mods (DkBrackets t) =
    braces (prettyDk mods t)

newtype DkCtx = DkCtx [(DkIdent,DkTerm)]

printContext :: [Int] -> DkCtx -> Doc
printContext used (DkCtx l) =
  let ll = extractIndex 0 (sortUniq used) l in
  brackets (hsep (punctuate (char ',') (map (printIdent . fst) (reverse ll))))
  where
    extractIndex _ []     _        = []
    extractIndex a (b:tl) (x:vars)
      | a==b      = x:(extractIndex (a+1) tl vars)
      | otherwise = extractIndex (a+1) (b:tl) vars

data DkName =
    DkLocal DkIdent
  | DkQualified DkModName DkIdent
  deriving (Eq, Show)

instance PrettyDk DkName where
  prettyDk mods (DkLocal n)            = printIdent n
  prettyDk mods (DkQualified qualif n) =
    let
      q = if last qualif == "DEFAULT"
          then init qualif
          else qualif
    in
    let modName =
          if mods == q
          then empty
          else hcat (punctuate (text "__") (map text q)) <> char '.'
    in
    let symName = printIdent n in
    modName <> symName

type DkModName = [String]

type DkIdent = (Maybe String, String)

printIdent (Nothing, n) =
    text $ replace convUnicode n
printIdent (Just m,  n) =
    text $ replace convUnicode (m++"__"++n)

data IsStatic = Static | Defin | TypeConstr

replace :: Eq a => [(a, [a])] -> [a] -> [a]
replace = replace' []

replace' :: Eq a => [a] -> [(a, [a])] -> [a] -> [a]
replace' acc assoc []     = reverse acc
replace' acc assoc (x:tl) = case lookup x assoc of Nothing    -> replace' (x:acc) assoc tl
                                                   Just latex -> replace' ((reverse latex)++acc) assoc tl
