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
  let kw = if b then empty else text "def " in
  let typDecl = parens (prettyDk mods k) <+> parens (prettyDk mods t) in
  kw <> withoutFile mods n <+> text ": naiveAgda.Term" <+> typDecl <> text ".\n"

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
  | DkApp DkTerm DkTerm [DkTerm]
  | DkLam DkIdent (Maybe (DkTerm,DkSort)) DkTerm
  | DkDB DkIdent Int
  | DkFake String

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
  prettyDk mods (DkApp t u l)            =
    let args = hsep (map (parens . (prettyDk mods)) l) in
    parens (prettyDk mods t) <+> parens (prettyDk mods u) <+> args
  prettyDk mods (DkLam n Nothing t)      =
    printIdent n <+> text "=>" <+> prettyDk mods t
  prettyDk mods (DkLam n (Just (a,s)) t) =
    let typCode = parens (prettyDk mods a) in
    let annot = text "naiveAgda.Term" <+> parens (prettyDk mods s) <+> typCode in
    printIdent n <+> char ':' <+> annot <+> text "=>" <+> prettyDk mods t
  prettyDk mods (DkDB n _)               =
    printIdent n
  prettyDk mods (DkFake s)               =
    text ("FAKE "++s)

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
    let modName =
          if isPrefixOf mods qualif
          then hcat (punctuate (text "__") (map printIdent mods))
          else hcat (punctuate (text "__") (map printIdent qualif))
    in
    let symList = case stripPrefix mods qualif of Nothing -> [n]
                                                  Just s  -> s++[n]
    in
    let symName = hcat (punctuate (text "__") (map printIdent symList)) in
    modName <> char '.'<> symName

withoutFile :: DkModName -> DkName -> Doc
withoutFile mods (DkLocal n)            = printIdent n
withoutFile mods (DkQualified qualif n) =
  let symList = case stripPrefix mods qualif of Nothing -> qualif++[n]
                                                Just s  -> s++[n]
  in
  hcat (punctuate (text "__") (map printIdent symList))

type DkModName = [DkIdent]

type DkIdent = String

printIdent n =
    text $ replace n [] convUnicode

type IsStatic = Bool

replace :: Eq a => [a] -> [a] -> [(a, [a])] -> [a]
replace []   acc _       = reverse acc
replace (x:tl) acc assoc = case lookup x assoc of Nothing    -> replace tl (x:acc) assoc
                                                  Just latex -> replace tl ((reverse latex)++acc) assoc
