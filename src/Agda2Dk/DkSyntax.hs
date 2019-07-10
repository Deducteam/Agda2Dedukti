module Agda2Dk.DkSyntax where

import Data.Word
import Data.List
import Text.PrettyPrint

class PrettyDk a where
  prettyDk :: a -> Doc

data DkDefinition =
   DkDefinition
    { name      :: DkName
    , staticity :: IsStatic
    , typ       :: DkTerm
    , rules     :: [DkRule]
    }

instance PrettyDk DkDefinition where
  prettyDk (DkDefinition {name=n, staticity=b, typ=t, rules=l}) =
    let kw = if b then text "def " else empty in
    kw<>(prettyDk n)<+> text ": eps"<+> parens (prettyDk t)<>text ".\n"<>(hcat (map prettyDk l))

data DkSort =
    DkSet Int
  | DkProp Int
  | DkSetOmega
  | DkDefaultSort

instance PrettyDk DkSort where
  prettyDk (DkSet i) = text "set"<+>int i
  prettyDk (DkProp i) = text "prop"<+>int i
  prettyDk DkSetOmega = text "setOmega"
  prettyDk DkDefaultSort = text "DEFAULT_SORT"

data DkRule =
   DkRule
    { context  :: DkCtx
    , headsymb :: DkName
    , patts    :: [DkPattern]
    , rhs      :: DkTerm
    }

instance PrettyDk DkRule where
  prettyDk (DkRule {context=c, headsymb=hd, patts=l, rhs=t}) =
    (prettyDk c)<+>(prettyDk hd)<+>hsep (map (parens . prettyDk) l)<+>text "-->"<+>(prettyDk t)<>text ".\n"

data DkTerm =
    DkSort DkSort
  | DkProd DkSort DkSort DkIdent DkTerm DkTerm
  | DkConst DkName
  | DkApp DkTerm DkTerm [DkTerm]
  | DkLam DkIdent (Maybe DkTerm) DkTerm
  | DkDB DkIdent Int
  | DkFake String

instance PrettyDk DkTerm where
  prettyDk (DkSort s) = prettyDk s
  prettyDk (DkProd s1 s2 n t u) =
    text "prod"<+>parens (prettyDk s1)<+>parens (prettyDk s2)<+>parens (prettyDk t)<+>parens (prettyDk n<+>text "=>"<+>prettyDk u)
  prettyDk (DkConst f) = prettyDk f
  prettyDk (DkApp t u l) = parens (prettyDk t)<+>parens (prettyDk u)<+>hsep (map prettyDk l)
  prettyDk (DkLam n Nothing t) = prettyDk n<+>text "=>"<+>prettyDk t
  prettyDk (DkLam n (Just a) t) = prettyDk n<+>text ": eps"<+>parens (prettyDk a)<+>text "=>"<+>prettyDk t
  prettyDk (DkDB i _) = prettyDk i
  prettyDk (DkFake s) = text ("Fake "++s)

data DkPattern =
    DkVar DkIdent Int [DkPattern]
  | DkFun DkName [DkPattern]
  | DkLambda DkIdent DkPattern
  | DkBrackets DkTerm

instance PrettyDk DkPattern where
  prettyDk (DkVar n _ l) = prettyDk n<+>hsep (map (parens . prettyDk) l)
  prettyDk (DkFun n l) = prettyDk n<+>hsep (map (parens . prettyDk) l)
  prettyDk (DkLambda n t) = prettyDk n<+>text "=>"<+>prettyDk t
  prettyDk (DkBrackets t) = braces (prettyDk t)

newtype DkCtx = DkCtx [(DkIdent,DkTerm)]

instance PrettyDk DkCtx where
  prettyDk (DkCtx l) =
    let colonSep (a,b) = prettyDk a<+>text ": eps"<+>parens (prettyDk b) in
    brackets (hsep (punctuate (char ',') (map colonSep l)))

data DkName =
    DkLocal DkIdent
  | DkQualified DkModName DkIdent

instance PrettyDk DkName where
  prettyDk (DkLocal n) = prettyDk n
  prettyDk (DkQualified mods n) = hcat (punctuate (char '.') (map prettyDk (mods++[n])))

type DkModName = [DkIdent]

data DkIdent =
  DkIdent
  { w64      :: Word64
  , concrete :: String
  }

instance PrettyDk DkIdent where
  prettyDk (DkIdent {concrete=n}) = text n

type IsStatic = Bool
