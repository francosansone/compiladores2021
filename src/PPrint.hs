{-|
Module      : PPrint
Description : Pretty printer para FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module PPrint (
    pp,
    ppTy,
    ppName,
    ppDecl,
    sppDecl
    ) where

import Lang
import Subst ( open, openN )

import Data.Text ( unpack )
import Prettyprinter.Render.Terminal
  ( renderStrict, italicized, bold, color, colorDull, Color (..), AnsiStyle )
import Data.Text.Prettyprint.Doc
 --( (<+>), nest, parens, sep, pretty, Doc, layoutSmart, defaultLayoutOptions, annotate )
import MonadFD4
import Global

freshen :: [Name] -> Name -> Name
freshen ns n = let cands = n : (map (\i -> n ++ show i) [0..])
               in head (filter (\m -> not (elem m ns)) cands)

-- | 'openAll' convierte términos locally nameless
-- a términos fully named abriendo todos las variables de ligadura que va encontrando
-- Debe tener cuidado de no abrir términos con nombres que ya fueron abiertos.
-- Estos nombres se encuentran en la lista ns (primer argumento).
openAll :: [Name] -> Term -> NTerm
openAll ns (V p v) = case v of
      Bound i ->  V p $ "(Bound "++show i++")" --este caso no debería aparecer
                                               --si el término es localmente cerrado
      Free x -> V p x
      Global x -> V p x
openAll ns (Const p c) = Const p c
openAll ns (Lam p x ty t) =
  let x' = freshen ns x
  in Lam p x' ty (openAll (x':ns) (open x' t))
openAll ns (App p t u) = App p (openAll ns t) (openAll ns u)
openAll ns (Fix p f fty x xty t) =
  let
    x' = freshen ns x
    f' = freshen (x':ns) f
  in Fix p f' fty x' xty (openAll (x:f:ns) (openN [f',x'] t))
openAll ns (IfZ p c t e) = IfZ p (openAll ns c) (openAll ns t) (openAll ns e)
openAll ns (Print p str t) = Print p str (openAll ns t)
openAll ns (BinaryOp p op t u) = BinaryOp p op (openAll ns t) (openAll ns u)
openAll ns (Let p v ty m n) =
    let v'= freshen ns v
    in  Let p v' ty (openAll ns m) (openAll (v':ns) (open v' n))

--Colores
constColor = annotate (color Red)
opColor = annotate (colorDull Green)
keywordColor = annotate (colorDull Green) -- <> bold)
typeColor = annotate (color Blue <> italicized)
typeOpColor = annotate (colorDull Blue)
defColor = annotate (colorDull Magenta <> italicized)
nameColor = id
defTypeColor = annotate (colorDull Cyan <> italicized)


-- | Pretty printer de nombres (Doc)
name2doc :: Name -> Doc AnsiStyle
name2doc n = nameColor (pretty n)

-- |  Pretty printer de nombres (String)
ppName :: Name -> String
ppName = id

-- | Pretty printer para tipos (Doc)
ty2doc :: Ty -> Doc AnsiStyle
ty2doc NatTy     = typeColor (pretty "Nat")
ty2doc (FunTy x@(FunTy _ _) y) = sep [parens (ty2doc x), typeOpColor (pretty "->"),ty2doc y]
ty2doc (FunTy x y) = sep [ty2doc x, typeOpColor (pretty "->"),ty2doc y]

-- | Pretty printer para tipos (String)
ppTy :: Ty -> String
ppTy = render . ty2doc

c2doc :: Const -> Doc AnsiStyle
c2doc (CNat n) = constColor (pretty (show n))

binary2doc :: BinaryOp -> Doc AnsiStyle
binary2doc Add = opColor (pretty "+")
binary2doc Sub = opColor (pretty "-")

collectApp :: NTerm -> (NTerm, [NTerm])
collectApp t = go [] t where
  go ts (App _ h tt) = go (tt:ts) h
  go ts h = (h, ts)

parenIf :: Bool -> Doc a -> Doc a
parenIf True = parens
parenIf _ = id

-- t2doc at t :: Doc
-- at: debe ser un átomo
-- | Pretty printing de términos (Doc)
t2doc :: Bool     -- Debe ser un átomo? 
      -> NTerm    -- término a mostrar
      -> Doc AnsiStyle
-- Uncomment to use the Show instance for STerm
{- t2doc at x = text (show x) -}
t2doc at (V _ x) = name2doc x
t2doc at (Const _ c) = c2doc c
t2doc at (Lam _ v ty t) =
  parenIf at $
  sep [sep [ keywordColor (pretty "fun")
           , binding2doc (v,ty)
           , opColor(pretty "->")]
      , nest 2 (t2doc False t)]

t2doc at t@(App _ _ _) =
  let (h, ts) = collectApp t in
  parenIf at $
  t2doc True h <+> sep (map (t2doc True) ts)

t2doc at (Fix _ f fty x xty m) =
  parenIf at $
  sep [ sep [keywordColor (pretty "fix")
                  , binding2doc (f, fty)
                  , binding2doc (x, xty)
                  , opColor (pretty "->") ]
      , nest 2 (t2doc False m)
      ]
t2doc at (IfZ _ c t e) =
  parenIf at $
  sep [keywordColor (pretty "ifz"), nest 2 (t2doc False c)
     , keywordColor (pretty "then"), nest 2 (t2doc False t)
     , keywordColor (pretty "else"), nest 2 (t2doc False e) ]

t2doc at (Print _ str t) =
  parenIf at $
  sep [keywordColor (pretty "print"), pretty (show str), t2doc True t]

t2doc at (Let _ v ty t t') =
  parenIf at $
  sep [
    sep [keywordColor (pretty "let")
       , binding2doc (v,ty)
       , opColor (pretty "=") ]
  , nest 2 (t2doc False t)
  , keywordColor (pretty "in")
  , nest 2 (t2doc False t') ]

t2doc at (BinaryOp _ o a b) =
  parenIf at $
  t2doc True a <+> binary2doc o <+> t2doc True b

binding2doc :: (Name, Ty) -> Doc AnsiStyle
binding2doc (x, ty) =
  parens (sep [name2doc x, pretty ":", ty2doc ty])


-- | Pretty printing de términos (String)
pp :: MonadFD4 m => Term -> m String
-- Uncomment to use the Show instance for Term
{- pp = show -}
pp t = do
       gdecl <- gets glb
       return (render . t2doc False $ openAll (map declName gdecl) t)

render :: Doc AnsiStyle -> String
render = unpack . renderStrict . layoutSmart defaultLayoutOptions

-- | Pretty printing de declaraciones
ppDecl :: MonadFD4 m => Decl Term -> m String
ppDecl (Decl p x ty t) = do
  gdecl <- gets glb
  return (render $ sep [defColor (pretty "let")
                       , name2doc x
                       , defColor (pretty "=")]
                   <+> nest 2 (t2doc False (openAll (map declName gdecl) t)))

-- | Pretty printer para tipos con azucar (Doc)
sty2doc :: STy -> Doc AnsiStyle
sty2doc SNatTy     = typeColor (pretty "Nat")
sty2doc (SFunTy x@(SFunTy _ _) y) = sep [parens (sty2doc x), typeOpColor (pretty "->"),sty2doc y]
sty2doc (SFunTy x y) = sep [sty2doc x, typeOpColor (pretty "->"),sty2doc y]
sty2doc (SSynType n) = typeColor (pretty n)

-- | Pretty printing de declaraciones con azucar
sppDecl :: MonadFD4 m => SDecl STerm -> m String
sppDecl (SDecl p isrec x t binders b) =
  return (render $ sep ([defColor (pretty "let")
                       , name2doc x
                       ] ++ concatMap (\(x, t) ->
                          [ defColor (pretty "(")
                          , name2doc x
                          , defColor (pretty ":")
                          , sty2doc t
                          , defColor (pretty ")")])
                           binders ++
                       [ defColor (pretty ":")
                       , sty2doc t
                       , defColor (pretty "=")])
                   <+> nest 2 (st2doc False b))
sppDecl (SDeclType p n sty) = return (render $ sep [defTypeColor (pretty "type"), name2doc n, pretty "=", sty2doc sty])

scollectApp :: STerm -> (STerm, [STerm])
scollectApp t = go [] t where
  go ts (SApp _ h tt) = go (tt:ts) h
  go ts h = (h, ts)

sbinding2doc :: (Name, STy) -> Doc AnsiStyle
sbinding2doc (x, ty) =
  parens (sep [name2doc x, pretty ":", sty2doc ty])

-- st2doc at t :: Doc
-- at: debe ser un átomo
-- | Pretty printing de términos (Doc)
st2doc :: Bool     -- Debe ser un átomo?
      -> STerm    -- término a mostrar
      -> Doc AnsiStyle
-- Uncomment to use the Show instance for STerm
{- t2doc at x = text (show x) -}
st2doc at (SV _ x) = name2doc x
st2doc at (SConst _ c) = c2doc c
st2doc at (SLam _ b e) =
  parenIf at $
  sep [sep ([ keywordColor (pretty "fun")] ++
           map sbinding2doc b ++
           [ opColor(pretty "->")])
      , nest 2 (st2doc False e)]

st2doc at t@(SApp _ _ _) =
  let (h, ts) = scollectApp t in
  parenIf at $
  st2doc True h <+> sep (map (st2doc True) ts)

st2doc at (SFix _ bind m) =
  parenIf at $
  sep [ sep ([keywordColor (pretty "fix")] ++
            map sbinding2doc bind ++
            [opColor (pretty "->") ])
      , nest 2 (st2doc False m)
      ]

st2doc at (SIfZ _ c t e) =
  parenIf at $
  sep [keywordColor (pretty "ifz"), nest 2 (st2doc False c)
     , keywordColor (pretty "then"), nest 2 (st2doc False t)
     , keywordColor (pretty "else"), nest 2 (st2doc False e) ]


st2doc at (SPrint _ str) =
  parenIf at $
  sep [keywordColor (pretty "print"), pretty (show str)]

st2doc at (SLet _ _ v sty bind t t') =
  parenIf at $
  sep [
    sep ([keywordColor (pretty "let")
        , name2doc v] ++
        map sbinding2doc bind ++
        [ pretty ":"
        , sty2doc sty
        , opColor (pretty "=") ])
  , nest 2 (st2doc False t)
  , keywordColor (pretty "in")
  , nest 2 (st2doc False t') ]

st2doc at (SBinaryOp _ o a b) =
  parenIf at $
  st2doc True a <+> binary2doc o <+> st2doc True b
