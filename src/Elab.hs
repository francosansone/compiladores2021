{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@NTerm) a locally closed (@Term@) 
-}

module Elab ( elab, desugarSdecl, elabAndDesugar ) where

import Lang
import Subst
import MonadFD4 (failPosFD4, MonadFD4, lookupTy, addTy, lookupSTy)
import Common (Pos(NoPos))
import Control.Monad (when)
import Data.Maybe (isNothing, fromJust)

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: NTerm -> Term
elab = elab' []

elabAndDesugar :: MonadFD4 m => STerm -> m Term
elabAndDesugar s = do
  t <- desugarSterm s
  return $ elab t

elab' :: [Name] -> NTerm -> Term
elab' env (V p v) =
  -- Tenemos que hver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  if v `elem` env
    then  V p (Free v)
    else V p (Global v)

elab' _ (Const p c) = Const p c
elab' env (Lam p v ty t) = Lam p v ty (close v (elab' (v:env) t))
elab' env (Fix p f fty x xty t) = Fix p f fty x xty (closeN [f, x] (elab' (x:f:env) t))
elab' env (IfZ p c t e)         = IfZ p (elab' env c) (elab' env t) (elab' env e)
-- Operador Print
elab' env (Print i str t) = Print i str (elab' env t)
-- Operadores binarios
elab' env (BinaryOp i o t u) = BinaryOp i o (elab' env t) (elab' env u)
-- Aplicaciones generales
elab' env (App p h a) = App p (elab' env h) (elab' env a)
elab' env (Let p v vty def body) = Let p v vty (elab' env def) (close v (elab' (v:env) body))

desugarSdecl :: MonadFD4 m => SDecl STerm -> m (Decl NTerm)
desugarSdecl (SDecl p True n sty binders body) = do
  let l = (n, sty):binders
  b <- desugarSterm $ SFix p ((n, typeFromBinders l):binders) body
  return (Decl p n b)
desugarSdecl (SDecl p False n sty binders body) = do
  b <- desugarSterm $ SLam p binders body
  return (Decl p n b)
desugarSdecl (SDeclType p n sty) = failPosFD4 p "Esto no debería haber pasado"


desugarSterm :: MonadFD4 m => STerm  -> m NTerm
desugarSterm (SV info var) = return (V info var)
desugarSterm (SConst info c) = return (Const info c)
desugarSterm (SLam info ((n, ty):xs) exp) = do
  ty <- slookupTy ty
  typeExist info ty
  Lam info n (fromJust ty) <$> desugarSterm (SLam info xs exp)
desugarSterm (SLam info [] exp) = desugarSterm exp
desugarSterm (SApp info exp1 exp2) = do
  e1 <- desugarSterm exp1
  e2 <- desugarSterm exp2
  return (App info e1 e2)
-- η-expansion del termino Print
desugarSterm (SPrint info str) = return (Lam info "x" NatTy (Print info str (V info "x")))
desugarSterm (SBinaryOp info op sexp1 sexp2) = do
  exp1 <- desugarSterm sexp1
  exp2 <- desugarSterm sexp2
  return (BinaryOp info op exp1 exp2)
desugarSterm (SFix info ((y, ysty):((x, xsty):xs)) exp) = do
  yty <- slookupTy ysty
  typeExist info yty
  xty <- slookupTy xsty
  Fix info y (fromJust yty) x (fromJust xty) <$> desugarSterm (SLam info xs exp)
desugarSterm (SIfZ info sexp1 sexp2 sexp3) = do
  exp1 <- desugarSterm sexp1
  exp2 <- desugarSterm sexp2
  exp3 <- desugarSterm sexp3
  return (IfZ info exp1 exp2 exp3)
desugarSterm (SLet False info f sty [] st1 st2) = do
  ty <- slookupTy sty
  typeExist info ty
  t1 <- desugarSterm st1
  t2 <- desugarSterm st2
  return $ Let info f (fromJust ty) t1 t2
desugarSterm (SLet False info f sty ((x, xty):xs)  st1 st2) = desugarSterm (SLet False info f (SFunTy xty sty) xs (SLam info [(x, xty)] st1) st2)
desugarSterm (SLet b info n sty binders sexp1 sexp2) = do
  ty <- slookupTy sty
  typeExist info ty
  exp2 <- desugarSterm sexp2
  exp1 <- desugarSterm (SFix info binders sexp1)
  return (Let info n (fromJust ty) exp1 exp2)
desugarSterm _ = failPosFD4 NoPos "desugarSterm: esto no deberia haber pasado"

slookupTy :: MonadFD4 m => STy -> m (Maybe Ty)
slookupTy SNatTy = return (Just NatTy)
slookupTy (SFunTy sty1 sty2) =
  do ty1 <- slookupTy sty1
     ty2 <- slookupTy sty2
     if isNothing ty1 || isNothing ty2 then return Nothing
     else return (Just (FunTy (fromJust ty1) (fromJust ty2)))
slookupTy (SSynType n) = do
  st <- lookupSTy n
  case st of
    Nothing -> return Nothing
    Just SNatTy  -> return $ Just NatTy
    Just x -> slookupTy x

typeExist :: MonadFD4 m => Pos -> Maybe Ty -> m ()
typeExist p ty = when (isNothing ty) $ do
    failPosFD4 p "El tipo no existe"

typeFromBinders :: [(Name, STy)] -> STy
typeFromBinders [(n, t)] = t
typeFromBinders ((x, t):xs) = SFunTy t $ typeFromBinders xs
typeFromBinders [] = errorWithoutStackTrace "typeFromBinders"
