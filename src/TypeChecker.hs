{-|
Module      : Typechecker
Description : Chequeo de tipos de términos y declaraciones.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}
module TypeChecker (
   tc,
   tcDecl,
   tyDecl
   ) where

import Lang
import Global
import MonadFD4
import PPrint
import Subst
import MonadFD4 (MonadFD4)
import Data.Maybe (fromJust)


-- | 'tc' chequea y devuelve el tipo de un término 
-- Si el término no está bien tipado, lanza un error
-- usando la interfaz de las mónadas @MonadFD4@.
tc :: MonadFD4 m => Term         -- ^ término a chequear
                 -> [(Name,Ty)]  -- ^ entorno de tipado
                 -> m Ty         -- ^ tipo del término
tc (V p (Bound _)) _ = failPosFD4 p "typecheck: No deberia haber variables Bound"
tc (V p (Free n)) bs = case lookup n bs of
                           Nothing -> failPosFD4 p $ "Variable no declarada "++ppName n
                           Just ty -> return ty
tc (V p (Global n)) bs = case lookup n bs of
                           Nothing -> failPosFD4 p $ "Variable no declarada "++ppName n
                           Just ty -> return ty
tc (Const _ (CNat n)) _ = return NatTy
tc (Print p str t) bs = do
      ty <- tc t bs
      expect NatTy ty t
tc (IfZ p c t t') bs = do
       tyc  <- tc c bs
       expect NatTy tyc c
       tyt  <- tc t bs
       tyt' <- tc t' bs
       expect tyt tyt' t'
tc (Lam p v ty t) bs = do
         ty' <- tc (open v t) ((v,ty):bs)
         return (FunTy ty ty')
tc (App p t u) bs = do
         tyt <- tc t bs
         (dom,cod) <- domCod t tyt
         tyu <- tc u bs
         expect dom tyu u
         return cod
tc (Fix p f fty x xty t) bs = do
         (dom, cod) <- domCod (V p (Free f)) fty
         when (dom /= xty) $ do
           failPosFD4 p "El tipo del argumento de un fixpoint debe coincidir con el \
                        \dominio del tipo de la función"
         let t' = openN [f, x] t
         ty' <- tc t' ((x,xty):(f,fty):bs)
         expect cod ty' t'
         return fty
tc (Let p v ty def t) bs = do
         ty' <- tc def bs
         expect ty ty' def
         tc (open v t) ((v,ty):bs)
tc (BinaryOp p op t u) bs = do
         tty <- tc t bs
         expect NatTy tty t
         uty <- tc t bs
         expect NatTy uty u

-- | @'typeError' t s@ lanza un error de tipo para el término @t@ 
typeError :: MonadFD4 m => Term   -- ^ término que se está chequeando  
                        -> String -- ^ mensaje de error
                        -> m a
typeError t s = do
   ppt <- pp t
   failPosFD4 (getInfo t) $ "Error de tipo en "++ppt++"\n"++s

-- | 'expect' chequea que el tipo esperado sea igual al que se obtuvo
-- y lanza un error si no lo es.
expect :: MonadFD4 m => Ty    -- ^ tipo esperado
                     -> Ty    -- ^ tipo que se obtuvo
                     -> Term  -- ^ término que se está chequeando
                     -> m Ty
expect ty ty' t = if ty == ty' then return ty
                               else typeError t $
              "Tipo esperado: "++ ppTy ty
            ++"\npero se obtuvo: "++ ppTy ty'

-- | 'domCod chequea que un tipo sea función
-- | devuelve un par con el tipo del dominio y el codominio de la función
domCod :: MonadFD4 m => Term -> Ty -> m (Ty, Ty)
domCod t (FunTy d c) = return (d, c)
domCod t ty = typeError t $ "Se esperaba un tipo función, pero se obtuvo: " ++ ppTy ty

-- | 'tcDecl' chequea el tipo de una declaración
-- y la agrega al entorno de tipado de declaraciones globales
tcDecl :: MonadFD4 m  => Decl Term -> m ()
tcDecl (Decl p n ty t) = do
    --chequear si el nombre ya está declarado
    mty <- lookupTy n
    case mty of
        Nothing -> do  --no está declarado
                  s <- get
                  ty1 <- tc t (tyEnv s)
                  expect ty ty1 t
                  addTy n ty1
        Just _  -> failPosFD4 p $ n ++" ya está declarado"

-- | 'tcDecl' agrega un sinonimo de tipo al entorno de sinonimos de tipos globales
tyDecl :: MonadFD4 m  => SDecl STerm -> m ()
tyDecl (SDeclType p n t) = do
    --chequear si el nombre ya está declarado
    y <- isValidType t
    if y then
      do mty <- lookupSTy n
         case mty of
            Nothing -> do  addSynTy n t --no está declarado
            Just _  -> failPosFD4 p $ "El tipo " ++ n ++" ya está declarado"
    else failPosFD4 p $ n ++" fue declarado a un tipo inexistente"
tyDecl _ = return ()

isValidType :: MonadFD4 m => STy -> m Bool
isValidType (SFunTy x y) = do
   b <- isValidType x
   if b then
      do isValidType y
   else
      return False
isValidType SNatTy = return True
isValidType (SSynType n) = do
   t <- lookupSTy n
   case t of
      Nothing -> return False
      Just _ -> return True

getTy :: MonadFD4 m => STy -> m Ty
getTy SNatTy = return NatTy
getTy (SFunTy x y) = do
   u <- getTy x
   v <- getTy y
   return $ FunTy u v
getTy (SSynType n) = do
   t <- lookupSTy n
   getTy $ fromJust t