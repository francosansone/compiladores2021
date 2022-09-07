{-# LANGUAGE PatternSynonyms #-}
{-|
Module      : ClosureConvert
Description : Compila a Ir.
-}

-- http://learnyouahaskell.com/for-a-few-monads-more

module ClosureConvert
 where

import Control.Monad.Writer
import Control.Monad.State
import IR
import Lang
import MonadFD4
import Subst
import C
import Common

-- runCC :: [Decl Term] -> [IrDecl]

getFreshName :: () -> StateT Int (Writer [IrDecl]) Name
getFreshName () = do
    counter <- get
    let fresh_name = "__" ++ "f" ++ show (counter)
    modify(\c -> c + 1)
    return fresh_name

codef :: Name -> Ir -> [Name] -> Ir
codef = codef' 1

codef' counter name term [] = term
codef' counter name term (x:xs) = IrLet x (IrAccess (IrVar name) counter)
                                          (codef' (counter + 1) name term xs)

closureConvert :: Term -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V _ (Free n)) = return $ IrVar n

closureConvert (V _ (Bound _)) = error "variable ligada en closureConvert"

closureConvert (V _ (Global n)) = return $ IrGlobal n

closureConvert (Const _ c) = return $ IrConst c
-- Crear una nueva clausura con un nombre fresco.
-- agregar un let con la implementación de la clausura usando
-- writer
closureConvert (Lam _ n _ term) = do    new_name <- getFreshName ()
                                        cterm <- closureConvert $ (open n term)
                                        let free_vars = freeVars term
                                        let clos_name = new_name ++ "_c"
                                        let fun_term = codef clos_name cterm free_vars
                                        tell [IrFun new_name [clos_name, n] fun_term]
                                        let clos_env = map (\x -> IrVar x) free_vars
                                        return $ MkClosure new_name clos_env

closureConvert (App _ f x) = do clos_f <- closureConvert f
                                clos_x <- closureConvert x
                                fun_name <- getFreshName ()
                                let clos = IrVar fun_name
                                return $ IrLet fun_name clos_f (IrCall (IrAccess clos 0) [clos, clos_x])

closureConvert (Print _ str t) = do ir_t <- closureConvert t
                                    return $ IrPrint str ir_t
closureConvert (BinaryOp _ op a b) = do ir_a <- closureConvert a
                                        ir_b <- closureConvert b
                                        return $ IrBinaryOp op ir_a ir_b

-- closureConvert (Fix _ f _ v _ t) = do   ffresh_name <- getFreshName ()

closureConvert (IfZ _ t a b) = do ir_t <- closureConvert t
                                  ir_a <- closureConvert a
                                  ir_b <- closureConvert b
                                  return $ IrIfZ ir_t ir_a ir_b

closureConvert (Let _ n _ t u) = do ir_t <- closureConvert t
                                    ir_u <- closureConvert (open n u)
                                    return $ IrLet n ir_t ir_u
-- closureConvert t = return $ IrVar "a"

-- 'runFD4\'' corre una computación de la mónad 'FD4' en el estado inicial 'Global.initialEnv'
-- runFD4' :: FD4 a -> IO (Either Error (a, GlEnv))
-- runFD4' c =  runExceptT $ runStateT c initialEnv

-- runFD4:: FD4 a -> IO (Either Error a)
-- runFD4 c = fmap fst <$> runFD4' c

-- runWriter $ runStateT (closureConvert term) [] retorna ((Ir, [Name]), [IrDecl])

-- Traduzco a IrVal para estar acorde con la funcion fd4Main.
runCC :: [Decl Term] -> [IrDecl]
runCC [] = []
runCC ((Decl _ name body):decls) =
    let ((ir, _), ir_decls) = runWriter $ runStateT (closureConvert body) 0 -- no tengo muy claro esto, pero tipa
        rest = (runCC decls)
    in (IrVal name ir):(ir_decls ++ rest)

cCompile :: [Decl Term] -> String
cCompile xs = ir2C $ IrDecls $ runCC xs

cWrite :: String -> FilePath -> IO ()
cWrite cp filename = writeFile filename cp