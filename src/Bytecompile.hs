{-# LANGUAGE PatternSynonyms #-}
{-|
Module      : Byecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite compilar módulos a la BVM. También provee una implementación de la BVM 
para ejecutar bytecode.
-}
module Bytecompile
  (Bytecode, runBC, bcWrite, bcRead,bytecompileModule)
 where

import Lang
import Subst
import MonadFD4

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )

import Data.Char

type Opcode = Int
type Bytecode = [Int]

{- Tipo algebraico para la representacion de valores -}
type Env = [Val]
data Val = I Int | Fun Env Bytecode | RA Env Bytecode deriving (Show)

newtype Bytecode32 = BC { un32 :: [Word32] }

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord32le
                      BC xs <- go
                      return $ BC (x:xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:
 
   f (CALL : cs) = ...

 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.

 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern NULL     = 0
pattern RETURN   = 1
pattern CONST    = 2
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern ADD      = 6
pattern SUB      = 7
pattern IFZ      = 8
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
pattern JUMP     = 15
pattern TAILCALL = 16

bc :: MonadFD4 m => Term -> m Bytecode
bc (V _ (Bound n)) = return [ACCESS, n]
bc (Const _ (CNat n)) = return [CONST, n]
bc (Lam _ n _ t) = do tc <- tailcall t
                      return $ [FUNCTION, length tc + 1] ++ tc ++ [RETURN]
bc (App _ t u) = do bt <- bc t
                    bu <- bc u
                    return $ bt ++ bu ++ [CALL]
bc (BinaryOp _ op t u) = do bt <- bc t
                            bu <- bc u
                            case op of
                              Add -> return $ bt ++ bu ++ [ADD]
                              _   -> return $ bt ++ bu ++ [SUB]
bc (Let _ n t e1 e2) = do be1 <- bc e1
                          be2 <- bc e2
                          return $ be1 ++ [SHIFT] ++ be2 ++ [DROP]
bc (Print _ str n) = do bn <- bc n
                        return $ [PRINT] ++ map ord str ++ [NULL] ++ bn ++ [PRINTN]
bc (Fix _ _ _ _ _ t) = do bt <- bc t
                          return $ [FUNCTION, length bt + 1] ++ bt ++ [RETURN, FIX]
bc (IfZ _ b e1 e2) = do bb <- bc b
                        be1 <- bc e1
                        be2 <- bc e2
                        let
                            lb1 = length be1
                            lb2 = length be2 in
                          return $ bb ++ [IFZ, lb1 + 2] ++ be1 ++ [JUMP, lb2] ++ be2
bc t = do printFD4 $ show t; return [STOP]

-- Funcion auxiliar para compilar funciones en posicion de cola
tailcall :: MonadFD4 m => Term -> m Bytecode
tailcall (App _ a b) = do ba <- bc a
                          bb <- bc b
                          return $ ba ++ bb ++ [TAILCALL]
tailcall (IfZ _ b e1 e2) = do bb <- bc b
                              te1 <- tailcall e1
                              te2 <- tailcall e2
                              let
                                  le1 = length te1
                                  le2 = length te2 in
                                return $ bb ++ [IFZ, le1 + 2] ++ te1 ++ [JUMP, le2] ++ te2
tailcall (Let _ _ _ m n) = do   be1 <- bc m
                                be2 <- tailcall n
                                return $ be1 ++ [SHIFT] ++ be2
tailcall t           = do bt <- bc t
                          return $ bt  ++ [RETURN]

bytecompileModule :: MonadFD4 m => Bool -> Module -> m Bytecode
bytecompileModule opt m = do  -- printFD4 $ show (moduleToTerm m)
                              m_op <- if opt then
                                        optimizing 100 $ moduleToTerm m -- esto podría mejorarse detectando si la optimizacion funcionó
                                      else
                                        optimizing 0 $ moduleToTerm m
                              -- printFD4 $ show m_op
                              l <- bc m_op
                              -- printFD4 $ show $ l ++ [PRINTN, STOP]
                              return $ l ++ [PRINTN, STOP]

moduleToTerm :: Module -> Term
moduleToTerm [Decl p n _ b] = b
moduleToTerm ((Decl p n _ b):ms) = Let p n NatTy b (close n (moduleToTerm ms))
moduleToTerm [] = error "moduleToTerm: No deberia haber pasado"

-- | Toma un bytecode, lo codifica y lo escribe un archivo 
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)


---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = map fromIntegral <$> un32  <$> decode <$> BS.readFile filename

runBC :: Bytecode -> IO ()
runBC c = runBC' c [] []

{- 
type Env = [Val]
data Val = I Int | Fun Env Bytecode | RA Env Bytecode
-}

runBC':: Bytecode -> Env -> Env -> IO ()
runBC' (CONST:(n:c)) e s = runBC' c e (I n:s)
runBC' (ADD:c) e (I x:(I y:s)) = runBC' c e (I (y + x):s)
runBC' (SUB:c) e (I x:(I y:s)) = runBC' c e (I (y - x):s)
runBC' (ACCESS:(i:c)) e s = runBC' c e (e!!i:s)
runBC' (CALL:c) e (v:(Fun ef b:s)) = runBC' b (v:ef) (RA e c:s)
runBC' (TAILCALL:r) e (v:Fun eg cg:ra@(RA ef cf):s) = runBC' cg (v:eg) (ra:s)
runBC' (FUNCTION:(len:c)) e s =
  let
    cf = take len c
    c' = drop len c
  in
    runBC' c' e (Fun e cf:s)
runBC' (RETURN:_) _ (v:(RA e c:s)) = runBC' c e (v:s)
runBC' (SHIFT:c) e (v:s) = runBC' c (v:e) s
runBC' (DROP:c) (v:e) s = runBC' c e s
runBC' (PRINTN:c) e (I n:s) = do
  print $ show n
  runBC' c e (I n:s)
runBC' (PRINT:c) e s = do c' <- auxPrint c ""; runBC' c' e s
runBC' (FIX:c) e ((Fun fe fc):s)        =
  let
    efix = (Fun efix fc):fe
  in
    runBC' c e ((Fun efix fc):s)
runBC' (IFZ:(bb1:c)) e ((I 0):s) = runBC' c e s
runBC' (IFZ:(bb1:c)) e (x:s) =
  let
    cf = drop bb1 c
  in
    runBC' cf e s
runBC' (JUMP:(n:c)) e s = runBC' (drop n c) e s
runBC' (STOP:c) e s = return ()
runBC' c _ s = error $ show c ++ ", " ++ show s  ++ " Error en tiempo de ejecucion."

auxPrint :: Bytecode -> String -> IO (Bytecode)
auxPrint (NULL:c) str = do print $ reverse str; return c
auxPrint (x:c) str = auxPrint c (chr x:str)
auxPrint _ _ = error "Error en PRINT"

optimizing :: MonadFD4 m => Int -> Term -> m Term
optimizing 0 t = return t
optimizing n t = do t_op <- constanFolding t
                    t_op_2 <- constantPropagation t_op
                    optimizing (n-1) t_op_2

constanFolding :: MonadFD4 m => Term -> m Term
constanFolding v@(V _ (Bound n)) = return v
constanFolding c@(Const _ (CNat n)) = return c
constanFolding (Lam i n ty t) = do body <- constanFolding t; return $ Lam i n ty body
constanFolding (App i t u) = do t_op <- constanFolding t; u_op <- constanFolding u; return $ App i t_op u_op
constanFolding (BinaryOp i op (Const _ (CNat t)) (Const _ (CNat u))) = return $ Const i (CNat $ t + u)
constanFolding (Let i n t e1 e2) = do e1_op <- constanFolding e1
                                      e2_op <- constanFolding e2
                                      return $ Let i n t e1_op e2_op
constanFolding (Print i str n) = do n_op <- constanFolding n; return $ Print i str n_op
constanFolding (Fix i n1 t1 n2 t2 t) = do t_op <- constanFolding t; return $ Fix i n1 t1 n2 t2 t_op
constanFolding (IfZ _ (Const _ c) e1 e2) = case c of
                                              CNat 0 -> constanFolding e1
                                              _      -> constanFolding e2
constanFolding (IfZ i b e1 e2) = do b_op <- constanFolding b
                                    e1_op <- constanFolding e1
                                    e2_op <- constanFolding e2
                                    return $ IfZ i b_op e1_op e2_op
constanFolding t = return t

constantPropagation :: MonadFD4 m => Term -> m Term
constantPropagation (Let p v vty c@(Const _ _) e) = do  e_op <- constantPropagation $ replaceConstant c e
                                                        return $ Let p v vty c e_op
constantPropagation (Lam p y ty b) = do b_op <- constantPropagation b;
                                                 return (Lam p y ty b_op)
constantPropagation (App p l r) = do  l_op <- constantPropagation l
                                      r_op <- constantPropagation r
                                      return $ App p l_op r_op
constantPropagation (Fix p f fty x xty t) = do  t_op <- constantPropagation t
                                                return $ Fix p f fty x xty t_op
constantPropagation (IfZ p c t e) = do  c_op <- constantPropagation c
                                        t_op <- constantPropagation t
                                        e_op <- constantPropagation e
                                        return $ IfZ p c_op t_op e_op
constantPropagation (Print p str t) = do  t_op <- constantPropagation t
                                          return $ Print p str t_op
constantPropagation (BinaryOp p op t u) = do  t_op <- constantPropagation t
                                              u_op <- constantPropagation u
                                              return $ BinaryOp p op t_op u_op
constantPropagation t = return t

replaceConstant :: Term -> Term -> Term
replaceConstant = replaceConstant' 0

replaceConstant' :: Int -> Term -> Term -> Term
replaceConstant' n t v@(V _ (Bound i)) = if i == n then t else v
replaceConstant' n t (Lam p y ty b) = Lam p y ty (replaceConstant' (n + 1) t b)
replaceConstant' n t (App p l r) = App p (replaceConstant' n t l) (replaceConstant' n t r)
replaceConstant' n t (Fix p f fty x xty b) = Fix p f fty x xty (replaceConstant' (n + 1) t b)
replaceConstant' n t (IfZ p c l r) = IfZ p (replaceConstant' n t c) (replaceConstant' n t l) (replaceConstant' n t r)
replaceConstant' n t c@(Const _ _) = c
replaceConstant' n t (Print p str b) = Print p str (replaceConstant' n t b)
replaceConstant' n t (BinaryOp p op l r) = BinaryOp p op (replaceConstant' n t l) (replaceConstant' n t r)
replaceConstant' n t (Let p v vty m o) = Let p v vty (replaceConstant' n t m) (replaceConstant' (n + 1) t o)
replaceConstant' _ _ b = b