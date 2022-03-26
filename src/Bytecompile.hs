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

type Module = [Decl Term]

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule m = do printFD4 $ show m
                         printFD4 $ show (moduleToTerm m)
                         l <- bc $ moduleToTerm m
                         printFD4 $ show $ l ++ [PRINTN, STOP]
                         return $ l ++ [PRINTN, STOP]

moduleToTerm :: Module -> Term
moduleToTerm [Decl p n b] = b
moduleToTerm ((Decl p n b):ms) = Let p n NatTy b (close n (moduleToTerm ms))
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
