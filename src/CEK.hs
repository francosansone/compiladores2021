module CEK (evalCEK) where 

import Lang
import Common
import Subst (substN)
import MonadFD4

type Env = [Val]

data Val = VNat Const | VClos Clos
    deriving (Show)

data Clos = ClosFun Env Name Ty Term | ClosFix Env Name Ty Name Ty Term -- necesito los tipos en Clos para convertirlos nuevamente a terminos 
    deriving (Show)

data Frame = 
    KArg Env Term |
    KClos Clos |
    KIfZ Env Term Term |
    KBinOp1 BinaryOp Env Term |
    KBinOp2 BinaryOp Val |
    KPrint String | 
    KLet Env Name Term 
    deriving (Show)

type Kont = [Frame]

search :: MonadFD4 m => Term -> Env -> Kont -> m Val
search (Print _ str t) e k = search t e (KPrint str:k)
search (BinaryOp _ op t u) e k = search t e (KBinOp1 op e u:k)
search (IfZ _ c t u) e k = search c e (KIfZ e t u:k)
search (App _ t u) e k = search t e (KArg e u:k)
search (V _ (Bound x)) e k = destroy (e!!x) k
search (V _ (Free x)) e k = do
    t <- lookupDecl x
    case t of
        Just u -> search u e k
        Nothing -> failFD4 $ "Error en runtime. Variable " ++ x ++ " no declarada."
search (Const _ n) e k = destroy (VNat n) k
search (Lam _ n nty t) e k = destroy (VClos $ ClosFun e n nty t) k
search (Fix _ f fty x xty t) e k = destroy (VClos $ ClosFix e f fty x xty t) k
search (Let _ n nty t u) e k = search t e (KLet e n u:k)
search _ _ k = do
    printFD4 (show k) 
    failFD4 "Esto no debería haber pasado"

destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v [] = return v
destroy v (KPrint str:k) = do
    printFD4 str
    destroy v k
destroy n (KBinOp1 op e u : k) = search u e (KBinOp2 op n : k)
destroy (VNat (CNat x)) (KBinOp2 Add (VNat (CNat y)) : k) = destroy (VNat (CNat $ x + y)) k
destroy (VNat (CNat n1)) (KBinOp2 _ (VNat (CNat n2)) : k) = destroy (VNat $ CNat (max 0 (n2 - n1))) k
destroy (VNat (CNat 0)) (KIfZ e t u:k) = search t e k
destroy (VNat (CNat n)) (KIfZ e t u:k) = search u e k
destroy (VClos c) (KArg e t:k) = search t e (KClos c:k)
destroy v (KClos (ClosFun e n nty t):k) = search t (v:e) k
destroy v (KClos (ClosFix e f fty n nty t):k) = let ff = VClos $ ClosFix e f fty n nty t in search t (v:(ff:e)) k
destroy v (KLet e n t:k) = search t (v:e) k
destroy v k = do
    failFD4 $ "[destroy] Esto no debería haber pasado\n" ++ show v ++ "\n"  ++ show k

valToTerm :: Val -> Term
valToTerm (VNat v) = Const NoPos v
valToTerm (VClos (ClosFun e x xty t))       = substN (map valToTerm e) (Lam NoPos x xty t)
valToTerm (VClos (ClosFix e f fty x xty t)) = substN (map valToTerm e) (Fix NoPos f fty x xty t)

evalCEK :: MonadFD4 m => Term -> m Term
evalCEK t = do v <- search t [] [] -- inicia con entorno y continuaciones vacios
               return (valToTerm v)