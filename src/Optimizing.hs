module Optimizing
  where

import Lang
import MonadFD4
import Common

optimizing :: MonadFD4 m => Int -> Module -> m Module
optimizing 0 t = return t
optimizing n t = do t_op_1 <- mapM constantFoldingDecl t
                    t_op_2 <- constantPropagationGlobal t_op_1
                    t_op_3 <- mapM constantPropagationDecl t_op_2
                    optimizing (n-1) t_op_3

constantFoldingDecl :: MonadFD4 m => Decl Term -> m (Decl Term)
constantFoldingDecl d@(Decl p n ty t) = do
    opt_t <- constanFolding t
    return $ Decl p n ty opt_t

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

constantPropagationDecl :: MonadFD4 m => Decl Term -> m (Decl Term)
constantPropagationDecl d@(Decl p n ty t) = do
    opt_t <- constantPropagationTerm t
    return $ Decl p n ty opt_t

constantPropagationGlobal :: MonadFD4 m => [Decl Term] -> m ([Decl Term])
constantPropagationGlobal (d@(Decl p n ty c@(Const _ _)):ds) = do
    new_decls <- mapM (replaceConstantDecl n c) ds
    new_decls2 <- constantPropagationGlobal new_decls
    return $ d:new_decls2
constantPropagationGlobal (d@(Decl p n ty t):ds) = do
    decls <- constantPropagationGlobal ds
    return $ d:ds
constantPropagationGlobal [] = return []


replaceConstantDecl :: MonadFD4 m => Name -> Term -> Decl Term -> m(Decl Term)
replaceConstantDecl name t1 (Decl p n ty t2) = do
    new_t <- replaceConstantTerm name t1 t2
    return $ Decl p n ty new_t

replaceConstantTerm :: MonadFD4 m => Name -> Term -> Term -> m(Term)
replaceConstantTerm name term t@(V p (Free v)) = do
    if v == name then
        return term
    else
        return t
replaceConstantTerm name term (Lam info n ty t) = do
    opt_t <- replaceConstantTerm name term t
    return $ Lam info n ty opt_t
replaceConstantTerm name term (App info t1 t2) = do
    opt_t1 <- replaceConstantTerm name term t1
    opt_t2 <- replaceConstantTerm name term t2
    return $ App info opt_t1 opt_t2
replaceConstantTerm name term (Print info str t) = do
    opt_t <- replaceConstantTerm name term t
    return $ Print info str opt_t
replaceConstantTerm name term (BinaryOp info op t1 t2) = do
    opt_t1 <- replaceConstantTerm name term t1
    opt_t2 <- replaceConstantTerm name term t2
    return $ BinaryOp info op opt_t1 opt_t2
replaceConstantTerm name term (Fix info n1 ty1 n2 ty2 t) = do
    opt_t <- replaceConstantTerm name term t
    return $ Fix info n1 ty1 n2 ty2 opt_t
replaceConstantTerm name term (IfZ info cond t1 t2) = do
    opt_cond <- replaceConstantTerm name term cond
    opt_t1 <- replaceConstantTerm name term t1
    opt_t2 <- replaceConstantTerm name term t2
    return $ IfZ info opt_cond opt_t1 opt_t2
replaceConstantTerm name term (Let info n ty t1 t2) = do
    opt_t1 <- replaceConstantTerm name term t1
    opt_t2 <- replaceConstantTerm name term t2
    return $ Let info n ty opt_t1 opt_t2
replaceConstantTerm name term t = return t
-----------------

constantPropagationTerm :: MonadFD4 m => Term -> m Term
constantPropagationTerm (Let p v vty c@(Const _ _) e) = do  e_op <- constantPropagationTerm $ replaceConstant c e
                                                            return $ Let p v vty c e_op
constantPropagationTerm (Lam p y ty b) = do b_op <- constantPropagationTerm b;
                                                     return (Lam p y ty b_op)
constantPropagationTerm (App p l r) = do  l_op <- constantPropagationTerm l
                                          r_op <- constantPropagationTerm r
                                          return $ App p l_op r_op
constantPropagationTerm (Fix p f fty x xty t) = do  t_op <- constantPropagationTerm t
                                                    return $ Fix p f fty x xty t_op
constantPropagationTerm (IfZ p c t e) = do  c_op <- constantPropagationTerm c
                                            t_op <- constantPropagationTerm t
                                            e_op <- constantPropagationTerm e
                                            return $ IfZ p c_op t_op e_op
constantPropagationTerm (Print p str t) = do  t_op <- constantPropagationTerm t
                                              return $ Print p str t_op
constantPropagationTerm (BinaryOp p op t u) = do  t_op <- constantPropagationTerm t
                                                  u_op <- constantPropagationTerm u
                                                  return $ BinaryOp p op t_op u_op
constantPropagationTerm t = return t

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