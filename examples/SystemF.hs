-- | This is an example of the use of the library with two separate variable types
module SystemF where

{- One issue with this example is that we only store one sort of environment at each binder. 
   However, terms are subject to two different forms of substitution --- either for terms or types.
   So, applying the "wrong" sort through a binder means that we don't gain any advantage from 
   the caching --- we need to bind and unbind the to propagate.

-}

import AutoEnv
import AutoEnv.Bind.Single
import AutoEnv.Context

data Ty (n :: Nat) where
    TVar :: Fin n -> Ty n
    TAll :: Bind Ty Ty n -> Ty n
    TArr :: Ty n -> Ty n -> Ty n

-- swap the order of the scopes so that we can talk about 
-- substituting a type inside of an expression
newtype TyExp n m = TyExp { unTyExp :: Exp m n }

data Exp (m :: Nat) (n :: Nat) where
    EVar  :: Fin n -> Exp m n
    ELam  :: Ty m -> Bind (Exp m) (Exp m) n -> Exp m n 
    EApp  :: Exp m n -> Exp m n -> Exp m n
    ETLam :: Bind Ty (TyExp n) m -> Exp m n
    ETApp :: Exp m n -> Ty m -> Exp m n

instance SubstVar Ty where
    var = TVar 
instance Subst Ty Ty where
    applyE r (TVar x) = applyEnv r x
    applyE r (TAll b) = TAll (applyE r b)
    applyE r (TArr t1 t2) = TArr (applyE r t1) (applyE r t2)

instance SubstVar (Exp m) where
    var = EVar

-- apply type substitution to an expression, using the newtype
substTy :: Env Ty m1 m2 -> Exp m1 n -> Exp m2 n
substTy r e = unTyExp (applyE r (TyExp e))

instance Subst Ty (TyExp n) where
    applyE :: forall m1 m2 n. Env Ty m1 m2 -> TyExp n m1 -> TyExp n m2
    applyE r (TyExp (EVar x)) = TyExp (EVar x)
    applyE r (TyExp (ELam ty b)) = 
        let q = substTy r (unbind b)
        in TyExp (ELam (applyE r ty) (bind q))
    applyE r (TyExp (EApp e1 e2)) = TyExp (EApp (substTy r e1) (substTy r e2))
    applyE r (TyExp (ETLam b)) = 
        let q = applyE (up r) (unbind b)
        in TyExp (ETLam (bind q))
    applyE r (TyExp (ETApp e1 t2)) = 
        TyExp (ETApp (substTy r e1) (applyE r t2))

-- | shift the type scope in the range of a term substiution
upTyScope :: Env (Exp m) n1 n2 -> Env (Exp (S m)) n1 n2
upTyScope = transform (substTy shift1E)
    
instance Subst (Exp m) (Exp m) where
    applyE :: forall m n1 n2. Env (Exp m) n1 n2 -> Exp m n1 -> Exp m n2
    applyE r (EVar x) = applyEnv r x
    applyE r (ELam ty b) = ELam ty (applyE r b)
    applyE r (EApp t1 t2) = EApp (applyE r t1) (applyE r t2)
    applyE r (ETLam b) =
        let (TyExp te) = unbind b 
        in ETLam (bind (TyExp (applyE (upTyScope r) te)))
    applyE r (ETApp e t) = ETApp (applyE r e) t    


