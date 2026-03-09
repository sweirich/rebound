{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Tutorial.Simple.CPS where

import Tutorial.Simple.Syntax
import Data.Vec ( (!) ) 
import Tutorial.Simple.Gen
import Tutorial.Named.PP

-- prop = forAllShow arbitrary

-- CBV CPS translation (naive)
--
-- [[x]] k = k x
-- [[\x.e]] k = k (\x.\xk. [[e]] xk)
-- [[e1 e2]] k = [[e1]] \x. [[e2]] \y. x y k
-- [[unit]] k = k unit
-- [[(e1, e2)]] k = [[e1]] \x. [[e2]] \y. k (x,y)
-- [[case p of (x1,y1) -> e]] k = [[p]] (\z. case z of (x1,y1) -> [[e]] k)
-- [[inj i e]] k = [[e]] \x. k (inj i x)
-- [[case e of (inj i -> ei)]] k = [[e]] (\z. case z of inj i -> [[ei]] k)


cps :: Tm Z -> Tm Z
cps e = cpsExp CpsStart e (Meta (bind1 wildcardName (Var FZ))) 

contName :: LocalName
contName = LocalName "k"

data Cont (g :: Nat) where
  Obj   :: Tm g  -> Cont g
  Meta  :: Bind1 Tm Tm g -> Cont g
    deriving (Generic1)

applyCont :: Cont g -> Tm g -> Tm g
applyCont (Obj o)  v  = App o v
applyCont (Meta k) v  = instantiate1 k v

reifyCont :: Cont g -> Tm g 
reifyCont (Obj o)   = o
reifyCont (Meta k)  = Lam k

instance Subst Tm Cont where

data CpsCtx g g' where

  CpsStart  :: CpsCtx N0 N0
  -- Empty context

  CpsLam   :: CpsCtx g g' -> CpsCtx (S g) (S (S g'))
  -- Context in the body of Lam. The input has the type
  -- of the parameter and the output has both its converted
  -- type and a continuation. 

  CpsMeta   :: CpsCtx g g' -> CpsCtx (S g) (S g')
  -- Context in the body of Meta. The input has the type
  -- of the parameter and the output has the converted type.
          

cpsIdx :: CpsCtx g g' -> Fin g -> Fin g' 
cpsIdx CpsStart v = case v of {}
cpsIdx (CpsLam gg)  FZ      = FS FZ
cpsIdx (CpsLam gg)  (FS v)  = FS (FS (cpsIdx gg v))
cpsIdx (CpsMeta gg) FZ      = FZ
cpsIdx (CpsMeta gg) (FS v)  = FS (cpsIdx gg v)

weaken :: Env Tm n (S n)
weaken = shift1E

cpsExp :: forall g g'.  CpsCtx g g' -> Tm g -> Cont g'  -> Tm g' 
cpsExp g (Var v)  k = applyCont k (Var (cpsIdx g v))
cpsExp g (Unit)   k = applyCont k Unit
cpsExp g (Lam b)  k =
  let   e'  = Lam . bind1 (getLocalName b)
               $ Lam . bind1 contName
                 $ cpsExp (CpsLam g) (getBody1 b) k'
  
        k'  = Obj $ Var FZ
  
      in
        applyCont k e'    
cpsExp g (Pair e1 e2) k = 
  let k1 :: Cont g'
      k1 = Meta . bind1 contName $ cpsExp (CpsMeta g) (applyE weaken e2) k2
      k2 :: Cont (S g')
      k2 = Meta . bind1 contName $ applyCont k' (Pair (Var (FS FZ)) (Var FZ)) 

      k' = applyE (weaken .>> weaken) k
  in 
    cpsExp g e1 k1

cpsExp g (App e1 e2)  k =
    let      
         k1 :: Cont g' 
         k1 = Meta . bind1 contName $ cpsExp (CpsMeta g) (applyE weaken e2) k2
   
         k2 :: Cont (S g') 
         k2 =  Meta . bind1 contName $ App (App (Var (FS FZ)) (Var FZ))
                (reifyCont (applyE (weaken .>> weaken) k))
     in
       cpsExp g e1 k1

cpsExp g (MatchPair e1 b) k = 
  let b' = getBody2 b
      g' = CpsMeta (CpsMeta g)
      k' = applyE (weaken .>> weaken) k
      b'' = bind2 x1 x2 (cpsExp g' b' k')
      x1 = names ! FZ
      x2 = names ! FS FZ
      names = getLocalName2 b
      k1 = Meta . bind1 contName $ MatchPair (Var FZ) (applyE weaken b'')
  in
      cpsExp g e1 k1
cpsExp g (Inj i e) k = 
  cpsExp g e (Meta . bind1 contName $ applyCont (applyE weaken k) (Inj i (Var FZ)))
