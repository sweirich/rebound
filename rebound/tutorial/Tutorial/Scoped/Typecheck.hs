module Tutorial.Scoped.Typecheck where

import Tutorial.Scoped.Syntax hiding (Ctx)

-- * Typing contexts

-- | a typing context is a total map for all free variables in scope
type Ctx n = Fin n -> Ty

-- | the empty context has an empty domain
emptyCtx :: Ctx Z
emptyCtx = \x -> case x of {}

-- | extend a context with a new type, enlarging its domain
(+%) :: Ctx n -> Ty -> Ctx (S n)
(+%) g a = \x -> case x of { FZ -> a ; FS y -> g y }


-- * Bidirectional type checking 
-- tiTm (type inference) /tcTm (type check) work together 

-- | Infer the type of a term
tiTm :: Ctx n -> Tm n -> Either String Ty

tiTm g (Ann v a) = do
    tcTm g v a 
    return a

tiTm g (Var x) = return (g x)

tiTm g Unit = return One

tiTm g (Pair v1 v2) = do 
    a1 <- tiTm g v1 
    a2 <- tiTm g v2 
    return (a1 :* a2)

tiTm g (App m v) = do
    c <- tiTm g m 
    case c of
        a :-> b -> do
            tcTm g v a
            return b
        _ -> Left "type error"

tiTm g (MatchUnit v m) = do
    tcTm g v One
    tiTm g m 

tiTm g (MatchPair v m) = do
    a <- tiTm g v
    case a of 
        a1 :* a2 -> tiTm ((g +% a1) +% a2) (getBody2 m) 
        _ -> Left "type error"

tiTm g (MatchSum v m1 m2) = do
    a <- tiTm g v
    case a of 
        a1 :+ a2 -> do 
            b1 <- tiTm (g +% a1) (getBody1 m1)
            b2 <- tiTm (g +% a2) (getBody1 m2)
            if b1 == b2 then return b1 else Left "type error"
        _ -> Left "type error"

tiTm g (Inj _ _) = 
    Left "annotation needed for inject"
tiTm g (Lam m) = 
    Left "annotation needed for lambda"



-- | Check the type of a value
tcTm :: Ctx n -> Tm n -> Ty -> Either String ()
tcTm g (Lam m) (a :-> b) = 
    tcTm (g +% a) (getBody1 m) b

tcTm g (Pair v1 v2) (a1 :* a2) = do 
    tcTm g v1 a1
    tcTm g v2 a2

tcTm g (Inj 0 v1)   (a1 :+ a2) = tcTm g v1 a1

tcTm g (Inj 1 v1)   (a1 :+ a2) = tcTm g v1 a2

tcTm g (App m v) b = do
    a <- tiTm g v
    tcTm g m (a :-> b)

tcTm g (MatchUnit v m) b = do
    tcTm g v One
    tcTm g m b

tcTm g (MatchPair v m) b = do
    a <- tiTm g v
    case a of 
        (a1 :* a2) -> tcTm ((g +% a1) +% a2) (getBody2 m) b
        _ -> Left "type error"

tcTm g (MatchSum v m1 m2) b = do
    a <- tiTm g v
    case a of 
        (a1 :+ a2) -> do 
            tcTm (g +% a1) (getBody1 m1) b 
            tcTm (g +% a2) (getBody1 m2) b
        _ -> Left "type error"

-- includes Unit, Ann, 
tcTm g m b2 = do
    b1 <- tiTm g m
    if b1 == b2 then 
       return ()
    else 
       Left "type error"
