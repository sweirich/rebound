> module Tutorial where

> import AutoEnv.Lib
> import Data.Vec

This is *beautiful* code. It is an evaluator for lambda-calculus
expressions, where bound variables are represented by de Bruijn
indices (of type `Fin n`). The is expression type is indexed 
by a *scope*, which is a bound of the largest index that appears
in the term.

< -- | Lambda calculus expressions, including variables, 
< -- abstractions and applications.
< data Exp :: Nat -> Type where 
<    Var :: Fin n -> Exp n 
<    Lam :: Exp (S n) -> Exp n
<    App :: Exp n -> Exp n -> Exp n
<  deriving (Show)

< -- | An environment, or length indexed vector of values
< -- The value at position i is a substitution for the
< -- variable with index i.
< type Env n = Vec n Val 

< -- | Closed lambda expression, pairing the body of a 
< -- first-class function with definitions for all of its
< -- free variables.
< data Val where
<    Closure :: Env n -> Exp (S n) -> Val

< -- | Environment-based interpreter, computes the value 
< -- of every lambda-expression
< eval :: Env n -> Exp n -> Val
< eval r (Var x)  = r ! x
< eval r (Lam b)  = Closure r b   
< eval r (App a1 a2) =
<     case eval r a1 of 
<       Closure r' b -> let v = eval r a2 in eval (v ::: r') b

This code is beautiful because everything fits together perfectly. Using 
de Bruijn indices means that all alpha-equivalent lambda expressions 
have the same representation. The scope index for the `Exp` type tracks
how big the environment needs to be to evaluate the expression. (When 
the index is zero, the type only represents *closed* expressions, 
those that do not have any free variables.) The evaluator works 
cleanly: even though we are using indices to represent variables, 
there is no shifting or substitution required. Instead, the environment 
does all of the work: delaying the substitution until the very last moment. 

However, despite our initial enthusiasm there are a few problems with this 
definition. 

1. What if we wanted normalization (i.e. reduction under lambdas) instead of 
   evaluation (i.e. only top-level reduction)? Our "trick" of saving the 
   environment in the closure won't work. We need to keep going! But how 
   do we do that while retaining efficient execution?

2. Alpha-equivalent lambda-expressions have a unique representation, so 
   the derivable definition of `(==)` suffices. However, the same is not 
   true of closure values. Both of these represent the same lambda value
   (`\x -> \y -> y`), but they are not equal. 

< c1 = Closure VNil (Lam (Var f0))

< c2 = Closure (Lam (Var f0) ::: VNil) (Var f0)
 
3. In our evaluation function, we need to explicitly pass around an environment 
   and store the delayed environment in a closure. That doesn't look like the 
   lambda-calculus. What if we wanted an evaluator that looks more like a 
   research paper? And what if we were not modeling an evaluator, but some other 
   reduction semantics? In that case, having a separate value type is not what 
   we want.

Key observation: The fundamental mechanism of this code is the *closure*, i.e.
a lambda-expression that includes a *delayed* substitution. Let's take just this 
idea to see if we can bring some of the benefits of an evaluation-based interpreter
to a substitution-based implementation.

Substitution(?)-based interpreter
------------------------------

In this version, we create a type for binders, i.e. expressions with a 
single free variable and a delayed substitution. For convenience, we represent
the delayed substitution as a function from indices to expression. 

<         Fin m -> Exp n   -- indices bounded by m to expressions in scope n

Unlike closures, which restrict the co-domain of the environment to closed 
values, in this version we allow the co-domain to include be arbitrary 
expressions, that may not be closed. We therefore index the type of the 
binder with this scope.

< -- single binder, includes a delayed substitution for
< -- the free variables in the body of the expression 
< data BindExp n where
<     Bind :: (Fin m -> Exp n) -> Exp (S m) -> Bind n

Now we use this type for lambda expressions in our representation
of expressions. Note that we cannot use the derivable equality 
for alpha-equivalence for `Bind`. Instead, we will make an instance
below that forces the delayed substitution.

> -- | Lambda calculus expressions, including variables, 
> -- abstractions and applications
> data Exp :: Nat -> Type where 
>    Var :: Fin n -> Exp n 
>    Lam :: BindExp n -> Exp n
>    App :: Exp n -> Exp n -> Exp n

Now let's revise the evaluator above to work with this new 
datatype. Instead of producing a (closed) value, the result
of this function is a new expression, with scope determined
by the environment. 

> eval :: (Fin m -> Exp n) -> Exp m -> Exp n
> eval r (Var x)  = r x
> eval r (Lam (Bind r' b)) = Lam (Bind (r' .>> r) b)
> eval r (App a1 a2) =
>     case eval r a1 of 
>       Lam (Bind r' b) -> let v = eval r a2 in eval (v .: r') b
>       _ -> error "should be a lambda"

In the application case, as above, we need to extend the environment
with a definition for the argument of the function. This corresponds
to defining a "cons"-like operator for our function-based environments.

> (.:) :: e n -> (Fin m -> e n) -> (Fin (S m) -> e n)
> a .: r = \ x -> case x of 
>                    FZ -> a 
>                    FS y -> r y

The only other modification that we need to make to the above 
definition is that in the `Lam` case, we need *compose* the 
current environment with the suspended environment in the 
lambda expression. We do so with the `(.>>)` operator below.

> (.>>) :: (Fin m  -> Exp n) -> (Fin n -> Exp p) -> (Fin m -> Exp p)
> v1 .>> v2 = subst v2 . v1

Composition of delayed substitutions means that we need to 
apply the second substitution to all terms in the co-domain
of the first environment. 

< subst :: (Fin n1 -> Exp n2) -> Exp n1 -> Exp n2
< subst r (Var x) = r x
< subst r (Lam (Bind r' b)) = Lam (Bind (r' .>> r) b)
< subst r (App a1 a2) = App (subst r a1) (subst r a2)

Alpha-equivalence
-----------------

Because we have a way to apply a delayed substituion, we can 
implement alpha-equivalence. To do so, we first implement 
a function that forces the delayed substitution, called `unbind`
which substitutes through the body of the binder. 

> unbind (Bind r a) = subst (up r) a

However, there is a catch: we have to first modify the delayed 
substitution so that its domain and co-domain correspond to the 
extended scope of the binder. The `up` function, shown below
does this transformation.

> up :: (Fin n -> Exp m) -> (Fin (S n) -> Exp (S m))
> up e = \x -> case x of 
>                FZ -> Var f0   -- leave binding variable alone
>                FS f -> subst (Var . FS) (e f) -- shift the indices as we go under the binder

With the definition of `unbind`, we can define equality for binders and 
expressions succinctly. 

> instance Eq (BindExp n) where
>    b1 == b2 = unbind b1 == unbind b2

> deriving instance (Eq (Exp n))

Implicit/slightly-less-delayed environment
----------------------

We can simplify our definition of the evaluator so that it looks 
even more like a substitution-based implementation. In the version, 
we don't need to manipulate a delayed substitution as an argument to the 
function. However, we still use the `Bind` operator to store a delayed
substitution in lambda expressions. This delayed substitution is 
not visible in the code below: the `instantiate` function, used
during beta-reduction, does all such manipulation behind the scenes.

> eval2 :: Exp n -> Exp n
> eval2 (Var x) = Var x
> eval2 (Lam b) = Lam b
> eval2 (App a1 a2) =
>     case eval2 a1 of 
>       Lam b -> let v = eval2 a2 in eval2 (instantiate b v)
>       _ -> error "should be a lambda"

The `instantiate` function extends the delayed substitution in 
the binder with the substitution for the argument, and then 
immediately applies it to the term. (Recall that in the definition 
of `subst`, when the substitution reaches *another* binder, it 
will be delayed there.)

> instantiate :: BindExp n -> Exp n -> Exp n
> instantiate (Bind r a) v = subst (v .: r) a

This version of the evaluator is simpler than the version above, but 
is slightly less efficient, due to the fact that it applies substitutions
(slightly) more eagerly and because values are "evaluated" twice. Wherever 
a value is substituted for a variable by `instantiate`, that value will 
be the argument to `eval`. This is not a significant cost, because
the only values are function values, they can always be evaluated in 
constant time. 

Making the library do the heavy lifting
---------------------------------------

The above above are specialized for the type `Exp`. While some operations, such 
as `(.:)` can be made more generic by abstracting `Exp`, for others, we need 
to know how to traverse the expression (with `subst`) and how to create an 
expression out of an index (with `Var`). By using typeclasses to overload 
these two operations, we can develop a generic library. 

> class SubstVar (e :: Nat -> Type) where
>    var :: Fin n -> e n

> instance SubstVar Exp where var = Var

> class Subst (e :: Nat -> Type) where
>    subst :: (Fin m -> e n) -> e m -> e n

> instance Subst Exp where
>   subst r (Var x) = r x
>   subst r (Lam (Bind r' b)) = Lam (Bind (r' .>> r) b)
>   subst r (App a1 a2) = App (subst r a1) (subst r a2)

These two classes are all that we need to create generic versions of the 
operations used above such as `(.>>)` and `up`. Furthermore, by also creating 
a new type for binders

> data Bind e n where
>     Bind :: (Fin m -> e n) -> e (S m) -> Bind e n

that generalizes our previous definition.

> type BindExp = Bind Exp

Developing a reusable library also gives us a chance to make the environment 
type abstract. 

> type Env e m n = Fin m -> e n






Normalization
-------------

What about reducing under binders? How can we do that the most 
efficiently?

> -- | Calculate the normal for with an explicit environment
> norm :: (Fin m -> Exp n) -> Exp m -> Exp n
> norm r (Var x) = r x
> norm r (Lam (Bind r' b)) = 
>     Lam (Bind var (norm (up (r' .>> r)) b))
> norm r (App a b) = App (norm r a) (norm r b)

> -- | Calculate the normal form with an *implicit* environment
> nf :: Exp n -> Exp n
> nf (Var x) = Var x
> nf (Lam b) = Lam (Bind var (nf (unbind b)))
> nf (App e1 e2) =
>   case nf e1 of
>      Lam b -> nf (instantiate b (nf e2))
>      t -> App t (nf e2)

> {-
> -- delay both *substitution* and *normalization* 
> -- when we get to a binder
> data Ne n where
>   NeVar :: Fin n -> Ne n
>   NeApp :: Ne n -> Nf n -> Ne n
> data Nf n where
>   NfNe  :: Ne n -> Nf n
>   NfLam :: Bind n -> Nf n

> toNf :: (Fin m -> Nf n) -> Exp m -> Nf n
> toNf r (Var x) = r x
> toNf r (Lam (Bind r' b)) = Lam (Bind r'' b) where
>    r'' = \x -> toNf r (r' x)
> toNf r (App a1 a2) = 
>     let nf2 = toNf r a2 in
>     case toNf r a1 of 
>        NfNe ne -> NfNe (NeApp ne nf2)
>        NfLam (Bind r' b) -> toNf (nf2 .: r'') b where
>            r'' = toNf (NfNe . NeVar) . r'
> -}

