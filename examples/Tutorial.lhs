> module Tutorial where

> import AutoEnv.Lib

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
> a .: r = \ case
>             FZ -> a 
>             FS y -> r y

The only other modification that we need to make to the above 
definition is that in the `Lam` case, we need *compose* the 
current environment with the suspended environment in the 
lambda expression. We do so with the `(.>>)` operator below.

< (.>>) :: (Fin m  -> Exp n) -> (Fin n -> Exp p) -> (Fin m -> Exp p)
< v1 .>> v2 = applyE v2 . v1

Composition of delayed substitutions means that we need to 
apply the second substitution to all terms in the co-domain
of the first. 

< applyE :: (Fin n1 -> Exp n2) -> Exp n1 -> Exp n2
< applyE r (Var x) = r x
< applyE r (Lam (Bind r' b)) = Lam (Bind (r' .>> r) b)
< applyE r (App a1 a2) = App (applyE r a1) (applyE r a2)

Alpha-equivalence
-----------------

Because we have a way to apply a delayed substituion, we can 
implement alpha-equivalence. To do so, we first implement 
a function that forces the delayed substitution, called `unbind`
which substitutes through the body of the binder. 

> unbind (Bind r a) = applyE (up r) a

However, there is a catch: we have to first modify the delayed 
substitution so that its domain and co-domain correspond to the 
extended scope of the binder. The `up` function, shown below
does this transformation.

< up :: (Fin n -> Exp m) -> (Fin (S n) -> Exp (S m))
< up e = \case
<           FZ -> Var f0   -- leave binding variable alone
<           FS f -> applyE (Var . FS) (e f) -- shift indices under the binder

With `unbind`, we can define alpha-equality for binders and 
expressions succinctly. 

> instance Eq (BindExp n) where
>    b1 == b2 = unbind b1 == unbind b2

> deriving instance (Eq (Exp n))

An Implicit Environment-passing Implementation
----------------------------------------------

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
>       Lam b -> let a2' = eval2 a2 in eval2 (instantiate b a2')
>       _ -> error "should be a lambda"

The `instantiate` function extends the delayed substitution in 
the binder with the substitution for the argument, and then 
immediately applies it to the term. (Recall that in the definition 
of `applyE`, when the substitution reaches *another* binder, it 
will be delayed there.)

> instantiate :: BindExp n -> Exp n -> Exp n
> instantiate (Bind r a) v = applyE (v .: r) a

This version of the evaluator is simpler than the version above, but 
is slightly less efficient, due to the fact that it applies substitutions
(slightly) more eagerly and because values are "evaluated" twice. Wherever 
a value is substituted for a variable by `instantiate`, that value will 
be the argument to `eval`. This is not a significant cost, because
the only values are function values, they can always be evaluated in 
constant time. 

Making the library do the heavy lifting
---------------------------------------

The above definitions are specialized for the type `Exp`. While some operations, such 
as `(.:)` can be made more generic by abstracting `Exp`, for others, we need 
to know how to traverse the expression (with `applyE`) and how to create an 
expression out of an index (with `Var`). By using typeclasses to overload 
these two operations, we can develop a generic library. 

> class SubstVar (e :: Nat -> Type) where
>    var :: Fin n -> e n

> instance SubstVar Exp where var = Var

The `Subst` type class takes two arguments. The first, `v` describes the 
co-domain of the deferred substitution (i.e. what type do variables 
stand for) and the second `e` describes what type we are substituting
into.

> class (SubstVar v) => Subst (v :: Nat -> Type) (e :: Nat -> Type) where
>    applyE :: (Fin m -> v n) -> e m -> e n


Often, these two types will be the same. For example, in the 
lambda calculus, we can replace variables by `Exp`, when substituting
by an `Exp` with this instance.

> instance Subst Exp Exp where
>   applyE r (Var x) = r x
>   applyE r (Lam b) = Lam (applyE r b)
>   applyE r (App a1 a2) = App (applyE r a1) (applyE r a2)

These two classes are all that we need to create generic versions of the 
operations used above such as `(.>>)` and `up`. 

> (.>>) :: Subst v e => (Fin m -> e n) -> (Fin n -> v p) -> (Fin m -> e p)
> r1 .>> r2 = applyE r2 . r1

> up :: forall v n m. (Subst v v) => (Fin n -> v m) -> (Fin (S n) -> v (S m))
> up e = \case  
>           FZ -> var f0   -- leave binding variable alone
>           FS f -> applyE (var @v . FS) (e f) -- shift indices under the binder

Furthermore, by creating a new type for binders

> data Bind v e n where
>     Bind :: (Fin m -> v n) -> e (S m) -> Bind v e n

that generalizes our previous definition

> type BindExp = Bind Exp Exp

we can make an instance of the `Subst` class for `Bind`. This instance
simplifies the definition of `applyE` in the `Lam case above.

> instance Subst v v => Subst v (Bind v e) where
>    applyE r (Bind r' b) = Bind (r' .>> r) b

We also have a "smart constructor" to construct binders.

> bind :: SubstVar v => e (S n) -> Bind v e n
> bind = Bind var

Developing a reusable library also gives us a chance to make the environment 
type abstract. 

> type Env e m n = Fin m -> e n

And develop some environment-aware operations. For example, we may wish to instantiate
a binder in the context of a function that is parameterized by an environment. In this 
case, the definition is shorter than the type, but captures the idea, that we want to 
pass the stored environment to the function along with the body of the binder, at the same 
time as extending it with a value for the bound variable.

> -- | instantiate 
> instantiateWith :: (forall m n. (Fin m -> v n) -> e m -> e n) -> Bind v e n -> v n -> e n
> instantiateWith f (Bind r a) v = f (v .: r) a

This library function is exactly what we need to rewrite the environment-based interpreter
while keeping the `Bind` and `Env` types abstract.

> evalE :: Env Exp m n -> Exp m -> Exp n
> evalE r (Var x)  = r x
> evalE r (Lam bnd) = Lam (applyE r bnd)
> evalE r (App a1 a2) =
>     case eval r a1 of 
>       Lam bnd -> let v = eval r a2 in instantiateWith evalE bnd v
>       _ -> error "should be a lambda"

Strong reduction
----------------

What about reducing under binders? How can we do that 
efficiently? What sort of interface do we need from the binding 
library to implement this succinctly?

The main difference between evaluation (`eval2` above) and the
normalization function (`nf` below), is that this code calls itself 
recursively in the body of the lambda expression. We already have 
the functionality to write this code nicely: the `unbind` and 
`bind` functions let us lift the normalization function for expressions
to binders.

> -- | Calculate the beta-normal form with an *implicit* environment
> nf :: Exp n -> Exp n
> nf (Var x) = Var x
> nf (Lam b) = Lam (bind . nf . unbind $ b)
> nf (App a1 a2) =
>   let a2' = nf a2 in
>   case nf a1 of
>      Lam b -> nf (instantiate b a2')
>      a1' -> App a1' a2'

But the `bind . nf . unbind` dance is inefficient. With `unbind` we
have to apply the stored substitution to the body, then with `nf` we 
normalize the body, and the recreate the binder with an identity 
substitution.  

Now let's consider a version with an explicit environment. By passing 
an environment as another argument of the evaluator, we can compose 
it with the stored environment in the binder, instead of applying it.

< -- | Calculate the beta-normal form with an explicit environment
< norm :: (Fin m -> Exp n) -> Exp m -> Exp n
< norm r (Var x) = r x
< norm r (Lam (Bind r' a')) = Lam (bind (norm (up (r' .>> r)) a'))
< norm r (App a1 a2) = 
<   let a2' = norm r a2 in
<   case norm r a of
<      Lam (Bind r' a') -> norm (a2' .: r') a'
<      a1' -> App a1' a2'

And, by defining a few library functions, we can encapsulate the 
environment manipulation.

> -- | Calculate the beta-normal form with an explicit environment
> norm :: Env Exp m n -> Exp m -> Exp n
> norm r (Var x) = r x
> norm r (Lam b) = Lam (applyUnderEnv norm r b)
> norm r (App a1 a2) = 
>   let a2' = norm r a2 in
>   case norm r a1 of
>      Lam b -> instantiateWith norm b a2'
>      a1' -> App a1' a2'


> -- | apply an environment-parameterized function & environment
> -- underneath a binder
> applyUnderEnv :: (Subst v v, Subst v c) =>
>    (forall m n. Env v m n -> c m -> c n) ->
>    Env v n1 n2 -> Bind v c n1 -> Bind v c n2
> applyUnderEnv f r2 (Bind r1 t) = Bind var (f (up (r1 .>> r2)) t)



