In this module we will define our language constructs.
```agda
module Language.Definition where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)

open import Language.Types
open import Language.Contexts
```

First, we define some variables that will be used throughout the module.
```agda
private
    variable
        δ : FContext
        γ : Context
        A B C : Type
        ft : FType
```

We also have to inform Agda what mixfix operators we will be defining in this module.
```agda
infix  4 _×_⊢_
```

Our language expressions are defined by the environments they are evaluated in
and the type they return. For this language definition we take some inspiration
from the language defined in the
[DeBruijn chapter](https://plfa.github.io/DeBruijn/) of the PLFA book.
```agda
data _×_⊢_ : FContext → Context → Type → Set where
```

For booleans the constructor takes an Agda boolean value and returns an 
expressions that in any contexts will return a boolean type.
```agda
    bool   : Bool
           --------------
           → δ × γ ⊢ tyBool
```

This same concept is applied to natural numbers, but instead of taking and
returning booleans it of course uses natural numbers.
```agda

    nat    : ℕ
           --------------
           → δ × γ ⊢ tyNat
```

The plus constructor takes two other expressions as arguments. These expressions
have to be evaluated in the same contexts as the plus expression returned and
should both return natural numbers. The created plus expression will also return
a natural number.
```agda
    plus   : δ × γ ⊢ tyNat
           → δ × γ ⊢ tyNat
           --------------
           → δ × γ ⊢ tyNat
```

**Mult**iplication works in the same way as the plus expression. The only difference
between these two is in the semantics defined later.
```agda
    mult   : δ × γ ⊢ tyNat
           → δ × γ ⊢ tyNat
           --------------
           → δ × γ ⊢ tyNat
```

The less-than expression is similar to the other binary operators we have defined
thus far, but instead of returning a natural number it will return a boolean
value.
```agda
    lt     : δ × γ ⊢ tyNat
           → δ × γ ⊢ tyNat
           --------------
           → δ × γ ⊢ tyBool
```

The `and` and `or` constructors function in much the same way as the `plus` and
`mult` constructors, but using boolean instead of natural number types.
```agda
    and    : δ × γ ⊢ tyBool
           → δ × γ ⊢ tyBool
           --------------
           → δ × γ ⊢ tyBool

    or     : δ × γ ⊢ tyBool
           → δ × γ ⊢ tyBool
           --------------
           → δ × γ ⊢ tyBool

```

Negation is the only unary operator in our language. It takes some expression
evaluating to a boolean type and will return a boolean type.
```agda
    neg    : δ × γ ⊢ tyBool
           --------------
           → δ × γ ⊢ tyBool
```

The `var` constructor takes a lookup into an environment and returns the type at
that location in the environment.
```agda
    var    : γ ∋ A
           --------------
           → δ × γ ⊢ A
```

Lambda expressions are used to create a function from type `A` to `B` in our
language. It takes one argument, an expression that will be evaluated in the same
context as the lambda, but with the type `A` appended to it. This expression must
return type `B`.

```agda
    lambda : δ × γ , A ⊢ B
           --------------
           → δ × γ ⊢ (A ⇒ B)
```

The `appl` (function **appl**ication) constructor takes two arguments. The first
is an expression that evaluates to a function type from `A` to `B`. The second is
is an expression that evaluates to the type `A`. It will then use these two
expressions to produce the type `B`.
```agda
    appl   : δ × γ ⊢ (A ⇒ B)
           → δ × γ ⊢ A
           --------------
           → δ × γ ⊢ B
```

The `fdef` (**f**unction **def**inition) constructor is used to store a function
type in the function environment. It takes two expressions as arguments. The
first is the function to store in the context and the second is the rest of the
program that will have access to this function value in the new context.
```agda
    fdef   : δ × γ ⊢ (A ⇒ B)
           → (δ ,ᶠ (A ⇒ᶠ B)) × γ ⊢ C
           --------------
           → δ × γ ⊢ C
```

The `fvar` constructor is similar to the `var` constructor, but instead of taking
a value from the normal context it takes it from the function context.
```agda
    fvar   : δ ∋ᶠ ft
           --------------
           → δ × γ ⊢ (FType-to-Type ft)
```

Finally, the `newCtx` constructor can be used to evaluate an expression in a
completely fresh context with no variables or functions bound.
```agda
    newCtx : ∅ᶠ × ∅ ⊢ A
           --------------
           → δ × γ ⊢ A
```
