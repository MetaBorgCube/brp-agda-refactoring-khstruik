This module defines the environments and values contained in them for use by our
language.
```agda
module Language.Environments where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)

open import Language.Contexts
open import Language.Definition
open import Language.Types
```

First, we define some variables that will be used throughout the module.
```agda
private
    variable
        δ : FContext
        γ : Context
        argT retT t : Type
        ft : FType
```

Within this module we will define the following infix operators.
```agda
infixl 5 _,'_
infixl 5 _,ᶠ'_
```

Since we will use environments in the definition of values we need to define
their types first.
```agda
data Env : Context → Set
data FEnv : FContext → Set
```

Expressions in our language can produce three different types of values. Natural
numbers (`natV`), booleans (`boolV`), and function values (`funcV`). Function
values are closures. This means that they contain a copy of the environment they
where originally defined in for use with the execution of the expression stored
within.
```agda
data Val : Type → Set where
    natV  : ℕ → Val tyNat
    boolV : Bool → Val tyBool
    funcV : Env γ → FEnv δ → δ × γ , argT ⊢ retT → Val (argT ⇒ retT)
```

Since we now have a definition of values, we can complete our definition of
environments. Environments contain a context that they are based on. Each value
stored in the environment has to have the same type as the context contains at
the same position.
```agda
data Env where
    ∅' : Env ∅
    _,'_ : Env γ → Val t → Env (γ , t) 
    
data FEnv where
    ∅ᶠ' : FEnv ∅ᶠ
    _,ᶠ'_ : FEnv δ → Val (FType-to-Type ft) → FEnv (δ ,ᶠ ft)
```

To retrieve values from an environment we can use context lookups of the
associated context. For this we define the following lookup functions.

```agda
env-lookup : Env γ → (l : γ ∋ t) → Val t
env-lookup (γ ,' v) Z = v
env-lookup (γ ,' v) (S l) = env-lookup γ l

fenv-lookup : FEnv δ → δ ∋ᶠ ft → Val (FType-to-Type ft)
fenv-lookup (δ ,ᶠ' v) Zᶠ = v
fenv-lookup (δ ,ᶠ' v) (Sᶠ l) = fenv-lookup δ l
```
