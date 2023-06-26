In this module we define the big-step semantics for our language.
```agda
module Language.Semantics where

open import Data.Nat using (ℕ; _+_; _*_; _<ᵇ_)
open import Data.Bool using (Bool; not; _∨_; _∧_)

open import Language.Contexts
open import Language.Definition
open import Language.Environments
open import Language.Types
```

Throughout the definition of our semantics we will use the following variables.
```agda
private
    variable
        δ β : FContext
        γ σ : Context
        Δ : FEnv δ
        Γ : Env γ
        Β : FEnv β
        Σ : Env σ
        t A B argT retT : Type
        Aᶠ Bᶠ : FType
        n : ℕ
        b : Bool
```

The evaluation of an expression in our language is expressed using the following
data type. It is loosely based on the big-step semantics explained in the
[BigStep chapter](https://plfa.github.io/BigStep/) of the PLFA book.
```agda
data _×_⊢_↓_ : FEnv δ → Env γ → (δ × γ ⊢ t) → Val t → Set where
```

The evaluation for `nat` and `bool` expressions simply takes the stored value and
creates a corresponding value type with the same value in any environment.
```agda
    ↓nat  : Δ × Γ ⊢ nat n ↓ natV n
    ↓bool : Δ × Γ ⊢ bool b ↓ boolV b
```

All the binary operators take evaluations for both their arguments and combine
those values using their respective operators.
```agda
    ↓plus : ∀ {v₁ v₂} {e₁ e₂ : δ × γ ⊢ tyNat}
          → Δ × Γ ⊢ e₁ ↓ (natV v₁)
          → Δ × Γ ⊢ e₂ ↓ (natV v₂)
          → Δ × Γ ⊢ (plus e₁ e₂) ↓ (natV (v₁ + v₂))
    ↓mult : ∀ {v₁ v₂} {e₁ e₂ : δ × γ ⊢ tyNat}
          → Δ × Γ ⊢ e₁ ↓ (natV v₁)
          → Δ × Γ ⊢ e₂ ↓ (natV v₂)
          → Δ × Γ ⊢ (mult e₁ e₂) ↓ (natV (v₁ * v₂))
    ↓lt : ∀ {v₁ v₂} {e₁ e₂ : δ × γ ⊢ tyNat}
        → Δ × Γ ⊢ e₁ ↓ (natV v₁)
        → Δ × Γ ⊢ e₂ ↓ (natV v₂)
        → Δ × Γ ⊢ (lt e₁ e₂) ↓ (boolV (v₁ <ᵇ v₂))
    ↓and : ∀ {v₁ v₂} {e₁ e₂ : δ × γ ⊢ tyBool}
         → Δ × Γ ⊢ e₁ ↓ (boolV v₁)
         → Δ × Γ ⊢ e₂ ↓ (boolV v₂)
         → Δ × Γ ⊢ (and e₁ e₂) ↓ (boolV (v₁ ∧ v₂))
    ↓or : ∀ {v₁ v₂} {e₁ e₂ : δ × γ ⊢ tyBool}
        → Δ × Γ ⊢ e₁ ↓ (boolV v₁)
        → Δ × Γ ⊢ e₂ ↓ (boolV v₂)
        → Δ × Γ ⊢ (or e₁ e₂) ↓ (boolV (v₁ ∨ v₂))
```

The evaluation of negation takes one argument that evaluates to a boolean value
and returns the negated version of that value.
```agda
    ↓neg : ∀ {v} {e : δ × γ ⊢ tyBool}
         → Δ × Γ ⊢ e ↓ (boolV v)
         → Δ × Γ ⊢ (neg e) ↓ (boolV (not v))
```

The evaluation of a lambda expression stores the current environments and the
function body into a new function value and simply returns that.
```agda
    ↓lambda : ∀ {e : δ × γ , A ⊢ B}
            → Δ × Γ ⊢ (lambda e) ↓ (funcV Γ Δ e)
```

Function application takes three arguments. The first is an evaluation that
should evaluate to the function to apply, the second is an evaluation whos result
will be used as the function argument, and finally it takes an evaluation for the
function body with this specific argument.
```agda
    ↓appl : ∀ {retV : Val retT}
              {argV : Val argT}
              {e₁ : δ × γ ⊢ (argT ⇒ retT)}
              {e₂ : δ × γ ⊢ argT}
              {body : β × (σ , argT) ⊢ retT}
          → Δ × Γ ⊢ e₁ ↓ (funcV Σ Β body)
          → Δ × Γ ⊢ e₂ ↓ argV
          → Β × (Σ ,' argV) ⊢ body ↓ retV
          → Δ × Γ ⊢ (appl e₁ e₂) ↓ retV
```

The evaluations for `var` and `fvar` simply use the already stored lookups to
retrieve a value from the current environment and return that.
```agda
    ↓var : ∀ {l : γ ∋ A}
         → Δ × Γ ⊢ (var l) ↓ (env-lookup Γ l)

    ↓fvar : ∀ {l : δ ∋ᶠ (A ⇒ᶠ B)}
          → Δ × Γ ⊢ (fvar l) ↓ (fenv-lookup Δ l)
```

The evaluation for `fdef` takes two arguments. The first argument should evaluate
to the function value that will be appended to the function environment and the
second one is the evaluation for the rest of the program with that function
appended to its function environment.
```agda
    ↓fdef : ∀ {v : Val t} {fv : Val (A ⇒ B)} {body : (δ ,ᶠ A ⇒ᶠ B) × γ ⊢ t}
              {func : δ × γ ⊢ (A ⇒ B)}
          → Δ × Γ ⊢ func ↓ fv
          → (Δ ,ᶠ' fv) × Γ ⊢ body ↓ v
          → Δ × Γ ⊢ (fdef func body) ↓ v
```

The evaluation for `newCtx` simply takes an evaluation starting with empty
environments and returns its resulting value in the current environment.
```agda
    ↓newCtx : ∀ {v : Val t} {e : ∅ᶠ × ∅ ⊢ t}
            → ∅ᶠ' × ∅' ⊢ e ↓ v
            → Δ × Γ ⊢ (newCtx e) ↓ v
```
