```agda
module Refactoring.Util where

open import Agda.Builtin.Equality using (_≡_; refl)

open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality.Core using (_≢_)
open import Relation.Nullary using (yes; no; ¬_)
```

```agda
private
    variable
        n m : ℕ
```

```agda
isFalse : ∀ {A : Set} → ⊥ → A
isFalse ()
```

```agda
decProof : (suc n) ≡ (suc m) → n ≡ m
decProof refl = refl
```

```agda
incProof : n ≡ m → (suc n) ≡ (suc m)
incProof refl = refl
```

```agda
¬decProof : (suc n) ≢ (suc m) → (n ≢ m)
¬decProof {zero} {zero} p = isFalse (p refl)
¬decProof {zero} {suc m} p = λ ()
¬decProof {suc n} {zero} p = λ ()
¬decProof {suc n} {suc m} p with (suc n ≟ suc m)
... | yes p₁ = isFalse (p (incProof p₁))
... | no  p₁ = p₁
```
