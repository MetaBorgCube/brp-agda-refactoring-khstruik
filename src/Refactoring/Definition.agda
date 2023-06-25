module Refactoring.Definition where

open import Agda.Builtin.Equality using (_≡_; refl)

open import Relation.Nullary using (yes; no; Dec; ¬_)
open import Relation.Binary.PropositionalEquality.Core using (_≢_)
open import Data.List using ([])
open import Data.Bool using (if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Empty using (⊥)

open import Language

private 
    variable
        δ : FContext
        γ : Context
        t argT retT A B : Type
        ft : FType
        n m : ℕ

insertType : Context → ℕ → Type → Context
insertType γ zero ty = γ , ty
insertType (γ , x) (suc n) ty = insertType γ n ty , x
insertType ∅ (suc n) _ = ∅

fixVar : γ ∋ t → (n : ℕ) → (insertType γ n A) ∋ t
fixVar x zero = S x
fixVar Z (suc n) = Z
fixVar (S x) (suc n) = S (fixVar x n)

fixRefs : δ × γ ⊢ t → (n : ℕ) → δ × (insertType γ n A) ⊢ t
fixRefs (var x) n = var (fixVar x n)
fixRefs (lambda e) n = lambda (fixRefs e (suc n))

fixRefs (bool x) n = bool x
fixRefs (nat x) n = nat x
fixRefs (plus e e₁) n = plus (fixRefs e n) (fixRefs e₁ n)
fixRefs (mult e e₁) n = mult (fixRefs e n) (fixRefs e₁ n)
fixRefs (lt e e₁) n = lt (fixRefs e n) (fixRefs e₁ n)
fixRefs (and e e₁) n = and (fixRefs e n) (fixRefs e₁ n) 
fixRefs (or e e₁) n = or (fixRefs e n) (fixRefs e₁ n)
fixRefs (neg e) n = neg (fixRefs e n)
fixRefs (appl e e₁) n = appl (fixRefs e n) (fixRefs e₁ n)
fixRefs (fdef e e₁) n = fdef (fixRefs e n) (fixRefs e₁ n)
fixRefs (fvar x) n = fvar x
fixRefs (newCtx e) n = newCtx e

replaceFunction : FContext → ℕ → Type → FContext
replaceFunction ∅ᶠ n ty = ∅ᶠ
replaceFunction (δ ,ᶠ rt) zero ty = δ ,ᶠ (ty ⇒ᶠ (FType-to-Type rt))
replaceFunction (δ ,ᶠ rt) (suc n) ty = (replaceFunction δ n ty) ,ᶠ rt

fLookupDepth : δ ∋ᶠ ft → ℕ
fLookupDepth Zᶠ = zero
fLookupDepth (Sᶠ l) = suc (fLookupDepth l)

isFalse : ∀ {A : Set} → ⊥ → A
isFalse ()

decProof : (suc n) ≡ (suc m) → n ≡ m
decProof refl = refl

incProof : n ≡ m → (suc n) ≡ (suc m)
incProof refl = refl

¬decProof : (suc n) ≢ (suc m) → (n ≢ m)
¬decProof {zero} {zero} p = isFalse (p refl)
¬decProof {zero} {suc m} p = λ ()
¬decProof {suc n} {zero} p = λ ()
¬decProof {suc n} {suc m} p with (suc n ≟ suc m)
... | yes p₁ = isFalse (p (incProof p₁))
... | no  p₁ = p₁

fixLookupʸ : (l : δ ∋ᶠ ft) → (n : ℕ) → fLookupDepth l ≡ n → (replaceFunction δ n argT) ∋ᶠ (argT ⇒ᶠ (FType-to-Type ft))
fixLookupʸ Zᶠ zero p = Zᶠ
fixLookupʸ (Sᶠ l) (suc n) p = Sᶠ (fixLookupʸ l n (decProof p))

fixLookupⁿ : (l : δ ∋ᶠ ft) → (n : ℕ) → fLookupDepth l ≢ n → (replaceFunction δ n argT) ∋ᶠ ft
fixLookupⁿ Zᶠ zero p = isFalse (p refl)
fixLookupⁿ Zᶠ (suc n) p = Zᶠ
fixLookupⁿ (Sᶠ l) zero p = Sᶠ l
fixLookupⁿ (Sᶠ l) (suc n) p = Sᶠ (fixLookupⁿ l n (¬decProof p))

fixFvar : δ ∋ᶠ ft
        → (n : ℕ)
        → ∅ᶠ × ∅ ⊢ argT
        → (replaceFunction δ n argT) × γ ⊢ (FType-to-Type ft)

fixFvar l n default with (fLookupDepth l) ≟ n
... | yes p = appl (fvar (fixLookupʸ l n p)) (newCtx default)
... | no  p = fvar (fixLookupⁿ l n p)

fixCalls : δ × γ ⊢ t
         → (n : ℕ)
         → ∅ᶠ × ∅ ⊢ argT
         → (replaceFunction δ n argT) × γ ⊢ t
fixCalls (bool x) n default = bool x
fixCalls (nat x) n default = nat x
fixCalls (plus e e₁) n default = plus (fixCalls e n default) (fixCalls e₁ n default)
fixCalls (mult e e₁) n default = mult (fixCalls e n default) (fixCalls e₁ n default)
fixCalls (lt e e₁) n default = lt (fixCalls e n default) (fixCalls e₁ n default)
fixCalls (and e e₁) n default = and (fixCalls e n default) (fixCalls e₁ n default)
fixCalls (or e e₁) n default = or (fixCalls e n default) (fixCalls e₁ n default)
fixCalls (neg e) n default = neg (fixCalls e n default)
fixCalls (var x) n default = var x
fixCalls (lambda e) n default = lambda (fixCalls e n default)
fixCalls (appl e e₁) n default = appl (fixCalls e n default) (fixCalls e₁ n default)
fixCalls (fdef e e₁) n default = fdef (fixCalls e n default) (fixCalls e₁ (suc n) default)
fixCalls (fvar l) n default = fixFvar l n default
fixCalls (newCtx e) n default = newCtx e

-- [A]dd [F]unction [A]rgument refactoring
-- Program → Function index → New Arg Default → New Program
afa : δ × γ ⊢ t → ℕ → ∅ᶠ × ∅ ⊢ argT → δ × γ ⊢ t

afa (fdef e e₁) zero default = fdef (lambda (fixRefs e zero)) (fixCalls e₁ zero default)
afa (fdef e e₁) (suc index) default = fdef e (afa e₁ index default)

afa e index default = e

