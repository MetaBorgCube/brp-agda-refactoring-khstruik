module Language.Semantics where

open import Data.Nat using (ℕ; _+_; _*_; _<ᵇ_)
open import Data.Bool using (Bool; not; _∨_; _∧_)

open import Language.Definition

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

data _×_⊢_↓_ : FEnv δ → Env γ → (δ × γ ⊢ t) → Val t → Set where
    ↓nat  : Δ × Γ ⊢ nat n ↓ natV n
    ↓bool : Δ × Γ ⊢ bool b ↓ boolV b
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
    ↓neg : ∀ {v} {e : δ × γ ⊢ tyBool}
         → Δ × Γ ⊢ e ↓ (boolV v)
         → Δ × Γ ⊢ (neg e) ↓ (boolV (not v))
    ↓lambda : ∀ {e : δ × γ , A ⊢ B}
            → Δ × Γ ⊢ (lambda e) ↓ (funcV Γ Δ e)
    ↓appl : ∀ {retV : Val retT}
              {argV : Val argT}
              {e₁ : δ × γ ⊢ (argT ⇒ retT)}
              {e₂ : δ × γ ⊢ argT}
              {body : β × (σ , argT) ⊢ retT}
          → Δ × Γ ⊢ e₁ ↓ (funcV Σ Β body)
          → Δ × Γ ⊢ e₂ ↓ argV
          → Β × (Σ ,' argV) ⊢ body ↓ retV
          → Δ × Γ ⊢ (appl e₁ e₂) ↓ retV
    ↓var : ∀ {l : γ ∋ A}
         → Δ × Γ ⊢ (var l) ↓ (env-lookup Γ l)
    ↓fvar : ∀ {l : δ ∋ᶠ (A ⇒ᶠ B)}
          → Δ × Γ ⊢ (fvar l) ↓ (fenv-lookup Δ l)
    ↓fdef : ∀ {v : Val t} {fv : Val (A ⇒ B)} {body : (δ ,ᶠ A ⇒ᶠ B) × γ ⊢ t}
              {func : δ × γ ⊢ (A ⇒ B)}
          → Δ × Γ ⊢ func ↓ fv
          → (Δ ,ᶠ' fv) × Γ ⊢ body ↓ v
          → Δ × Γ ⊢ (fdef func body) ↓ v
    ↓newCtx : ∀ {v : Val t} {e : ∅ᶠ × ∅ ⊢ t}
            → ∅ᶠ' × ∅' ⊢ e ↓ v
            → Δ × Γ ⊢ (newCtx e) ↓ v

