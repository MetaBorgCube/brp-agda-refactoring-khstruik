module Refactoring.Proof where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Nullary using (yes; no; Dec; ¬_)
open import Relation.Binary.PropositionalEquality.Core using (_≢_)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _≟_; _+_; _*_; _<ᵇ_)
open import Data.Bool using (Bool; false; true; _∧_; _∨_; not)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)

open import Refactoring.Definition
open import Language

private
    variable 
        δ : FContext
        γ : Context
        Δ : FEnv δ
        Γ : Env γ
        t argT retT A B : Type
        ft : FType
        n : ℕ
        default : ∅ᶠ × ∅ ⊢ argT

value-from-↓expr : ∀ {v : Val t} {e : δ × γ ⊢ t}
                 → Δ × Γ ⊢ e ↓ v
                 → Val t
value-from-↓expr {v = v} e = v

_≡vᵣ_ : Val t → Val t → Set
natV xₒ ≡vᵣ natV xₙ = xₒ ≡ xₙ
boolV xₒ ≡vᵣ boolV xₙ = xₒ ≡ xₙ
funcV {argT = argT} {retT} Γₒ Δₒ bₒ ≡vᵣ funcV Γₙ Δₙ bₙ = 
    ∀ {argVₒ : Val argT} {argVₙ : Val argT} {argVₒ≡vᵣargVₙ : argVₒ ≡vᵣ argVₙ} 
      {retVₒ : Val retT} {retVₙ : Val retT}
    → Δₒ × (Γₒ ,' argVₒ) ⊢ bₒ ↓ retVₒ
    → Δₙ × (Γₙ ,' argVₙ) ⊢ bₙ ↓ retVₙ
    → retVₒ ≡vᵣ retVₙ 

i+j≡h+k : ∀ {i j h k} → i ≡ h → j ≡ k → i + j ≡ h + k
i+j≡h+k refl refl = refl

i*j≡h*k : ∀ {i j h k} → i ≡ h → j ≡ k → i * j ≡ h * k
i*j≡h*k refl refl = refl

i<ᵇj≡h<ᵇk : ∀ {i j h k} → i ≡ h → j ≡ k → (i <ᵇ j) ≡ (h <ᵇ k)
i<ᵇj≡h<ᵇk refl refl = refl

i∧j≡h∧k : ∀ {i j h k} → i ≡ h → j ≡ k → (i ∧ j) ≡ (h ∧ k)
i∧j≡h∧k refl refl = refl

i∨j≡h∨k : ∀ {i j h k} → i ≡ h → j ≡ k → (i ∨ j) ≡ (h ∨ k)
i∨j≡h∨k refl refl = refl

not-i≡not-h : ∀ {i h} → i ≡ h → (not i) ≡ (not h)
not-i≡not-h refl = refl

data EquivEnv : Env γ → Set where
    ee-root : EquivEnv ∅'
    ee-elem : ∀ {vₒ vₙ : Val t}
            → EquivEnv Γ → (vₒ≡vᵣvₙ : vₒ ≡vᵣ vₙ) → EquivEnv (Γ ,' vₒ)


constructEquivEnv : ∀ {Γ : Env γ} → EquivEnv Γ → Env γ
constructEquivEnv ee-root = ∅'
constructEquivEnv (ee-elem {vₙ = vₙ} ee vₒ≡vᵣvₙ) = (constructEquivEnv ee) ,' vₙ

data EquivEnvPadded : Env γ → ℕ → Type → Set where
    eep-elem : ∀ {vₒ vₙ : Val t}
            → EquivEnvPadded Γ n argT
            → (vₒ≡vᵣvₙ : vₒ ≡vᵣ vₙ)
            → EquivEnvPadded (Γ ,' vₒ) (suc n) argT

    eep-pad  : EquivEnv Γ
            → (vₙ : Val argT)
            → EquivEnvPadded Γ zero argT

constructEquivEnvPadded : ∀ {Γ : Env γ}
                        → EquivEnvPadded Γ n argT
                        → Env (insertType γ n argT)
constructEquivEnvPadded (eep-elem {vₙ = vₙ} eep vₒ≡vᵣvₙ) = (constructEquivEnvPadded eep) ,' vₙ
constructEquivEnvPadded (eep-pad ee vₙ) = (constructEquivEnv ee) ,' vₙ


data EquivFEnv : FEnv δ → Set where
    efe-root : EquivFEnv ∅ᶠ'
    efe-elem : ∀ {vₒ vₙ : Val (FType-to-Type ft)}
             → EquivFEnv Δ → (vₒ≡vᵣvₙ : vₒ ≡vᵣ vₙ) → EquivFEnv (Δ ,ᶠ' vₒ)


constructEquivFEnv : ∀ {Δ : FEnv δ} → EquivFEnv Δ → FEnv δ
constructEquivFEnv efe-root = ∅ᶠ'
constructEquivFEnv (efe-elem {vₙ = vₙ} efe vₒ≡vᵣvₙ) = (constructEquivFEnv efe) ,ᶠ' vₙ


data EquivFEnvReplaced : FEnv δ → ℕ → Type → Set where
    efer-elem : ∀ {vₒ vₙ : Val (FType-to-Type ft)}
              → EquivFEnvReplaced Δ n argT
              → (vₒ≡vᵣvₙ : vₒ ≡vᵣ vₙ)
              → EquivFEnvReplaced (Δ ,ᶠ' vₒ) (suc n) argT
    efer-repl : ∀ {vₒ : Val (A ⇒ B)} {vₙ : Val (argT ⇒ A ⇒ B)}
                  {e : δ × ∅ ⊢ (A ⇒ B)}
              → (efe : EquivFEnv Δ)
              → (ee : EquivEnv ∅')
              → Δ × ∅' ⊢ e ↓ vₒ
              → (constructEquivFEnv efe) × (constructEquivEnv ee) ⊢ (lambda (fixRefs e zero)) ↓ vₙ
              → EquivFEnvReplaced (Δ ,ᶠ' vₒ) zero argT


constructEquivFEnvReplaced : ∀ {Δ : FEnv δ}
                           → EquivFEnvReplaced Δ n argT
                           → FEnv (replaceFunction δ n argT)
constructEquivFEnvReplaced (efer-elem {vₙ = vₙ} efer vₒ≡vᵣvₙ)
    = (constructEquivFEnvReplaced efer) ,ᶠ' vₙ
constructEquivFEnvReplaced (efer-repl {vₙ = vₙ} efer ee ↓eₒ ↓eₙ)
    = (constructEquivFEnv efer) ,ᶠ' vₙ


var≡vᵣ : ∀ {γ t} {Γ : Env γ}
     → (ee : EquivEnv Γ)
     → (l : γ ∋ t)
     → (env-lookup Γ l) ≡vᵣ (env-lookup (constructEquivEnv ee) l)
var≡vᵣ (ee-elem ee vₒ≡vᵣvₙ) Z = vₒ≡vᵣvₙ
var≡vᵣ (ee-elem ee vₒ≡vᵣvₙ) (S l) = var≡vᵣ ee l


fvar≡vᵣ : ∀ {δ ft} {Δ : FEnv δ}
        → (efe : EquivFEnv Δ)
        → (l : δ ∋ᶠ ft)
        → (fenv-lookup Δ l) ≡vᵣ (fenv-lookup (constructEquivFEnv efe) l) 
fvar≡vᵣ (efe-elem efe vₒ≡vᵣvₙ) Zᶠ = vₒ≡vᵣvₙ
fvar≡vᵣ (efe-elem efe vₒ≡vᵣvₙ) (Sᶠ l) = fvar≡vᵣ efe l


equiv-env≡ : ∀ {vₒ vₙ : Val t} {e : δ × γ ⊢ t}
           → (efe : EquivFEnv Δ)
           → (ee : EquivEnv Γ)
           → Δ × Γ ⊢ e ↓ vₒ
           → (constructEquivFEnv efe) × (constructEquivEnv ee) ⊢ e ↓ vₙ
           → vₒ ≡vᵣ vₙ
equiv-env≡ efe ee ↓nat ↓nat = refl
equiv-env≡ efe ee ↓bool ↓bool = refl
equiv-env≡ efe ee (↓plus eₒ eₒ₁) (↓plus eₙ eₙ₁) = i+j≡h+k (equiv-env≡ efe ee eₒ eₙ) (equiv-env≡ efe ee eₒ₁ eₙ₁)
equiv-env≡ efe ee (↓mult eₒ eₒ₁) (↓mult eₙ eₙ₁) = i*j≡h*k (equiv-env≡ efe ee eₒ eₙ) (equiv-env≡ efe ee eₒ₁ eₙ₁)
equiv-env≡ efe ee (↓lt eₒ eₒ₁) (↓lt eₙ eₙ₁) = i<ᵇj≡h<ᵇk (equiv-env≡ efe ee eₒ eₙ) (equiv-env≡ efe ee eₒ₁ eₙ₁)
equiv-env≡ efe ee (↓and eₒ eₒ₁) (↓and eₙ eₙ₁) = i∧j≡h∧k (equiv-env≡ efe ee eₒ eₙ) (equiv-env≡ efe ee eₒ₁ eₙ₁)
equiv-env≡ efe ee (↓or eₒ eₒ₁) (↓or eₙ eₙ₁) = i∨j≡h∨k (equiv-env≡ efe ee eₒ eₙ) (equiv-env≡ efe ee eₒ₁ eₙ₁)
equiv-env≡ efe ee (↓neg eₒ) (↓neg eₙ) = not-i≡not-h (equiv-env≡ efe ee eₒ eₙ)
equiv-env≡ efe ee ↓lambda ↓lambda {argVₒ≡vᵣargVₙ = argVₒ≡vᵣargVₙ} ↓bₒ ↓bₙ
    = equiv-env≡ efe (ee-elem ee argVₒ≡vᵣargVₙ) ↓bₒ ↓bₙ
equiv-env≡ efe ee (↓appl eₒ eₒ₁ eₒ₂) (↓appl eₙ eₙ₁ eₙ₂)
    = equiv-env≡ efe ee eₒ eₙ {argVₒ≡vᵣargVₙ = equiv-env≡ efe ee eₒ₁ eₙ₁} eₒ₂ eₙ₂
equiv-env≡ {e = var l} efe ee ↓var ↓var = var≡vᵣ ee l
equiv-env≡ {e = fvar l} efe ee ↓fvar ↓fvar = fvar≡vᵣ efe l
equiv-env≡ efe ee (↓fdef eₒ eₒ₁) (↓fdef eₙ eₙ₁)
    = equiv-env≡ (efe-elem efe (equiv-env≡ efe ee eₒ eₙ)) ee eₒ₁ eₙ₁
equiv-env≡ efe ee (↓newCtx eₒ) (↓newCtx eₙ) = equiv-env≡ efe-root ee-root eₒ eₙ


correct-fix-var : ∀ {Γ : Env γ}
                → (l : γ ∋ t)
                → (n : ℕ)
                → (eep : EquivEnvPadded Γ n A)
                → (env-lookup Γ l) ≡vᵣ (env-lookup (constructEquivEnvPadded eep) (fixVar l n))
correct-fix-var l zero (eep-pad ee vₙ) = var≡vᵣ ee l
correct-fix-var Z (suc n) (eep-elem eep vₒ≡vᵣvₙ) = vₒ≡vᵣvₙ
correct-fix-var (S l) (suc n) (eep-elem eep vₒ≡vᵣvₙ) = correct-fix-var l n eep


correct-fix-refs : ∀ {A δ γ t n} {Δ : FEnv δ} {Γ : Env γ}
                     {e : δ × γ ⊢ t}
                     {vₒ vₙ : Val t}
                 → (efe : EquivFEnv Δ)
                 → (ee : EquivEnvPadded Γ n A)
                 → Δ × Γ ⊢ e ↓ vₒ
                 → (constructEquivFEnv efe) × (constructEquivEnvPadded ee) ⊢ (fixRefs e n) ↓ vₙ
                 → vₒ ≡vᵣ vₙ
correct-fix-refs efe eep ↓nat ↓nat = refl
correct-fix-refs efe eep ↓bool ↓bool = refl
correct-fix-refs efe eep (↓plus eₒ eₒ₁) (↓plus eₙ eₙ₁) = i+j≡h+k (correct-fix-refs efe eep eₒ eₙ) (correct-fix-refs efe eep eₒ₁ eₙ₁)
correct-fix-refs efe eep (↓mult eₒ eₒ₁) (↓mult eₙ eₙ₁) = i*j≡h*k (correct-fix-refs efe eep eₒ eₙ) (correct-fix-refs efe eep eₒ₁ eₙ₁)
correct-fix-refs efe eep (↓lt eₒ eₒ₁) (↓lt eₙ eₙ₁) = i<ᵇj≡h<ᵇk (correct-fix-refs efe eep eₒ eₙ) (correct-fix-refs efe eep eₒ₁ eₙ₁)
correct-fix-refs efe eep (↓and eₒ eₒ₁) (↓and eₙ eₙ₁) = i∧j≡h∧k (correct-fix-refs efe eep eₒ eₙ) (correct-fix-refs efe eep eₒ₁ eₙ₁)
correct-fix-refs efe eep (↓or eₒ eₒ₁) (↓or eₙ eₙ₁) = i∨j≡h∨k (correct-fix-refs efe eep eₒ eₙ) (correct-fix-refs efe eep eₒ₁ eₙ₁)
correct-fix-refs efe eep (↓neg eₒ) (↓neg eₙ) = not-i≡not-h (correct-fix-refs efe eep eₒ eₙ)
correct-fix-refs efe eep ↓lambda ↓lambda {argVₒ≡vᵣargVₙ = argVₒ≡vᵣargVₙ} ↓bₒ ↓bₙ
    = correct-fix-refs efe (eep-elem eep argVₒ≡vᵣargVₙ) ↓bₒ ↓bₙ
correct-fix-refs efe eep (↓appl eₒ eₒ₁ eₒ₂) (↓appl eₙ eₙ₁ eₙ₂)
    = correct-fix-refs efe eep eₒ eₙ {argVₒ≡vᵣargVₙ = correct-fix-refs efe eep eₒ₁ eₙ₁} eₒ₂ eₙ₂
correct-fix-refs {n = n} {e = var l} efe eep ↓var ↓var = correct-fix-var l n eep
correct-fix-refs {e = fvar l} efe eep ↓fvar ↓fvar = fvar≡vᵣ efe l
correct-fix-refs efe eep (↓fdef eₒ eₒ₁) (↓fdef eₙ eₙ₁)
    = correct-fix-refs (efe-elem efe (correct-fix-refs efe eep eₒ eₙ)) eep eₒ₁ eₙ₁
correct-fix-refs efe eep (↓newCtx eₒ) (↓newCtx eₙ) = equiv-env≡ efe-root ee-root eₒ eₙ


correct-fix-lookupⁿ : ∀ {Δ : FEnv δ}
                    → (l : δ ∋ᶠ A ⇒ᶠ B)
                    → (n : ℕ)
                    → (p : ¬ fLookupDepth l ≡ n)
                    → (efer : EquivFEnvReplaced Δ n argT)
                    → fenv-lookup Δ l ≡vᵣ
                      fenv-lookup (constructEquivFEnvReplaced efer) (fixLookupⁿ l n p)
correct-fix-lookupⁿ Zᶠ zero p efer = isFalse (p refl)
correct-fix-lookupⁿ Zᶠ (suc n) p (efer-elem efer vₒ≡vᵣvₙ) = vₒ≡vᵣvₙ
correct-fix-lookupⁿ (Sᶠ l) zero p (efer-repl efe _ _ _) = fvar≡vᵣ efe l
correct-fix-lookupⁿ (Sᶠ l) (suc n) p (efer-elem efer vₒ≡vᵣvₙ) = correct-fix-lookupⁿ l n (¬decProof p) efer


rewrite-eₙ-fvar : ∀ {notHereT} {Δ : FEnv δ} {Γ : Env γ} {vₙ : Val (argT ⇒ A ⇒ B)}
                    {vₒₕ vₙₕ : Val (FType-to-Type notHereT)}
         → (vₒₕ≡vᵣvₙₕ : vₒₕ ≡vᵣ vₙₕ)
         → (n : ℕ)
         → (l : δ ∋ᶠ (A ⇒ᶠ B))
         → (p : fLookupDepth (Sᶠ {Bᶠ = notHereT} l) ≡ (suc n))
         → (ee : EquivEnv Γ) 
         → (efer : EquivFEnvReplaced Δ n argT)
         → (constructEquivFEnvReplaced (efer-elem efer vₒₕ≡vᵣvₙₕ)) × constructEquivEnv ee ⊢ fvar (fixLookupʸ (Sᶠ l) (suc n) p) ↓ vₙ
         → constructEquivFEnvReplaced efer × constructEquivEnv ee ⊢ fvar (fixLookupʸ l n (decProof p)) ↓ vₙ
rewrite-eₙ-fvar _ n l p ee efer ↓fvar = ↓fvar


dec-eₙ : ∀ {notHereT} {Δ : FEnv δ} {Γ : Env γ} {vₙ : Val (A ⇒ B)}
           {vₒₕ vₙₕ : Val (FType-to-Type notHereT)}
       → (vₒₕ≡vᵣvₙₕ : vₒₕ ≡vᵣ vₙₕ)
       → (n : ℕ)
       → (l : δ ∋ᶠ (A ⇒ᶠ B))
       → (p : fLookupDepth (Sᶠ {Bᶠ = notHereT} l) ≡ (suc n))
       → (ee : EquivEnv Γ) 
       → (efer : EquivFEnvReplaced Δ n argT)
       → (constructEquivFEnvReplaced (efer-elem efer vₒₕ≡vᵣvₙₕ)) × (constructEquivEnv ee) ⊢ (appl (fvar (fixLookupʸ (Sᶠ l) (suc n) p)) (newCtx default)) ↓ vₙ
       → (constructEquivFEnvReplaced efer) × (constructEquivEnv ee) ⊢ (appl (fvar (fixLookupʸ l n (decProof p))) (newCtx default)) ↓ vₙ
dec-eₙ _ zero Zᶠ p ee (efer-repl _ _ _ _) (↓appl ↓fvar (↓newCtx eₙ₁) eₙ₂) = ↓appl ↓fvar (↓newCtx eₙ₁) eₙ₂
dec-eₙ vₒₕ≡vᵣvₙₕ n@(suc _) l@(Sᶠ _) p ee efer (↓appl eₙ (↓newCtx eₙ₁) eₙ₂) = ↓appl (rewrite-eₙ-fvar vₒₕ≡vᵣvₙₕ n l p ee efer eₙ) (↓newCtx eₙ₁) eₙ₂


correct-fix-lookupʸ : ∀ {Δ : FEnv δ} {Γ : Env γ} {vₙ : Val (A ⇒ B)}
                    → (n : ℕ)
                    → (l : δ ∋ᶠ (A ⇒ᶠ B))
                    → (p : fLookupDepth l ≡ n)
                    → (ee : EquivEnv Γ) 
                    → (efer : EquivFEnvReplaced Δ n argT)
                    → ((constructEquivFEnvReplaced efer) × (constructEquivEnv ee) ⊢ (appl (fvar (fixLookupʸ l n p)) (newCtx default)) ↓ vₙ)
                    → (fenv-lookup Δ l) ≡vᵣ vₙ
correct-fix-lookupʸ zero Zᶠ refl _ (efer-repl efe ee ↓lambda ↓lambda) (↓appl ↓fvar eₙ₁ ↓lambda)
    {argVₒ≡vᵣargVₙ = argVₒ≡vᵣargVₙ} ↓bₒ ↓bₙ = correct-fix-refs efe (eep-elem (eep-pad ee (value-from-↓expr eₙ₁)) argVₒ≡vᵣargVₙ) ↓bₒ ↓bₙ
correct-fix-lookupʸ zero Zᶠ refl _ (efer-repl efe ee eₒ@(↓appl _ _ _) ↓lambda) (↓appl ↓fvar eₙ₁ eₙ@(↓appl _ _ _)) = correct-fix-refs efe (eep-pad ee (value-from-↓expr eₙ₁)) eₒ eₙ
correct-fix-lookupʸ zero Zᶠ refl _ (efer-repl efe ee eₒ@↓fvar         ↓lambda) (↓appl ↓fvar eₙ₁ eₙ@↓fvar)         = correct-fix-refs efe (eep-pad ee (value-from-↓expr eₙ₁)) eₒ eₙ
correct-fix-lookupʸ zero Zᶠ refl _ (efer-repl efe ee eₒ@(↓fdef _ _)   ↓lambda) (↓appl ↓fvar eₙ₁ eₙ@(↓fdef _ _))   = correct-fix-refs efe (eep-pad ee (value-from-↓expr eₙ₁)) eₒ eₙ
correct-fix-lookupʸ zero Zᶠ refl _ (efer-repl efe ee eₒ@(↓newCtx _)   ↓lambda) (↓appl ↓fvar eₙ₁ eₙ@(↓newCtx _))   = correct-fix-refs efe (eep-pad ee (value-from-↓expr eₙ₁)) eₒ eₙ
correct-fix-lookupʸ (suc n) (Sᶠ l) p ee (efer-elem efer vₒ≡vᵣvₙ) eₙ = correct-fix-lookupʸ n l (decProof p) ee efer (dec-eₙ vₒ≡vᵣvₙ n l p ee efer eₙ)


correct-fix-fvar : ∀ {Δ : FEnv δ} {Γ : Env γ} {l} {vₒ vₙ : Val (A ⇒ B)}
                 → (ee : EquivEnv Γ) 
                 → (efer : EquivFEnvReplaced Δ n argT)
                 → Δ × Γ ⊢ (fvar l) ↓ vₒ
                 → (constructEquivFEnvReplaced efer) × (constructEquivEnv ee) ⊢ (fixFvar l n default) ↓ vₙ
                 → vₒ ≡vᵣ vₙ
correct-fix-fvar {n = n} {l = l} ee efer ↓fvar eₙ with (fLookupDepth l) ≟ n
correct-fix-fvar {n = n} {l = l} ee efer ↓fvar eₙ    | yes p = correct-fix-lookupʸ n l p ee efer eₙ
correct-fix-fvar {n = n} {l = l} ee efer ↓fvar ↓fvar | no p = correct-fix-lookupⁿ l n p efer


correct-fix-calls : ∀ {Δ : FEnv δ} {Γ : Env γ} {e : δ × γ ⊢ t} {vₒ vₙ : Val t}
                  → (ee : EquivEnv Γ)
                  → (efer : EquivFEnvReplaced Δ n argT)
                  → Δ × Γ ⊢ e ↓ vₒ
                  → (constructEquivFEnvReplaced efer) × (constructEquivEnv ee) ⊢ (fixCalls e n default) ↓ vₙ
                  → vₒ ≡vᵣ vₙ

correct-fix-calls ee efer ↓nat ↓nat = refl
correct-fix-calls ee efer ↓bool ↓bool = refl
correct-fix-calls ee efer (↓plus eₒ eₒ₁) (↓plus eₙ eₙ₁) = i+j≡h+k (correct-fix-calls ee efer eₒ eₙ) (correct-fix-calls ee efer eₒ₁ eₙ₁)
correct-fix-calls ee efer (↓mult eₒ eₒ₁) (↓mult eₙ eₙ₁) = i*j≡h*k (correct-fix-calls ee efer eₒ eₙ) (correct-fix-calls ee efer eₒ₁ eₙ₁)
correct-fix-calls ee efer (↓lt eₒ eₒ₁) (↓lt eₙ eₙ₁) = i<ᵇj≡h<ᵇk (correct-fix-calls ee efer eₒ eₙ) (correct-fix-calls ee efer eₒ₁ eₙ₁)
correct-fix-calls ee efer (↓and eₒ eₒ₁) (↓and eₙ eₙ₁) = i∧j≡h∧k (correct-fix-calls ee efer eₒ eₙ) (correct-fix-calls ee efer eₒ₁ eₙ₁)
correct-fix-calls ee efer (↓or eₒ eₒ₁) (↓or eₙ eₙ₁) = i∨j≡h∨k (correct-fix-calls ee efer eₒ eₙ) (correct-fix-calls ee efer eₒ₁ eₙ₁)
correct-fix-calls ee efer (↓neg eₒ) (↓neg eₙ) = not-i≡not-h (correct-fix-calls ee efer eₒ eₙ)
correct-fix-calls ee efer ↓lambda ↓lambda {argVₒ≡vᵣargVₙ = argVₒ≡vᵣargVₙ} ↓bₒ ↓bₙ
    = correct-fix-calls (ee-elem ee argVₒ≡vᵣargVₙ) efer ↓bₒ ↓bₙ
correct-fix-calls ee efer (↓appl eₒ eₒ₁ eₒ₂) (↓appl eₙ eₙ₁ eₙ₂)
    = correct-fix-calls ee efer eₒ eₙ {argVₒ≡vᵣargVₙ = correct-fix-calls ee efer eₒ₁ eₙ₁} eₒ₂ eₙ₂
correct-fix-calls {e = var l} ee efer ↓var ↓var = var≡vᵣ ee l
correct-fix-calls ee efer eₒ@↓fvar eₙ = correct-fix-fvar ee efer eₒ eₙ
correct-fix-calls ee efer (↓fdef eₒ eₒ₁) (↓fdef eₙ eₙ₁)
    = correct-fix-calls ee (efer-elem efer (correct-fix-calls ee efer eₒ eₙ)) eₒ₁ eₙ₁
correct-fix-calls ee efer (↓newCtx eₒ) (↓newCtx eₙ) = equiv-env≡ efe-root ee-root eₒ eₙ


correct-afa : ∀ {Δ : FEnv δ} {e : δ × ∅ ⊢ t} {vₒ vₙ : Val t}
            → (efe : EquivFEnv Δ)
            → (ee : EquivEnv ∅')
            → Δ × ∅' ⊢ e ↓ vₒ
            → (constructEquivFEnv efe) × (constructEquivEnv ee) ⊢ (afa e n default) ↓ vₙ
            → vₒ ≡vᵣ vₙ

correct-afa {n = zero} efe ee (↓fdef eₒ eₒ₁) (↓fdef ↓lam@↓lambda eₙ)
    = correct-fix-calls ee (efer-repl efe ee eₒ ↓lam) eₒ₁ eₙ
correct-afa {n = suc n} efe ee (↓fdef eₒ eₒ₁) (↓fdef eₙ eₙ₁)
    = correct-afa (efe-elem efe (equiv-env≡ efe ee eₒ eₙ)) ee eₒ₁ eₙ₁

correct-afa efe ee ↓nat ↓nat = refl
correct-afa efe ee ↓bool ↓bool = refl
correct-afa efe ee (↓plus eₒ eₒ₁) (↓plus eₙ eₙ₁) = i+j≡h+k (equiv-env≡ efe ee eₒ eₙ) (equiv-env≡ efe ee eₒ₁ eₙ₁)
correct-afa efe ee (↓mult eₒ eₒ₁) (↓mult eₙ eₙ₁) = i*j≡h*k (equiv-env≡ efe ee eₒ eₙ) (equiv-env≡ efe ee eₒ₁ eₙ₁)
correct-afa efe ee (↓lt eₒ eₒ₁) (↓lt eₙ eₙ₁) = i<ᵇj≡h<ᵇk (equiv-env≡ efe ee eₒ eₙ) (equiv-env≡ efe ee eₒ₁ eₙ₁)
correct-afa efe ee (↓and eₒ eₒ₁) (↓and eₙ eₙ₁) = i∧j≡h∧k (equiv-env≡ efe ee eₒ eₙ) (equiv-env≡ efe ee eₒ₁ eₙ₁)
correct-afa efe ee (↓or eₒ eₒ₁) (↓or eₙ eₙ₁) = i∨j≡h∨k (equiv-env≡ efe ee eₒ eₙ) (equiv-env≡ efe ee eₒ₁ eₙ₁)
correct-afa efe ee (↓neg eₒ) (↓neg eₙ) = not-i≡not-h (equiv-env≡ efe ee eₒ eₙ)
correct-afa efe ee ↓lambda ↓lambda {argVₒ≡vᵣargVₙ = argVₒ≡vᵣargVₙ} ↓bₒ ↓bₙ
    = equiv-env≡ efe (ee-elem ee argVₒ≡vᵣargVₙ) ↓bₒ ↓bₙ
correct-afa efe ee (↓appl eₒ eₒ₁ eₒ₂) (↓appl eₙ eₙ₁ eₙ₂)
    = equiv-env≡ efe ee eₒ eₙ {argVₒ≡vᵣargVₙ = equiv-env≡ efe ee eₒ₁ eₙ₁} eₒ₂ eₙ₂
correct-afa {e = var l} efe ee ↓var ↓var = var≡vᵣ ee l
correct-afa {e = fvar l} efe ee ↓fvar ↓fvar = fvar≡vᵣ efe l
correct-afa efe ee (↓newCtx eₒ) (↓newCtx eₙ) = equiv-env≡ efe-root ee-root eₒ eₙ

