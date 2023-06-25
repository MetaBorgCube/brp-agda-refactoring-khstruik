module Language.Definition where

open import Data.Nat using (ℕ; zero; suc; _≤?_; s≤s; z≤n; _<_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Relation.Nullary.Decidable using (True; toWitness)

infix  4 _×_⊢_
infix  4 _∋_
infixl 5 _,_
infixr 7 _⇒_
infix  4 _∋ᶠ_
infixl 5 _,ᶠ_
infixr 7 _⇒ᶠ_

data Type : Set where
    tyBool : Type
    tyNat  : Type
    _⇒_    : Type → Type → Type

data FType : Set where
    _⇒ᶠ_ : Type → Type → FType

FType-to-Type : FType → Type
FType-to-Type (x ⇒ᶠ x₁) = x ⇒ x₁

data Context : Set where
    ∅   : Context
    _,_ : Context → Type → Context

data FContext : Set where
    ∅ᶠ   : FContext
    _,ᶠ_ : FContext → FType → FContext

private
    variable
        δ : FContext
        γ : Context
        argT retT A B C t : Type
        Aᶠ Bᶠ ft : FType

data _∋_ : Context → Type → Set where
    Z  : γ , A ∋ A

    S_ : γ ∋ A → γ , B ∋ A

data _∋ᶠ_ : FContext → FType → Set where
    Zᶠ : δ ,ᶠ Aᶠ ∋ᶠ Aᶠ

    Sᶠ : δ ∋ᶠ Aᶠ → δ ,ᶠ Bᶠ ∋ᶠ Aᶠ

data _×_⊢_ : FContext → Context → Type → Set where
    bool   : Bool
           --------------
           → δ × γ ⊢ tyBool

    nat    : ℕ
           --------------
           → δ × γ ⊢ tyNat

    plus   : δ × γ ⊢ tyNat
           → δ × γ ⊢ tyNat
           --------------
           → δ × γ ⊢ tyNat

    mult   : δ × γ ⊢ tyNat
           → δ × γ ⊢ tyNat
           --------------
           → δ × γ ⊢ tyNat

    lt     : δ × γ ⊢ tyNat
           → δ × γ ⊢ tyNat
           --------------
           → δ × γ ⊢ tyBool

    and    : δ × γ ⊢ tyBool
           → δ × γ ⊢ tyBool
           --------------
           → δ × γ ⊢ tyBool

    or     : δ × γ ⊢ tyBool
           → δ × γ ⊢ tyBool
           --------------
           → δ × γ ⊢ tyBool

    neg    : δ × γ ⊢ tyBool
           --------------
           → δ × γ ⊢ tyBool

    var    : γ ∋ A
           --------------
           → δ × γ ⊢ A

    lambda : δ × γ , A ⊢ B
           --------------
           → δ × γ ⊢ (A ⇒ B)

    appl   : δ × γ ⊢ (A ⇒ B)
           → δ × γ ⊢ A
           --------------
           → δ × γ ⊢ B

    fdef   : δ × γ ⊢ (A ⇒ B)
           → (δ ,ᶠ (A ⇒ᶠ B)) × γ ⊢ C
           --------------
           → δ × γ ⊢ C

    fvar   : δ ∋ᶠ Aᶠ
           --------------
           → δ × γ ⊢ (FType-to-Type Aᶠ)

    newCtx : ∅ᶠ × ∅ ⊢ A
           --------------
           → δ × γ ⊢ A

data Env : Context → Set
data FEnv : FContext → Set

data Val : Type → Set where
    natV  : ℕ → Val tyNat
    boolV : Bool → Val tyBool
    funcV : Env γ → FEnv δ → δ × γ , argT ⊢ retT → Val (argT ⇒ retT)

data Env where
    ∅' : Env ∅
    _,'_ : Env γ → Val t → Env (γ , t) 
    
env-lookup : Env γ → (l : γ ∋ t) → Val t
env-lookup (γ ,' v) Z = v
env-lookup (γ ,' v) (S l) = env-lookup γ l

data FEnv where
    ∅ᶠ' : FEnv ∅ᶠ
    _,ᶠ'_ : FEnv δ → Val (FType-to-Type ft) → FEnv (δ ,ᶠ ft)

fenv-lookup : FEnv δ → δ ∋ᶠ ft → Val (FType-to-Type ft)
fenv-lookup (δ ,ᶠ' v) Zᶠ = v
fenv-lookup (δ ,ᶠ' v) (Sᶠ l) = fenv-lookup δ l

