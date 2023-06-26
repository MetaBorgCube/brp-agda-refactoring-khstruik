This module defines the lookups into the contexts used in our language.
```agda
module Language.Context.Lookup where

open import Language.Types
open import Language.Context.Definition
```

First we define some variables we will be using throughout this module.
```agda
private
    variable
        δ : FContext
        γ : Context
        A B : Type
        Aᶠ Bᶠ : FType
```

We also need to inform Agda what infix operators we will be defining.
```agda
infix  4 _∋_
infix  4 _∋ᶠ_
```

We can then construct a data type to represent a lookup into a normal
environment. For the lookups we use the approach described in the
[Lambda chapter](https://plfa.github.io/Lambda/) of the PLFA book.

The `Z` construct signifies that the type we are looking for is at the end of the
current context, while the `S` constructor signifies that it is somewhere deeper
in the context. We can then chain these constructors to provide a lookup to
anywhere in the context.
```agda
data _∋_ : Context → Type → Set where
    Z  : γ , A ∋ A
    S_ : γ ∋ A → γ , B ∋ A
```

Similarly, we have to also define these lookups for the function environment.
```agda
data _∋ᶠ_ : FContext → FType → Set where
    Zᶠ : δ ,ᶠ Aᶠ ∋ᶠ Aᶠ
    Sᶠ : δ ∋ᶠ Aᶠ → δ ,ᶠ Bᶠ ∋ᶠ Aᶠ
```
