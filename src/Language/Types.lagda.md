```agda
module Language.Types where
```

First we inform agda what mixfix operators we will be defining in this file.
```agda
infixr 7 _⇒_
infixr 7 _⇒ᶠ_
```

Our language will contain three different types, booleans
(the `tyBool` constructor), natural numbers (the `tyNat` constructor), and 
functions (created using the infix operator `⇒` with other types on both sides).
```agda
data Type : Set where
    tyBool : Type
    tyNat  : Type
    _⇒_    : Type → Type → Type
```

We also define a special function only type for use later to ensure that our
function contexts will only be able to store functions.
```agda
data FType : Set where
    _⇒ᶠ_ : Type → Type → FType
```

Finally, we define a function to convert from our function only type to normal a
type.
```agda
FType-to-Type : FType → Type
FType-to-Type (x ⇒ᶠ x₁) = x ⇒ x₁
```
