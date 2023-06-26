This module defines the contexts used in our language.
```agda
module Language.Context.Definition where

open import Language.Types
```

First we have to inform Agda of the infix operators we will define within this
module.
```agda
infixl 5 _,_
infixl 5 _,ᶠ_
```

Contexts will contain a list of types that are currently in scope for an
expression in our language. Our definition for contexts is based on the one
defined in the [Lambda chapter](https://plfa.github.io/Lambda/) of the PLFA book.

A context can either be empty (signified by the `∅`) or contain some value
(using the `_,_` infix operator). The `_,_` constructor takes a context and a
type to append to it and returns a new context with that type appended to it.
```agda
data Context : Set where
    ∅   : Context
    _,_ : Context → Type → Context
```

Our function contexts work in the same way, except that they store function types
instead of normal types.
```agda
data FContext : Set where
    ∅ᶠ   : FContext
    _,ᶠ_ : FContext → FType → FContext
```
