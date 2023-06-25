module Util where

open import Data.List using (List; _∷_; [])

data Pair (A : Set) (B : Set) : Set where
    _,_ : (a : A) (b : B) → Pair A B

infixr 1 _,_

fst : ∀ {A B} → Pair A B → A
fst (a , b) = a

snd : ∀ {A B} → Pair A B → B
snd (a , b) = b

fstList : ∀ {A B} → List (Pair A B) → List A
fstList [] = []
fstList (x ∷ xs) = fst x ∷ fstList xs

sndList : ∀ {A B} → List (Pair A B) → List B
sndList [] = []
sndList (x ∷ xs) = snd x ∷ sndList xs

zip : ∀ {A B} → List A → List B → List (Pair A B)
zip [] _ = []
zip _ [] = []
zip (a ∷ as) (b ∷ bs) = (a , b) ∷ (zip as bs)
