# Monoid

This file implements a monoidal category, or a category equipped with a monoidal combining operation.
The combining operation is called `madd` and can represent any operation from addition to multiplication.

```agda

open import Felix.Raw
module monoid
           ⦃ prodmon : Products Set ⦄
         {_⇨_ : Set → Set → Set} (let private infix 0 _⇨_; _⇨_ = _⇨_)
         ⦃ bruhcat : Category _⇨_ ⦄ ⦃ brucat : Cartesian _⇨_ ⦄

 where
--- variable a b c : obj
open import Felix.Object

record monoidCategory (a : Set) : Set where
  field
    madd :   ( a × a ) ⇨ a
    mzero :  ⊤ ⇨ a

```
