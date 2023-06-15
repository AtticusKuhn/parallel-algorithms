

```agda
open import Felix.Object using (Products ;  Coproducts ;   _×_ ; ⊤ ; _⊎_)
open import Felix.Raw using (Category ; Cartesian ; Cocartesian ; id ; _∘_ ; _▵_ ; twice ; _⊗_ ; inl ; inr ; ! ; _▿_)
open import Felix.Equiv using (_≈_ ; Equivalent)
module hasparity
     {_⇨_ : Set  → Set  → Set} (let infix 0 _⇨_; _⇨_ = _⇨_)
     ⦃ x : Category _⇨_ ⦄
         {{ equiv : Equivalent Agda.Primitive.lzero _⇨_ }}
         {{ps : Products Set}}
     where



record HasParity (A Bit : Set) : Set where
  field
    %2 : A ⇨ Bit
    /2 : A ⇨ A
    *2 : A ⇨ A
    /2∘*2 : /2 ∘ *2 ≈ id
    p0 : ⊤ ⇨ A

```
