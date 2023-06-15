


```agda



open import Felix.Object using (Products ;  Coproducts ;   _×_ ; ⊤ ; _⊎_)
open import Felix.Raw using (Category ; Cartesian ; Cocartesian ; id ; _∘_ ; _▵_ ; twice ; _⊗_ ; inl ; inr ; ! ; _▿_)
open import Felix.Equiv using (_≈_ ; Equivalent)
module bitoperations
     {_⇨_ : Set  → Set  → Set} (let infix 0 _⇨_; _⇨_ = _⇨_)
     ⦃ x : Category _⇨_ ⦄
         {{ equiv : Equivalent Agda.Primitive.lzero _⇨_ }}
         {{ps : Products Set}}
     where



record HasBitOperations (Bit : Set) : Set₁ where
  field
    bit0 bit1 : ⊤ ⇨ Bit
    xor or and : Bit × Bit  ⇨ Bit
    if : {A : Set } →  Bit × (A × A) ⇨ A


```
