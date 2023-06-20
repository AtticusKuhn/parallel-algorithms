


```agda



open import Felix.Object using (Products ;  Coproducts ;   _×_ ; ⊤ ; _⊎_)
open import Felix.Raw using (Category ; Cartesian ; Cocartesian ; id ; _∘_ ; _▵_ ; twice ; _⊗_ ; inl ; inr ; ! ; _▿_ ; constʳ ; second)
open import Felix.Equiv using (_≈_ ; Equivalent)
module bitoperations
       {level}
       {S : Set level}
     {_⇨_ : S  → S  → Set} (let infix 0 _⇨_; _⇨_ = _⇨_)
     ⦃ x : Category _⇨_ ⦄
         {{ps : Products S}}
     ⦃ y : Cartesian _⇨_ ⦄
         {{ equiv : Equivalent Agda.Primitive.lzero _⇨_ }}
     where



record HasBitOperations (Bit : S) : Set (Agda.Primitive.lsuc level) where
  field
    bit0 bit1 : ⊤ ⇨ Bit
    xor or and : Bit × Bit  ⇨ Bit
    if : {A : S } →  Bit × (A × A) ⇨ A
    ifdistrib : {A B : S} {f : A ⇨ B } →  f ∘ if {A} ≈ if {B} ∘ second (twice f)


```
