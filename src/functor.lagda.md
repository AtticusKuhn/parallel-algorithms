

```agda
open import Felix.Object using (Products ;  Coproducts ;   _×_ ; ⊤ ; _⊎_)
open import Felix.Raw using (Category ; Cartesian ; Cocartesian ; id ; _∘_ ; _▵_ ; twice ; _⊗_ ; inl ; inr ; ! ; _▿_)
open import Felix.Equiv using (_≈_ ; Equivalent)
open import bitoperations using ( HasBitOperations )
open import hasparity  using (HasParity)
module functor {lvl} {S : Set lvl} {_⇨_ : S  → S  → Set} (let infix 0 _⇨_; _⇨_ = _⇨_) ⦃ x : Category _⇨_ ⦄ {{ps : Products S}} ⦃ y : Cartesian _⇨_ ⦄{{ equiv : Equivalent Agda.Primitive.lzero _⇨_ }} { Bit : S } { N : S } ⦃ bitops : HasBitOperations Bit ⦄ ⦃ num : HasParity N ⦄ where




open HasBitOperations bitops
open HasParity num

record Functor : Set (Agda.Primitive.lsuc lvl) where
  field
    %2 : N ⇨ Bit
    zeroeven : %2 ∘ p0 ≈ bit0
    oneodd : %2 ∘ p1 ≈ bit1
    distrib : %2 ∘ add ≈ xor ∘ twice %2
    -- this is just wrong!
    -- distrib/2 : and ∘ twice %2 ≈ %2 ∘ /2 ∘ add

```
