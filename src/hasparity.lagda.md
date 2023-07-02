

```agda

{-# OPTIONS --allow-unsolved-metas #-}
open import Felix.Object using (Products ;  Coproducts ;   _×_ ; ⊤ ; _⊎_)
open import Felix.Raw using (Category ; Cartesian ; Cocartesian ; id ; _∘_ ; _▵_ ; twice ; _⊗_ ; inl ; inr ; ! ; _▿_ ; second ; first ; assocˡ ; swap)
open import Felix.Equiv using (_≈_ ; Equivalent)
-- open import bitoperations using ( HasBitOperations )
module hasparity {lvl} {S : Set lvl} {_⇨_ : S  → S  → Set} (let infix 0 _⇨_; _⇨_ = _⇨_) ⦃ x : Category _⇨_ ⦄ {{ps : Products S}} ⦃ y : Cartesian _⇨_ ⦄{{ equiv : Equivalent Agda.Primitive.lzero _⇨_ }} where




-- open HasBitOperations bitops

record HasParity (A : S) : Set (Agda.Primitive.lsuc lvl) where
  field
    -- %2 : A ⇨ Bit
    /2 : A ⇨ A
    -- /2∘*2 : /2 ∘ *2 ≈ id
    p0 p1 : ⊤ ⇨ A
    add : A × A ⇨ A
    push : /2 ∘ add ≈ add ∘ twice /2
    p0/2 : /2 ∘ p0 ≈ p0
    p1/2 : /2 ∘ p1 ≈ p0
    addIdLeft : {B : S} {f : A × B ⇨ A} →  add ∘ ( (p0 ∘ !) ▵ (f)) ≈ f
    addAssoc : add ∘ second add ≈ add ∘ first add  ∘ assocˡ
    addComm : add ≈ add ∘ swap

  *2 : A ⇨ A
  *2 = add ∘ Cartesian.dup y
  /2∘*2 : /2 ∘ *2 ≈ id
  /2∘*2 = {! !}

    -- zeroeven : %2 ∘ p0 ≈ HasBitOperations.bit0 bitops
    -- distrib : %2 ∘ add ≈ HasBitOperations.xor bitops ∘ twice %2

```
