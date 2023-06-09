Switching course, I will explore binary arithmetic at first.




# Imports
```agda

{-# OPTIONS --allow-unsolved-metas #-}
open import Data.Nat.Base using (ℕ ; suc ; _+_ ; _^_ ; ⌊_/2⌋ )
open import Felix.Object using (Products ;  Coproducts ;   _×_ ; ⊤ ; _⊎_)
open import Felix.Raw using (Category ; Cartesian ; Cocartesian ; id ; _∘_ ; _▵_ ; twice ; _⊗_ ; inl ; inr ; ! ; _▿_ ; exl ; exr ; first ; second ; assocʳ ; assocˡ ;inAssocʳ′ ; transpose ;  dup ; swap ;   unitorⁱʳ ; constʳ; inAssocˡ′; inAssocˡ ; constˡ)
open import Relation.Binary.PropositionalEquality using (cong ; _≡_ ; subst)
open import Felix.Equiv using ( Equivalent)
import Felix.Laws as L using (Cartesian ; Category)
open import hasparity using (HasParity)
-- open import euclideanDomain using (EuclideanDomain)
open import bitoperations using (HasBitOperations)
open import functor using (Functor)

```

# Module declaration and Instances
```agda

module bin2
       {lvl}
       { S : Set lvl }
     -- (A : Set)
       {{ps : Products S }}
       {{cps : Coproducts S }}
     {_⇨_ : S  → S  → Set} (let infix 0 _⇨_; _⇨_ = _⇨_)
     ⦃ x : Category _⇨_ ⦄ ⦃ y : Cartesian _⇨_ ⦄ ⦃ z : Cocartesian _⇨_ ⦄

         {{ equiv : Equivalent Agda.Primitive.lzero _⇨_ }}
         ⦃ cateq : L.Category _⇨_ ⦄
         ⦃ carteq : L.Cartesian _⇨_ ⦄
         (N : S)
         (Bit : S)
         {{bitops : HasBitOperations Bit}}
         {{parity : HasParity {{x = x}} N}}
         {{f : Functor {lvl = lvl} {S = S} ⦃ x = x ⦄ ⦃ ps = ps ⦄ ⦃ y = y ⦄ ⦃ equiv = equiv ⦄  ⦃ num = parity ⦄ }}
         -- ⦃ ed : EuclideanDomain N ⦄

     where

open HasBitOperations bitops
open HasParity parity
open Functor f
open Equivalent equiv
open L.Cartesian carteq
open L.Category cateq
-- open EuclideanDomain ed
-- Bit : S
-- Bit = N
```


# Declare Varaibles
```agda
variable
  A B C D : S
  b : ℕ
```


# Define Bits
We will represent binary numbers as a list of bits
```agda
List : ℕ → S → S
List 0 A = A
List (suc n) A = A × (List n A)

Bits : ℕ → S
Bits n = List n Bit


```

# Convert Between Numbers and Little Endian Representations
Define the denotation function to convert between numbers and our binary representation of numbers. We are representing binary numbers as a little endian list of bits.
```agda
NatToLittleEndian : N ⇨ Bits b
NatToLittleEndian {0} =  %2
NatToLittleEndian {suc b} = %2 ▵ (NatToLittleEndian {b} ∘ /2)


bitToNat : Bit ⇨ N
bitToNat = if ∘ constʳ (p1 ▵ p0)

LittleEndianToNat : Bits b ⇨ N
LittleEndianToNat  {0} = bitToNat
LittleEndianToNat {suc b} =   add ∘ (bitToNat  ⊗ (*2 ∘ LittleEndianToNat {b}))
```



# Adder

Define a half adder.

Note that for convention, the left output is the sum and the right output is the carry.
```agda
halfAdder : Bit × Bit  ⇨ Bit × Bit
halfAdder  = xor ▵ and

open ≈-Reasoning
halfAdderSpecification :  LittleEndianToNat {1} ∘ halfAdder ≈ add ∘ twice bitToNat
halfAdderSpecification = begin
  LittleEndianToNat {1} ∘ halfAdder
  ≡⟨⟩
  (add ∘ (bitToNat ⊗ (*2 ∘ bitToNat))) ∘ (xor ▵ and)
  ≡⟨⟩
  (add ∘ (bitToNat ⊗ (*2 ∘ bitToNat))) ∘ (xor ▵ and)
  ≈⟨ ∘-assocʳ ⟩
  add ∘ (bitToNat ⊗ (*2 ∘ bitToNat)) ∘ (xor ▵ and)
  ≈⟨ ∘≈ʳ ⊗∘▵ ⟩
  add  ∘ (bitToNat ∘  xor ▵ (*2 ∘ bitToNat) ∘ and)
  ≡⟨⟩
  add  ∘ ((if ∘ constʳ (p1 ▵ p0)) ∘  xor ▵ (*2 ∘ (if ∘ constʳ (p1 ▵ p0))) ∘ and)
  ≈⟨ ∘≈ʳ (▵≈ʳ (∘≈ˡ ∘-assocˡ)) ⟩
  add  ∘ ((if ∘ constʳ (p1 ▵ p0)) ∘  xor ▵ ((*2 ∘ if) ∘ constʳ (p1 ▵ p0)) ∘ and)
  ≈⟨ ∘≈ʳ (▵≈ʳ (∘≈ˡ (∘≈ˡ ifdistrib ))) ⟩
  -- if(A ⊕ B,1,0) + if(A ∧ B, 2,0)
   add  ∘ ((if ∘ constʳ (p1 ▵ p0)) ∘  xor ▵ ( ( if ∘ second (twice *2)) ∘ constʳ (p1 ▵ p0)) ∘ and)
  ≈⟨ {! !} ⟩
  -- if(A,1,0) + if(B,1,0)
   add ∘ twice (LittleEndianToNat {0})
  ∎



```
Define a ful adder.

Note that for convention, the left output is the sum and the right output is the carry.
```agda
fullAdder : Bit × Bit × Bit ⇨ Bit × Bit
fullAdder = second or ∘ inAssocˡ′ (first halfAdder) ∘  second halfAdder

fullAdderSpecification : LittleEndianToNat {1} ∘ fullAdder  ≈ add ∘ second add ∘ (bitToNat ⊗ twice bitToNat)
fullAdderSpecification = sym (begin
  add ∘ second add ∘ (bitToNat ⊗ twice bitToNat)
  ≈⟨ ∘≈ʳ (second∘⊗)  ⟩
  add ∘  (bitToNat ⊗ add ∘ twice bitToNat)
  ≈⟨ ∘≈ʳ (⊗≈ʳ (sym halfAdderSpecification)) ⟩
  add ∘  (bitToNat ⊗ LittleEndianToNat {1} ∘ halfAdder)
  ≡⟨⟩
  add ∘  (bitToNat ⊗ (add ∘ (bitToNat ⊗ *2 ∘ bitToNat))  ∘ halfAdder)
  ≈⟨ {! !} ⟩
  LittleEndianToNat {1} ∘ fullAdder
  ∎)
-- fullAdderSpecification : NatToLittleEndian {1} ∘ add ∘  second add ≈ fullAdder ∘ (%2 ⊗ twice %2)
-- fullAdderSpecification = begin
--   NatToLittleEndian {1} ∘ add ∘  second add -- correct
--   ≡⟨⟩
--   (%2 ▵ (%2 ∘ /2)) ∘ add ∘ second add -- correct
--   ≈⟨ ∘-assocˡ ⟩
--   ((%2 ▵ (%2 ∘ /2)) ∘ add) ∘ second add -- coorect
--   ≈⟨ ∘≈ˡ halfAdderSpecification ⟩
--   (halfAdder ∘ twice %2) ∘ second add -- wrong
--   ≈⟨ ∘-assocʳ ⟩
--   halfAdder ∘ twice %2 ∘ second add
--   ≈⟨ ∘≈ʳ ⊗∘⊗ ⟩
--   halfAdder ∘ ((%2 ∘ id) ⊗ (%2 ∘ add))
--   ≈⟨ ∘≈ʳ (⊗≈ (trans identityʳ (sym identityˡ)) distrib ) ⟩
--   halfAdder ∘ ((id ∘ %2) ⊗ (xor ∘ twice %2))
--   ≈⟨ ∘≈ʳ (sym ⊗∘⊗) ⟩
--   halfAdder ∘ second xor ∘ (%2 ⊗  twice %2)
--   ≈⟨ {! !} ⟩
--   fullAdder ∘ (%2 ⊗ twice %2)
--   ∎

```

Specification that half adder and full adder are correct.

The specification for the half adder says that if I add two bits, that should be the same as putting the two bits through a half-adder and then converting the result to a number.

The specification for the full adder says that if I have any three bits, adding them should be the same as inputting them to the full-adder and then converting the result to a number.



Use ripple addition to add two `b` bit little endian representations of binary numbers.
```agda

zip : List b A × List b B ⇨ List b (A × B)
zip {0} = id
zip {suc b} =  second (zip {b}) ∘ transpose


RCA : Bit × List b (Bit × Bit) ⇨ Bits (suc b)
RCA {0} = fullAdder
RCA {suc n} = second (RCA {n}) ∘ inAssocˡ′ (first fullAdder)

RippleAdd : Bits b × Bits b ⇨ Bits (suc b)
RippleAdd {b} = RCA {b} ∘ constˡ (bit0) ∘ zip {b}

-- RCAspecification : LittleEndianToNat {suc b} ∘ RCA {b} ≈

-- RippleAddSpecification :  RippleAdd {b} ∘ twice (NatToLittleEndian {b}) ≈ NatToLittleEndian {b} ∘ add
-- RippleAddSpecification {0} = {! !}
-- RippleAddSpecification {suc b}  = begin
--   RippleAdd {suc b} ∘ twice (NatToLittleEndian {suc b})
--   ≡⟨⟩
--   ((second (RCA {b}) ∘ inAssocˡ′ (first fullAdder)) ∘ constˡ (bit0) ∘ (second (zip {b}) ∘ transpose)  ) ∘ twice (%2 ▵ (NatToLittleEndian {b} ∘ /2))
--   ≈⟨ {! !} ⟩
--   NatToLittleEndian {suc b } ∘ add
--   ∎
--
--
shiftLeft : Bits b ⇨ Bits (suc b)
shiftLeft = constˡ bit0

padLeft : (a : ℕ) → Bits b ⇨ Bits (a + b)
padLeft 0 = id
padLeft (suc n) = constˡ bit0 ∘ padLeft n

0s : ⊤ ⇨  Bits b
0s {0} = bit0
0s {suc b} = constˡ bit0 ∘ 0s {b}

mulDigit : Bit × Bits b ⇨ Bits b
mulDigit {b} = if ∘ second (id ▵  0s {b} ∘ !)

mulDigit2 : Bit × Bits b ⇨ Bits b
mulDigit2 {0} = and
-- mulDigit2 {suc n} =  and ∘ second exl ▵ mulDigit2 {n} ∘ second exr
mulDigit2 {suc n} = (and ⊗ mulDigit2 {n}) ∘ transpose ∘ first dup

longMultiplication : Bits b × Bits b ⇨ Bits ( b + b )
longMultiplication {0} = and
longMultiplication {suc n} = {! !}
```
