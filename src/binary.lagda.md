Switching course, I will explore binary arithmetic at first.




# Imports
```agda
open import Data.Nat.Base using (ℕ ; suc ; _+_ ; _^_ ; ⌊_/2⌋ )
open import Felix.Object using (Products ;  Coproducts ;   _×_ ; ⊤ ; _⊎_)
open import Felix.Raw using (Category ; Cartesian ; Cocartesian ; id ; _∘_ ; _▵_ ; twice ; _⊗_ ; inl ; inr ; ! ; _▿_ ; exl ; exr ; first ; second ; assocʳ ; assocˡ ;inAssocʳ′ ; transpose ;  dup ; swap)
open import Relation.Binary.PropositionalEquality using (cong ; _≡_ ; subst)
open import Felix.Equiv using (_≈_ ; Equivalent)
import Felix.Laws as L using (Cartesian)
open L.Cartesian
open import hasparity using (HasParity)
open HasParity
open import bitoperations using (HasBitOperations)
open HasBitOperations

```

# Module declaration and Instances
```agda
module binary
     -- (A : Set)
       {{ps : Products Set }}
       {{cps : Coproducts Set }}
     {_⇨_ : Set  → Set  → Set} (let infix 0 _⇨_; _⇨_ = _⇨_)
     ⦃ x : Category _⇨_ ⦄ ⦃ y : Cartesian _⇨_ ⦄ ⦃ z : Cocartesian _⇨_ ⦄

         {{ equiv : Equivalent Agda.Primitive.lzero _⇨_ }}
         (N : Set)
         (Bit : Set)
         {{parity : HasParity N Bit}}
         {{bitops : HasBitOperations Bit}}

     where
```


# Declare Varaibles
```agda
variable
  A B C D : Set
```


# Define Bits
We will represent binary numbers as a list of bits
```
List : ℕ → Set → Set
List 0 A = ⊤
List (suc n) A = A × (List n A)

Bits : ℕ → Set
Bits n = List n Bit

```

# Convert Between Numbers and Little Endian Representations
Define the denotation function to convert between numbers and our binary representation of numbers. We are representing binary numbers as a little endian list of bits.
```
NatToLittleEndian : (b : ℕ) →  N ⇨ Bits b
NatToLittleEndian 0 =  !
NatToLittleEndian (suc b) = (%2 parity) ▵ ((NatToLittleEndian b) ∘ (/2 parity))


LittleEndianToNat : (b : ℕ) → Bits b ⇨ N
LittleEndianToNat  0 = p0 parity
LittleEndianToNat (suc b) = if bitops ∘  (second ( second (*2 parity) ∘ twice (LittleEndianToNat b) ∘ dup)) --- ((id) ▿ (*2 hpa)) ⊗ (LittleEndianToNat b)
```

prove the the two functions are naturally isomorphic (they are inverses)

```agda
--- todo
inverses : (b : ℕ) → (NatToLittleEndian b ∘ LittleEndianToNat b ≈ id)
inverses 0 = {! !}
inverses (suc b) = {! !}
```

# Adder

Define a half adder.
```agda
halfAdder : Bit × Bit  ⇨ Bit × Bit
halfAdder  = (xor bitops) ▵ (and bitops)
```
Define a ful adder
```agda
fullAdder : (Bit × Bit) × Bit ⇨ Bit × Bit
fullAdder =  first (or bitops) ∘ inAssocʳ′ (second (halfAdder))  ∘ first (halfAdder) -- (or bitops ∘  ( exl ∘ halfAdder ∘ exl ▵  exl ∘ halfAdder ∘ first (exr ∘ halfAdder))) ▵  exr ∘ halfAdder ∘ first ( exr ∘ halfAdder)
```

Define some utility functions
```agda
scoop : {A B C D : Set} → (A × B) × (C × D) ⇨ ((A × B) × D) × C
scoop =  ((exl ∘ exl ▵ exr ∘ exl) ▵ ( exr ∘ exr)) ▵ (exl ∘ exr)


blender : {A B C : Set} → (A × B) × C ⇨ (A × C) × B
blender = inAssocʳ′ (second (swap))
```

Use ripple addition to add two `b` bit little endian representations of binary numbers.
```agda
rippleAddLittleEndian : (b : ℕ) → ((Bits b) × (Bits b)) × Bit ⇨ (Bits b) × Bit
rippleAddLittleEndian 0 = ! ⊗ id
rippleAddLittleEndian (suc n) =  (( ( ( blender {Bit} {Bit} {Bits n} ∘ first (fullAdder) ) ∘ scoop) ∘ second (rippleAddLittleEndian n) ) ∘ assocʳ  ) ∘ first (transpose)
```
