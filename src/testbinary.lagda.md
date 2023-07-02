

```agda

{-# OPTIONS --allow-unsolved-metas #-}


open import Data.Nat.Base
open import Data.Bool

import bin2
module testbinary where
open import Felix.Object
open import Felix.Raw
open import Felix.Equiv
open import Felix.Instances.Function.Raw
open Felix.Instances.Function.Raw.→-instances
open →-raw-instances
open import Agda.Builtin.Sigma
import Felix.Laws as L
import Felix.Instances.Function.Laws as LI
-- LI.→-laws-instances
import Data.Unit as u
import Level as v
open import bitoperations
open import hasparity
open import functor


odd : ℕ → Bool
odd 0 = false
odd 1 =  true
odd (suc (suc n)) = odd n
even : ℕ → Bool
even n = not (odd n)


instance
  ps2 : Products Set
  ps2 = products v.zero
  cps2 : Coproducts Set
  cps2 = coproducts Agda.Primitive.lzero
  cat : Category (λ A B → A → B)
  cat = category Agda.Primitive.lzero
  catcar : Cartesian (λ A B → A → B)
  catcar = cartesian Agda.Primitive.lzero
  cocatcar : Cocartesian (λ A B → A → B)
  cocatcar = cocartesian Agda.Primitive.lzero
  eq : Equivalent Agda.Primitive.lzero (λ A B → A → B)
  eq = equivalent Agda.Primitive.lzero
  lcat : L.Category (λ A B → A → B)
  lcat = LI.→-laws-instances.category v.zero
  lcart : L.Cartesian (λ A B → A → B)
  lcart = LI.→-laws-instances.cartesian v.zero
  bitops : HasBitOperations Bool
  bitops = record {
    bit0 = λ u → false
    ; bit1 = λ u → true
    ; xor = λ A → (fst A) xor (snd A)
    ; and = λ A → (fst A) ∧ (snd A)
    ; or = λ A → (fst A) ∨ (snd A)
    ; if = λ A → if (fst A) then (fst (snd A)) else (snd (snd A))
    }
  par : HasParity ℕ
  par = record {
    p0 = λ u → 0
    ; p1 = λ u → 1
    ; /2 = λ N → ⌊ N /2⌋
    ; add = λ NN → (fst NN) + (snd NN)
    }
  fun : Functor
  fun = record {
    %2 = odd
    ; zeroeven = {! !}
    ; distrib = {! !}
    }



import Data.List as Ls


open bin2 ⦃ ps2 ⦄ ⦃ cps2 ⦄ ⦃ cat ⦄ ⦃ catcar ⦄ ℕ Bool
--   using (List; [];)


-- range : ℕ → Ls.List (Bits 3)
-- range 0 = Ls.[]
-- range (suc n ) = Ls._∷_ (NatToLittleEndian 3 n)  (range n)

-- end : Bits 0
-- end = v.lift u.tt

list : Bits 1
list = true , true

test : ℕ
test  = LittleEndianToNat {1} list


bits : Bits 4
bits = NatToLittleEndian {4} 4


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

t1 : halfAdder (false , false)  ≡ (false , false)
t1 = Eq.refl

t2 : halfAdder (false , true)  ≡ (true , false)
t2 = Eq.refl
t3 : halfAdder (true , false)  ≡ (true , false)
t3 = Eq.refl
t4 : halfAdder (true , true)  ≡ (false , true)
t4 = Eq.refl

t5 : fullAdder (false , false , false)  ≡ (false , false)
t5 = Eq.refl

t13 : fullAdder (true , false , false)  ≡ (true , false)
t13 = Eq.refl
t6 : fullAdder (false , true , false)  ≡ (true , false)
t6 = Eq.refl
t7 : fullAdder (false , false , true)  ≡ (true , false)
t7 = Eq.refl
t8 : fullAdder (true , true , false)  ≡ (false , true)
t8 = Eq.refl
t9 : fullAdder (false , true , true)  ≡ (false , true)
t9 = Eq.refl
t10 : fullAdder (true , false , true)  ≡ (false , true)
t10 = Eq.refl
t11 : fullAdder (true , true , true)  ≡ (true , true)
t11 = Eq.refl


testAdd : ℕ
testAdd  = LittleEndianToNat {4} (RippleAdd {3} (NatToLittleEndian {3} 3 , NatToLittleEndian {3} 5))



```
