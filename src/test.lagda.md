



In this file, we will test our reduction function to make sure that it really works

# Imports
```agda
import cartesian
import monoid
open import Data.Nat.Base
open import Felix.Instances.Function.Raw
open import Felix.Instances.Function.Type
open import Data.Sum hiding (_⊎_)
open import Data.Product hiding (_×_)
open Felix.Instances.Function.Raw.→-instances
open import Felix.Object
open import Felix.Raw  -- hiding (_⊎_ ; _×_)
-- open Felix.Instances.Function.Type.→-instances
open →-raw-instances

open import Agda.Builtin.Sigma

```
# Instances
```agda
instance
  monoidNat : monoid.monoidCategory ⦃ prodmon = products Agda.Primitive.lzero ⦄ {_⇨_ = λ A B → A → B} ⦃ bruhcat = category Agda.Primitive.lzero ⦄ ⦃ brucat = cartesian Agda.Primitive.lzero ⦄ ℕ
  monoidNat = record
    { madd = λ x → (fst x) + (snd x)
    ; mzero = λ t → 0}

instance
  ps : Products Set
  ps = products Agda.Primitive.lzero
  pc : Coproducts Set
  pc = coproducts Agda.Primitive.lzero
  cat : Category (λ A B → A → B)
  cat = category Agda.Primitive.lzero
  catcar : Cartesian (λ A B → A → B)
  catcar = cartesian Agda.Primitive.lzero
  catcarco : Cocartesian (λ A B → A → B)
  catcarco = cocartesian Agda.Primitive.lzero
```
# Test
Test that the reduction on trees actually does what we want it to do.
```agda
--longType : Set
--longType = cartesian.Tree  ℕ {_⇨_ = λ A B → A → B } ⦃ x = category Agda.Primitive.lzero ⦄ ⦃ y = cartesian Agda.Primitive.lzero ⦄ ⦃ f = cocartesian Agda.Primitive.lzero ⦄ ⦃ z = monoidNat ⦄ ℕ
--testTree : cartesian.Tree  ℕ {_⇨_ = λ A B → A → B } ⦃ x = category Agda.Primitive.lzero ⦄ ⦃ y = cartesian Agda.Primitive.lzero ⦄ ⦃ f = cocartesian Agda.Primitive.lzero ⦄ ⦃ z = monoidNat ⦄ ℕ
--testTree = inj₁ 0

unroll :  ∀{a : Set} → cartesian.Tree ℕ a → ( a ⊎ cartesian.Tree ℕ  a × cartesian.Tree ℕ a )
unroll  ( cartesian.Leaf a ) = inj₁ a
unroll (cartesian.Branch x t) = inj₂ ( x , t )

open cartesian
 -- reduceTree : ∀ { a : Set } →
testTree : boundedTree ℕ 1 ℕ
testTree =  (1 , 2 )


testReduce : ℕ
testReduce = reduceBoundedTree ℕ 1 testTree


open import Agda.Builtin.Equality
testTestReduce : testReduce ≡ 3
testTestReduce = refl
-- test : ℕ
-- test = cartesian.reduceTree ℕ testTree



```
