
Upon the suggestion of Conal Elliott, I am going to start again, but this time using an approach based on Cartesian Categories instead of
arrows.



First, let's import from the felix library, which provides several nice category-theoretic abstractions.
```agda

open import Felix.Raw  -- hiding (_⊎_ ; _×_)
```



```agda
open import monoid -- hiding (a ; b ; c)
open monoidCategory

module cartesian
             ⦃ p : Products Set ⦄
            ⦃ cp : Coproducts Set ⦄
          (a : Set)
         {_⇨_ : Set → Set → Set} (let infix 0 _⇨_; _⇨_ = _⇨_)
         ⦃ x : Category _⇨_ ⦄ ⦃ y : Cartesian _⇨_ ⦄
         ⦃ f : Cocartesian _⇨_ ⦄
         ⦃ z : monoidCategory {{p}} {{x}} {{y}} a ⦄

 where


open import Data.Nat.Base
-- open import Felix.Instances.Function.Raw
open import Felix.Instances.Function.Type
open →-instances
--
-- open import Data.Product


double :  a ⇨ a
double  = (madd z) ∘ dup



data Tree (a : Set)  : Set  where
  Leaf : a -> Tree a
  Branch : Tree a -> Tree a -> Tree a

open import Agda.Builtin.Sigma

open import Data.Sum.Base hiding (_⊎_)
--{-# TERMINATING #-}
--myTree :  Set → Set
-- myTree a = ( a ⊎ ( (myTree a) × (myTree a)))

-- unroll2 : Tree a → a ⊎ Tree a × Tree a
-- unroll2 (Leaf a) = {! !}
-- unroll2 (Branch x t) = {! !}
-- open import Felix.Instances.Function.Type
open import Data.List

testid :  a ⇨ a
testid = id


reduceBranch : a ⊎ (a × a) ⇨ a
reduceBranch = id ▿ (madd z)

-- reduceTree : a ⊎ (Tree a × Tree a) ⇨ a
-- reduceTree ={! id ▿ !}

boundedTree : ℕ → Set →  Set
boundedTree zero a = a
boundedTree (suc n) a = (boundedTree n a) × (boundedTree n a)
-- {-# TERMINATING #-}
-- reduceTree :  ( Tree a ) ⇨ a
-- reduceTree =    id ▿  madd z ∘ twice  (reduceTree)

reduceBoundedTree : ( n : ℕ ) → (boundedTree n a) ⇨ a
reduceBoundedTree zero  = id
reduceBoundedTree (suc n) = madd z ∘ twice (reduceBoundedTree n)

module test where
open import Data.Nat.Base
open import Felix.Instances.Function.Raw
open import Data.Sum
--open →-instances
-- open →-raw-instances
-- testTree : myTree  ℕ
-- testTree = inj₁ 0


-- test : myTree a → a
-- test = reduceTree {_⇨_ = (λ a b → a → b)}


```
