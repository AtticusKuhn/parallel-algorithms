
Upon the suggestion of Conal Elliott, I am going to start again, but this time using an approach based on Cartesian Categories instead of
arrows.



First, let's import from the felix library, which provides several nice category-theoretic abstractions.
```agda

open import Felix.Raw  -- hiding (_⊎_ ; _×_)
```



```agda
-- import monoidal operations
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




-- here is how a tree is defined inductively`
data Tree (a : Set)  : Set  where
  Leaf : a -> Tree a
  Branch : Tree a -> Tree a -> Tree a

open import Agda.Builtin.Sigma

open import Data.Sum.Base hiding (_⊎_)
-- Note that this definition of tree is bad because it does not terminate
--{-# TERMINATING #-}
--myTree :  Set → Set
-- myTree a = ( a ⊎ ( (myTree a) × (myTree a)))

-- unroll2 : Tree a → a ⊎ Tree a × Tree a
-- unroll2 (Leaf a) = {! !}
-- unroll2 (Branch x t) = {! !}
-- open import Felix.Instances.Function.Type



-- reduceTree : a ⊎ (Tree a × Tree a) ⇨ a
-- reduceTree ={! id ▿ !}

-- a tree bounded by a height n
boundedTree : ℕ → Set →  Set
boundedTree zero a = a
boundedTree (suc n) a = (boundedTree n a) × (boundedTree n a)
-- {-# TERMINATING #-}
-- reduceTree :  ( Tree a ) ⇨ a
-- reduceTree =    id ▿  madd z ∘ twice  (reduceTree)

-- reduce a bounded tree
reduceBoundedTree : ( n : ℕ ) → (boundedTree n a) ⇨ a
reduceBoundedTree zero  = id
reduceBoundedTree (suc n) = madd z ∘ twice (reduceBoundedTree n)
```
