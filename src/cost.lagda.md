# Cost

Here I will try to define a cost function and then I will prove the cost of a parallel reduction of a tree using the cost approach.



# Imports
Import the needed libraries

```agda
module cost
 where

open import Data.Unit.Base
open import Data.Product
open import Data.Nat.Base
open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

variable
  A B C D : Set
```
# Cartesian Data Structure

Define the closed cartesian category data structure and operations over the structure.
```agda
data _⟹_ : Set → Set → Set₁ where
  mid : A ⟹ A
  _m∘_ : (f : B ⟹ C) → (g : A ⟹ B) → (A ⟹ C)
  m! : A ⟹ ⊤
  mexl : (A × B) ⟹ A
  mexr :  (A × B) ⟹ B
  _m▵_ : (left : A ⟹ C) → (right : A ⟹ D) → (A ⟹ (C × D))
  madd : ( ℕ × ℕ ) ⟹ ℕ

evaluate : (f : A ⟹ B) → (x : A) → B
evaluate mid x = x
evaluate (f m∘ g) x = evaluate f (evaluate g x)
evaluate m! x = tt
evaluate mexl ( a , b ) =  a
evaluate mexr (a , b) = b
evaluate (f m▵ g) x = (evaluate f x , evaluate g x)
evaluate madd (a , b) = a + b

parallelCost : (A ⟹ B) → A → ℕ
parallelCost mid a = 0
parallelCost (f m∘ g) a = parallelCost f (evaluate g a) + parallelCost g a
parallelCost m! a = 0
parallelCost mexl a = 0
parallelCost mexr a = 0
parallelCost (f m▵ g) a = (parallelCost f a) ⊔ (parallelCost g a)
parallelCost (madd) x = 1
```

# Tree
Define a tree and methods to reduce the tree

```agda


tree : (n : ℕ) → Set → Set
tree 0 a = a
tree (suc n ) a = (tree n a) × (tree n a)

reduce : (n : ℕ ) → (tree n  ℕ ⟹ ℕ)
reduce 0 = mid
reduce (suc n) = madd m∘ ( (reduce n  m∘ mexl) m▵ (reduce n m∘ mexr))

testTree : tree 2 ℕ
testTree = (( 1 , 2 ) , (3 , 4))

testReduce : parallelCost (reduce 2) testTree ≡ 2
testReduce = refl
```
# Auxiliary
Some auxiliary methods that I needed for the proof

```agda
maxIdempotent : (n : ℕ) → n ⊔ n ≡ n
maxIdempotent zero  = refl
maxIdempotent (suc b) = cong suc (maxIdempotent b)



addZero : (n : ℕ) → n + 0 ≡ n
addZero 0 = refl
addZero (suc n) = cong suc (addZero n)
```

# Proof
Prove that it takes `n` time to reduce a tree of height `n` in parallel.
```agda
timeReduce : (n : ℕ ) → (t : tree n ℕ) → parallelCost (reduce n) t ≡ n
timeReduce 0 x = refl
timeReduce (suc n ) (a , b) rewrite (addZero (parallelCost (reduce n) a)) | (addZero (parallelCost (reduce n ) a )) | (addZero (parallelCost (reduce n) b)) | (timeReduce n a) | (timeReduce n b) | (maxIdempotent n) = refl
```
