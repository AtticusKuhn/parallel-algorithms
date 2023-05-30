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

-- a number category
data _↝_ : Set → Set →  Set₁ where
  zero : ⊤ ↝ A
  one : ⊤ ↝ A
  add : (A × A) ↝ A
  max : (A × A) ↝ A
open import Function.Base using (id ; _∘_)
open import Agda.Builtin.Sigma
evaluate : (f : A ⟹ B) → (x : A) → B
evaluate mid  = id
evaluate (f m∘ g) = (evaluate f) ∘ (evaluate g)
evaluate m! x = tt
evaluate mexl  = fst
evaluate mexr  = snd
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


# Undeciable

Conal Elliott made me realize that the cost of a lambda term is undeciable, so my previous definition had been wrong.


Also, I realized that it is impossible to get a lower bound on the time of an algorithm, we can only ever get an upper bound on an execution time.

Even if one execution strategy gives one execution time to an algorithm, we have no way of knowing if another execution strategy might give a better time, so we can only
have an upper bound on the time of an algorithm. The datatype `CostLub` gives an upper bound on the cost of a function. `CostLub f x n` is the proposition that the function `f`
can be called on the input `x` in `n` time.

I also created the datatype `Equal` to use in `CostLub`. `Equal f g` is the proposition that the algorithm `f` is equal to the algorithm `g`.


```agda

data Equal : {A B : Set} → ( A ⟹ B ) → (A ⟹ B) → Set where
  refl : {A B : Set}  → (f : A ⟹ B) → Equal f f
  idright : {A B : Set} → (f : A ⟹ B) → Equal (f m∘ mid) f
  idleft : {A B : Set} → (f : A ⟹ B) → Equal (mid m∘ f) f
  assoc : {A B C D : Set} → (f : C ⟹ D) → (g : B ⟹ C) → (h : A ⟹ B) → Equal (f m∘ (g m∘ h)) ((f m∘ g) m∘ h)
  allTrue : {A : Set} → (f : A ⟹ ⊤ ) → Equal f m!
  distribTriangle : {A B C : Set} → (f : A ⟹ B) → (g : A ⟹ B) → (h : A ⟹ C) → (k : A ⟹ C) → (Equal f g) → (Equal k h) → Equal (f m▵  k) (g m▵ h)


testEqual : (f : A ⟹ B) → (g : A ⟹ C) →  Equal ( mexl m∘  (f m▵ g) ) f
testEqual f g = {! !}

data CostLub : {A : Set} → {B : Set} → (A ⟹ B) → A → ℕ →  Set₁ where
  LubId : {C : Set}  → (x : C) → CostLub mid x 0
  LubExl :{C : Set} → {D : Set} → (x : C × D) →  CostLub mexl x 0
  LubExr :{C : Set} → {D : Set} → (x : C × D) →  CostLub mexr x 0
  LubBang : {A : Set} → (x : A) → CostLub m! x 0
  LubComp : {A B C : Set} → (f : B ⟹ C) → (g : A ⟹ B) → (n : ℕ) → (m : ℕ) → (a : A)  → (x : CostLub f (evaluate g a) n) → (y : CostLub g a m) → CostLub (f m∘ g) a (n + m)
  LubTriangle : {A B C : Set} → (f : A ⟹ B) → (g : A ⟹ C) → (n : ℕ) → (m : ℕ) → (a : A)  (x : CostLub f a n) → (y : CostLub g a m) → CostLub (f m▵ g) a (n ⊔ m)
  LubEqual : {A B : Set} → (x : A) → (n : ℕ) → (f : A ⟹ B) → (g : A  ⟹ B) → Equal f g → CostLub f x n → CostLub g x n


open import Relation.Binary.PropositionalEquality using (subst)

timeLub : (n : ℕ) → (t : tree n ℕ) → (e : (a : ℕ) → (b :  ℕ) → CostLub madd ( a , b) 1) → CostLub (reduce n) t n
timeLub 0 a e = LubId a
timeLub (suc n) ( a , b ) e rewrite (maxIdempotent n) = LubComp madd ( (reduce n  m∘ mexl) m▵ (reduce n m∘ mexr)) 1 n (a , b) (e (evaluate (reduce n) a) (evaluate (reduce n) b))
  (subst (λ x → (CostLub ((reduce n m∘ mexl) m▵ (reduce n m∘ mexr)) ( a , b ) x)) (maxIdempotent n)
  (LubTriangle (reduce n m∘ mexl) (reduce n m∘ mexr) n n (a , b) (subst (λ x → CostLub (reduce n m∘ mexl) (a , b) x) (addZero n) ( LubComp (reduce n) mexl n 0 ((a , b)) (timeLub n a e) (LubExl ((a , b))))) (subst (λ x → CostLub (reduce n m∘ mexr) (a , b) x) (addZero n) (LubComp (reduce n) mexr n 0 ((a , b)) (timeLub n b e) (LubExr ( (a , b)))))))


automaticLub : (expr : A ⟹ B) → (x : A ) → CostLub expr x (parallelCost expr x)
automaticLub mid x = LubId x
automaticLub (f m∘ g) x = LubComp f g (parallelCost f (evaluate g x)) (parallelCost g x) x (automaticLub f (evaluate g x)) ( automaticLub g x)
automaticLub m! x = LubBang x
automaticLub mexl x = LubExl x
automaticLub mexr x = LubExr x
automaticLub (f m▵ g) x = LubTriangle (f) (g) (parallelCost f x) (parallelCost g x) x (automaticLub f x) (automaticLub g x)
automaticLub madd x = {!!}
```
