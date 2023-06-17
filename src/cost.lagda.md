# Cost

Here I will try to define a cost function and then I will prove the cost of a parallel reduction of a tree using the cost approach.



# Imports
Import the needed libraries

```agda

open import Felix.Raw  -- hiding (_⊎_ ; _×_)
```



```agda
-- import monoidal operations
open import monoid -- hiding (a ; b ; c)
open monoidCategory
open import Felix.Equiv hiding (sym)
-- open import Agda.Primitive.Level
-- open Equivalence
-- open ≡-Reasoning

module cost
             ⦃ p : Products Set ⦄
            ⦃ cp : Coproducts Set ⦄
          (a : Set)
         {_⇨_ : Set → Set → Set} (let infix 0 _⇨_; _⇨_ = _⇨_)
         ⦃ x : Category _⇨_ ⦄ ⦃ y : Cartesian _⇨_ ⦄
         ⦃ f : Cocartesian _⇨_ ⦄
         ⦃ z : monoidCategory {{p}} {{x}} {{y}} a ⦄
         {{ equiv : Equivalent Agda.Primitive.lzero _⇨_ }}

 where



-- open import Data.Unit.Base
-- open import Data.Product
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
-- data _⟹_ : Set → Set → Set₁ where
--   mid : A ⟹ A
--   _m∘_ : (f : B ⟹ C) → (g : A ⟹ B) → (A ⟹ C)
--   m! : A ⟹ ⊤
--   mexl : (A × B) ⟹ A
--   mexr :  (A × B) ⟹ B
--   _m▵_ : (left : A ⟹ C) → (right : A ⟹ D) → (A ⟹ (C × D))
--   madd : ( ℕ × ℕ ) ⟹ ℕ

-- -- a number category
-- data _↝_ : Set → Set →  Set₁ where
--   zero : ⊤ ↝ A
--   one : ⊤ ↝ A
--   add : (A × A) ↝ A
--   max : (A × A) ↝ A
-- open import Function.Base using (id ; _∘_)
-- open import Agda.Builtin.Sigma
-- evaluate : (f : A ⟹ B) → (x : A) → B
-- evaluate mid  = id
-- evaluate (f m∘ g) = (evaluate f) ∘ (evaluate g)
-- evaluate m! x = tt
-- evaluate mexl  = fst
-- evaluate mexr  = snd
-- evaluate (f m▵ g) x = (evaluate f x , evaluate g x)
-- evaluate madd (a , b) = a + b

-- parallelCost : (A ⟹ B) → A → ℕ
-- parallelCost mid a = 0
-- parallelCost (f m∘ g) a = parallelCost f (evaluate g a) + parallelCost g a
-- parallelCost m! a = 0
-- parallelCost mexl a = 0
-- parallelCost mexr a = 0
-- parallelCost (f m▵ g) a = (parallelCost f a) ⊔ (parallelCost g a)
-- parallelCost (madd) x = 1


```

# Tree
Define a tree and methods to reduce the tree

```agda

tree : ℕ → Set →  Set
tree zero a = a
tree (suc n) a = (tree n a) × (tree n a)

reduce : ( n : ℕ ) → (tree n a) ⇨ a
reduce zero  = id
reduce (suc n) = madd z ∘ twice (reduce n)

-- testTree : tree 2 ℕ
-- testTree = (( 1 , 2 ) , (3 , 4))

-- testReduce : parallelCost (reduce 2) testTree ≡ 2
-- testReduce = refl
```
# Auxiliary
Some auxiliary methods that I needed for the proof

```agda
-- maxIdempotent : (n : ℕ) → n ⊔ n ≡ n
-- maxIdempotent zero  = refl
-- maxIdempotent (suc b) = cong suc (maxIdempotent b)



-- addZero : (n : ℕ) → n + 0 ≡ n
-- addZero 0 = refl
-- addZero (suc n) = cong suc (addZero n)
```


# Undeciable

Conal Elliott made me realize that the cost of a lambda term is undeciable, so my previous definition had been wrong.


Also, I realized that it is impossible to get a lower bound on the time of an algorithm, we can only ever get an upper bound on an execution time.

Even if one execution strategy gives one execution time to an algorithm, we have no way of knowing if another execution strategy might give a better time, so we can only
have an upper bound on the time of an algorithm. The datatype `CostLub` gives an upper bound on the cost of a function. `CostLub f x n` is the proposition that the function `f`
can be called on the input `x` in `n` time.

I also created the datatype `Equal` to use in `CostLub`. `Equal f g` is the proposition that the algorithm `f` is equal to the algorithm `g`.


```agda
-- open Equivalence
data Cost : {A : Set} → {B : Set} → (A ⇨ B) → A → ℕ →  Set₁ where
-- the cost of id is 0
  costId : {C : Set}  →  (x : C)  → Cost id x 0
-- the exl of id is 0
  costExl :{C : Set} → {D : Set} → (x : C × D) →  Cost exl x 0
-- the exr of id is 0
  costExr :{C : Set} → {D : Set} → (x : C × D) →  Cost exr x 0
-- the cost of ! is 0
  cost! : {A : Set} → (x : A) → Cost ! x 0
  -- cost∘ : {A B C : Set} → (f : B ⇨  C) → (g : A ⇨ B) → (n : ℕ) → (m : ℕ) → (a : A)  → (x : Cost f (evaluate g a) n) → (y : Cost g a m) → Cost (f ∘ g) a (n + m)
  cost▵  : {A B C : Set} → (f : A ⇨ B) → (g : A ⇨ C) → (n : ℕ) → (m : ℕ) → (a : A)  (x : Cost f a n) → (y : Cost g a m) → Cost (f ▵ g) a (n ⊔ m)
  cost≈  : {A B : Set} → (x : A) → (n : ℕ) → (f : A ⇨ B) → (g : A  ⇨ B) →  f ≈ g → Cost f x n → Cost g x n


record CostFunction  (∥_∥ : {A B : Set} →  A ⇨ B → ℕ) :  Set₁ where
  field
    ∥id∥ : ∥ id ∥ ≡ 0
    ∥exl∥ : ∥ exl ∥ ≡ 0
    ∥exr∥ : ∥ exr ∥ ≡ 0
    ∥!∥ : ∥ ! ∥ ≡ 0
    ∥∘∥ : {A B C : Set} (f : B ⇨ C) (g : A ⇨ B) → ∥ f ∘ g ∥ ≤ ∥ f ∥ + ∥ g ∥
    ∥▵∥ : {A B C : Set} (f : A ⇨ B) (g : A ⇨ C) → ∥ f ▵ g ∥ ≤ ∥ f ∥ ⊔ ∥ g ∥
    ∥≈∥ : {A B : Set} (f g : A ⇨ B) → f ≈ g → ∥ f ∥ ≡ ∥ g ∥

-- well orderign
postulate
  ∥_∥  : {A B : Set} → A ⇨ B → ℕ
  ∥id∥ : ∥ id ∥ ≡ 0
  ∥exl∥ : ∥ exl ∥ ≡ 0
  ∥exr∥ : ∥ exr ∥ ≡ 0
  ∥!∥ : ∥ ! ∥ ≡ 0
  ∥∘∥ : {A B C : Set} (f : B ⇨ C) (g : A ⇨ B) → ∥ f ∘ g ∥ ≤ ∥ f ∥ + ∥ g ∥
  ∥▵∥ : {A B C : Set} (f : A ⇨ B) (g : A ⇨ C) → ∥ f ▵ g ∥ ≤ ∥ f ∥ ⊔ ∥ g ∥
  ∥≈∥ : {A B : Set} (f g : A ⇨ B) → f ≈ g → ∥ f ∥ ≡ ∥ g ∥
  ∥add∥ : ∥ madd z ∥ ≡ 1

data WellOrdering : {A B : Set} → (f : A ⇨ B) → (g : A ⇨ B) → (x : A) → Set₁ where
  <id : {A :  Set} → (f : A ⇨ A ) → (x : A) → WellOrdering id f x
  <exl : {A B : Set} → (f : (A × B) ⇨ A) → (x : A × B) → WellOrdering exl f x
  <exr : {A B : Set} → (f : (A × B) ⇨ B) → (x : A × B) → WellOrdering exr f x
  <! : {A : Set} → (f : A ⇨ ⊤) → (x : A ) → WellOrdering ! f x
  -- <∘ : {A B C : Set} → (f : B ⇨ C) → (g : A ⇨ C) → WellOrdering
  --<▵ :


data WCost : {A : Set} → {B : Set} → (A ⇨ B) → ℕ →  Set₁ where
-- the cost of id is 0
  wcostId :  { A : Set} → WCost {A} {A} id 0
-- the exl of exr is 0
  wcostExl : {C D : Set} →  WCost {C × D} {C} exl 0
-- the exr of exr is 0
  wcostExr : {C D : Set} →  WCost {C × D} {D} exr 0
-- the cost of ! is 0
  wcost! : {A : Set} →  WCost {A} {⊤} ! 0
  wcost∘ : {A B C : Set} (f : B ⇨ C) (g : A ⇨ B) (n m : ℕ) → WCost f n → WCost g m → WCost (f ∘ g) (n + m)
  wcost▵  : {A B C : Set} (f : A ⇨ B) (g : A ⇨ C) (n m : ℕ) → WCost f n → WCost g m → WCost (f ▵ g) (n ⊔ m)
  wcost≈  : {A B : Set}  (n : ℕ) (f g : A ⇨ B) →  f ≈ g → WCost f n → WCost g n



open import Relation.Binary.PropositionalEquality using (subst ; sym)

≤-trans : {m n p : ℕ}  → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n       _          =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)
costReduce : (n : ℕ) → ∥ reduce n ∥ ≤ n
costReduce 0  = subst (λ x → x ≤ 0) (sym ∥id∥) z≤n
costReduce (suc n) = ≤-trans (∥∘∥ (madd z) (twice (reduce n))) {! !}


-- timeLub : (n : ℕ) → (t : tree n ℕ) → (e : (a : ℕ) → (b :  ℕ) → CostLub madd ( a , b) 1) → CostLub (reduce n) t n
-- timeLub 0 a e = LubId a
-- timeLub (suc n) ( a , b ) e rewrite (maxIdempotent n) = LubComp madd ( (reduce n  m∘ mexl) m▵ (reduce n m∘ mexr)) 1 n (a , b) (e (evaluate (reduce n) a) (evaluate (reduce n) b))
--   (subst (λ x → (CostLub ((reduce n m∘ mexl) m▵ (reduce n m∘ mexr)) ( a , b ) x)) (maxIdempotent n)
--   (LubTriangle (reduce n m∘ mexl) (reduce n m∘ mexr) n n (a , b) (subst (λ x → CostLub (reduce n m∘ mexl) (a , b) x) (addZero n) ( LubComp (reduce n) mexl n 0 ((a , b)) (timeLub n a e) (LubExl ((a , b))))) (subst (λ x → CostLub (reduce n m∘ mexr) (a , b) x) (addZero n) (LubComp (reduce n) mexr n 0 ((a , b)) (timeLub n b e) (LubExr ( (a , b)))))))

```
