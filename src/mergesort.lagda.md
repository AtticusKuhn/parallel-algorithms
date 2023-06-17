

An experiment with mergesort, we'll see if this works or not.

```agda

open import Data.Nat.Base using (ℕ ; suc ; _+_ ; _^_)
open import Felix.Object using (Products ;  Coproducts ;   _×_ ; ⊤ ; _⊎_)
open import Felix.Raw using (Category ; Cartesian ; id ; _∘_ ; _▵_ ; twice ; _⊗_ )
open import Relation.Binary.PropositionalEquality using (cong ; _≡_ ; subst)
module mergesort
     -- (A : Set)
       {{ps : Products Set }}
       {{cps : Coproducts Set }}
     {_⇨_ : Set  → Set  → Set} (let infix 0 _⇨_; _⇨_ = _⇨_)
     ⦃ x : Category _⇨_ ⦄ ⦃ y : Cartesian _⇨_ ⦄
     -- ⦃ z : monoidCategory {{p}} {{x}} {{y}} a ⦄
     where



variable
  A B C D : Set
  n : ℕ


tree : ℕ → Set → Set
tree 0 A = A
tree (suc n) A = (tree n A) × (tree n A)


list : ℕ → Set → Set
list 0 A = A
list (suc n) A = A × (list n A)


Bool : Set
Bool = ⊤ ⊎ ⊤

record Comparable (a : Set) : Set₁ where
  field
    compare :   ( A × A ) ⇨ Bool
-- zerotimes : (n : ℕ) →   ((2 ^ n) + 0 Data.Nat.Base.* (2 ^ n)) ≡ (2 ^ n)

zerotiems : (n : ℕ)  → (2 ^ n) + 0 Data.Nat.Base.* (2 ^ n) ≡ ℕ.zero

eq : (n : ℕ) →  (2 ^ n) + (2 ^ n) ≡ 2 ^ (suc n)

mergeL : {{Comparable A}} → (n m : ℕ) → (list n A × list m A) ⇨ list (n + m) A
mergeL n m = {! !}



flatten : (n : ℕ ) →  tree n A ⇨ list (2 ^ n) A

parse : (n : ℕ) → list (2 ^ n) A ⇨ tree n A


merge : {A : Set}  → {{ Comparable A  }}  → (n : ℕ) → (tree n A) ⇨ (tree n A)
merge 0 = id
merge {A}  (suc n) = (subst (λ m → list m A ⇨ tree n A) {! !} (parse ( n)) ) ∘ (mergeL (2 ^ n) (2 ^ n)) ∘ (twice (flatten n))
mergesort : {{Comparable A}} → (n : ℕ) → (tree n A) ⇨ (tree n A)
mergesort 0 = id 
mergesort (suc n ) = (merge (suc n)) ∘ twice (mergesort n)

```
