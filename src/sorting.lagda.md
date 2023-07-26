
```agda
open import Data.Nat hiding (_≤_)
open import Data.Nat.Properties
open import Data.Fin hiding (_≤_)
open import Data.Vec
open import Data.Product
open import Relation.Binary.PropositionalEquality using (cong ; _≡_ ; subst ; refl)
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Bool hiding (_≤_)
open import Relation.Binary using (Decidable)
open import Relation.Nullary using (Dec; yes; no)
open import ordered
open Ordered


module sorting  where
-- open Ordered ordA

-- vec : ℕ → Set → Set
-- vec n A = Fin n → A
variable
  n : ℕ
  A : Set
  xs ys : Vec A n




-- record Ordered (A : Set) : Set₁ where
--   infix 7 _O≤_
--   field
--     _O≤_ : A → A → Set
--     id : {a : A } → a O≤ a
--     trans : {a b c : A} → a O≤ b → b O≤ c → a O≤ c

-- Ordered : Set → Set₁
-- Ordered A = A → A → Set

-- open Ordered

record OrderedHomomorphism {A B : Set} ⦃ ordA : Ordered A ⦄ ⦃ ordB : Ordered B ⦄  (f : A → B) : Set₁ where
  field
    distrib : ∀ (x y : A) → (_≤_ ordA x y ) ≡ _≤_ ordB (f x) (f y)

sameElements : Vec A n  → Vec A n → Set
sameElements {A} {n}  x y = ∀ (i : Fin n) → ∃  (λ j  →   lookup x i ≡ lookup y j)


compFin : {n : ℕ} → Fin n → Fin n → Set
compFin zero zero = ⊤
compFin (suc i) zero = ⊥
compFin zero (suc i) = ⊤
compFin (suc i) (suc j) = compFin i j
-- instance
orderedFin : Ordered (Fin n)
orderedFin = {!!}
  -- orderedFin = record {
  --   _O≤_ = λ i j →  i Data.Fin.≤ j
  --   }
isSorted :  ⦃ _ : Ordered A ⦄ → Vec A n → Set₁
isSorted xs = OrderedHomomorphism ⦃ orderedFin ⦄ (lookup xs)

sortedVersion : ⦃ _ : Ordered A ⦄ → Vec A n → Vec A n → Set₁
sortedVersion  x y = (isSorted y) × (sameElements x y)


-- vec0 : vec zero A
-- vec0 ()
open DecOrdered
min : ⦃ o : Ordered A ⦄ ⦃ d : DecOrdered A ⦄ → A → A → A
min  ⦃ o ⦄  ⦃ d ⦄  a b with decid d a b
...   | yes _ = a
...   | no _ = b
max :  ⦃ o : Ordered A ⦄ ⦃ d : DecOrdered A ⦄ → A → A → A
max  ⦃ d =  d ⦄  a b with decid d a b
...   | yes _ = b
...   | no _ = a
-- min a b =
minPartition :  {n : ℕ} → ⦃ _ : Ordered A ⦄ → ⦃ DecOrdered A ⦄ →  Vec A (suc n) → A × Vec A n
minPartition {n = zero} (xs ∷ [])  = ( xs , []   )
minPartition {A} {n = suc n}  (x ∷ xs) = min x (proj₁ res) ,    max x (proj₁ res)  ∷ (proj₂ res)
  where
    res : A × Vec A ( n)
    res = minPartition xs
  -- where
    -- res : A × vec (suc n) A
    -- res =
-- min : ⦃vec n A → A
sort : {n : ℕ} → ⦃ _ : Ordered A ⦄ → ⦃ DecOrdered  A ⦄ →  Vec A n → Vec A n
sort {n = 0} xs = xs
sort {A} {n = suc n} xs = (proj₁ res) ∷ sort (proj₂ res)
  where
    res : A × Vec A n
    res = minPartition xs

instance
  orderedℕ : Ordered ℕ
  orderedℕ = record {
    _≤_ = Data.Nat._≤_
    ; id = ≤-refl
    ; trans = ≤-trans
    }
  Decℕ : DecOrdered ℕ
  Decℕ = record {
    decid = Data.Nat.Properties._≤?_
    }
-- sort {n = 0} _≤_ xs = xs
-- sort {n = 1} _≤_ xs = xs
-- sort {n = suc n} _≤_ xs zero =  {!!}
-- sort {n = suc n} _≤_ xs (suc i) =  {!!}
test : Vec ℕ 10
test = sort {ℕ}  (3 ∷ 1 ∷ 2 ∷  5 ∷ 6 ∷ 1 ∷ 8 ∷ 12 ∷ 21 ∷ 2 ∷ [] )

-- emptyfin : Fin 0
-- emptyfin ()
absurdFin : {A : Set} → Fin 0 → A
absurdFin ()

spec : ⦃ _ : Ordered A ⦄ → ⦃ _ : DecOrdered A ⦄ →  (xs : Vec A n) → sortedVersion xs (sort xs)
spec [] = record { distrib = λ x y → refl} , λ i →  absurdFin i
spec ( x ∷ xs ) = (record { distrib = λ x₁ y → {!!} }) , (λ i → {!!} , {!!})
```
