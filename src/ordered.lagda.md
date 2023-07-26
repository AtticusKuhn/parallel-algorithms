

```agda
open import Relation.Nullary using (Dec; yes; no)

module ordered where

record Ordered (A : Set) : Set₁ where
  infix 7 _≤_
  field
    _≤_ : A → A → Set
    id : {a : A } → a ≤ a
    trans : {a b c : A} → a ≤ b → b ≤ c → a ≤ c

record DecOrdered (A : Set) ⦃ ordA : Ordered A ⦄ : Set₁ where
  field
    decid : (a b : A) → Dec (Ordered._≤_ ordA a b)


```
