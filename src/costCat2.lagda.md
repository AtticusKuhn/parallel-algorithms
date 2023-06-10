
Replacing the monoid instance

```agda

open import Felix.Raw
open import monoid -- hiding (a ; b ; c)
open monoidCategory
open import Data.Nat.Base
open import Felix.Homomorphism
module costCat2
       (a : Set)
          {{ps : Products Set }}
         {_⇨_ : Set  → Set  → Set} (let infix 0 _⇨_; _⇨_ = _⇨_)
         ⦃ x : Category _⇨_ ⦄ ⦃ y : Cartesian _⇨_ ⦄

 where
-- is this a real thing? I just made this up
record totallyOrderedCategory (a : Set) : Set where
  field
    max : a × a ⇨ a
    inc : a ⇨ a
    monoidZero  : ⊤ ⇨ a

open totallyOrderedCategory

functor : {b : Set} → {{e : totallyOrderedCategory b}} → monoidCategory a → monoidCategory (a × b)
functor {{e}} mca = record {
  madd =  (madd mca ⊗ inc e ∘ max e) ∘ transpose
  ; mzero =  mzero mca ▵ monoidZero e
  }
```
