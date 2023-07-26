

```agda

{-# OPTIONS --cubical #-}
open import Data.Nat
open import Data.Bool

open import Cubical.Foundations.Isomorphism

open import Cubical.Foundations.Prelude
module cubicalden where
data Parity : Set where
  ⟦_⟧ : ℕ → Parity
  eq : (x : ℕ) → ⟦ suc (suc x) ⟧ ≡ ⟦ x ⟧

ptob : Parity → Bool
ptob ⟦ 0 ⟧ = false
ptob ⟦ 1 ⟧ = true
ptob ⟦ suc (suc x) ⟧ = ptob ⟦ x ⟧
ptob (eq 0 i) = false
ptob (eq 1 i) = true
ptob (eq (suc (suc x)) i) = ptob (eq x i)
btop : Bool → Parity
btop true = ⟦ 1 ⟧
btop false = ⟦ 0 ⟧
secpt : section ptob btop
secpt false i = false
secpt true i = true
retpt : retract ptob btop
retpt ⟦ 0 ⟧ i = ⟦ 0 ⟧
retpt ⟦ 1 ⟧ i = ⟦ 1 ⟧
retpt ⟦ (suc (suc x)) ⟧    =  {!trans!}
retpt (eq zero j) = {!!}
retpt (eq (suc x) j) = {!!}
p=b : Parity ≡ Bool
p=b  =  isoToPath (iso ptob btop secpt retpt)

notP : Parity → Parity
notP ⟦ x ⟧ = ⟦ suc x ⟧
notP (eq x i) = eq (suc x) i
correctType : (Parity → Parity) ≡ (Bool → Bool)
correctType i = (p=b i) → (p=b i)

correct : (transport correctType notP) ≡ Data.Bool.not
correct i false = true
correct i true = false

notnot : (b : Bool) → not (not b) ≡ b
notnot false i = false
notnot true i = true

b=b : Bool ≡ Bool
b=b = isoToPath (iso not not notnot notnot)

bbb=bbb : (Bool → Bool → Bool) ≡ (Bool → Bool → Bool)
bbb=bbb i = b=b i → b=b i → b=b i

orcorrect : (transport bbb=bbb Data.Bool._∨_) ≡ Data.Bool._∧_
orcorrect i false false = false
orcorrect i false true = false
orcorrect i true false = false
orcorrect i true true = true
```
