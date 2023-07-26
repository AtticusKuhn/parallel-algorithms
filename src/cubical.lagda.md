# Cubical

An experiment with using Cubical agda!

My idea is that using higher inductive types (HITs) can make illegal code unwritable, i.e.
any code that uses _⟹_ **must** respect the identities that id ∘ f = f, for example.


```agda
{-# OPTIONS --cubical #-}
open import Data.Unit.Base
open import Data.Product
open import Data.Nat.Base
-- open import Agda.Builtin.Equality
-- open import Relation.Binary.PropositionalEquality
-- open import Cubical.Foundations.Equiv
open import Cubical.Core.Everything
variable
  A B C D  : Set
data _⟹_ : Set → Set → Set₁ where
  id : A ⟹ A
  _∘_ : (f : B ⟹ C) → (g : A ⟹ B) → (A ⟹ C)
  ! : A ⟹ ⊤
  exl : (A × B) ⟹ A
  exr :  (A × B) ⟹ B
  _▵_ : (left : A ⟹ C) → (right : A ⟹ D) → (A ⟹ (C × D))
  add : ( ℕ × ℕ ) ⟹ ℕ
  leftid : (f : A ⟹ B) →  id ∘ f  ≡ f
  rightid : (f : A ⟹ B) → f ∘ id  ≡ f
  assoc : (f : C ⟹ D) → (g : B ⟹ C) → (h : A ⟹ B) → f ∘ ( g ∘ h ) ≡ (f ∘ g) ∘ h

import Function.Base  as f using (id ; _∘_)
open import Agda.Builtin.Sigma
evaluate : (f : A ⟹ B) → (x : A) → B
evaluate id  = λ x → x
evaluate (f ∘ g) = (evaluate f) f.∘ (evaluate g)
evaluate ! x = tt
evaluate exl  = fst
evaluate exr  = snd
evaluate (f ▵ g) x = (evaluate f x , evaluate g x)
evaluate add (a , b) = a + b
evaluate (leftid f i) x = evaluate f x
evaluate (rightid f i) x = evaluate f x
evaluate (assoc f g h i) x  = evaluate f ( evaluate g ( evaluate h x ) )


data Parity : Set where
  ⟦_⟧ : ℕ → Parity
  eq : (x : ℕ) → ⟦ suc (suc x) ⟧ ≡ ⟦ x ⟧

open import Data.Bool

open import Cubical.Foundations.Isomorphism

open import Cubical.Foundations.Prelude using (transport ; refl)
odd : ℕ → Bool
odd 0 = false
odd 1 = true
odd (suc (suc x)) = odd x
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
retpt ⟦ (suc (suc x)) ⟧    =  {!!}
retpt (eq zero j) = {!!}
retpt (eq (suc x) j) = {!!}
p=b : Parity ≡ Bool
p=b  =  isoToPath (iso (ptob) btop secpt retpt)
-- _xorP_ : Parity → Parity → Parity
-- ⟦ a ⟧ xorP ⟦ b ⟧ = ⟦ a + b ⟧
-- (eq x i) xorP ⟦ y ⟧ =  {!!} -- eq (x * y) i
-- ⟦ a ⟧ xorP (eq x i) = {!!} -- eq (a * x ) i
-- (eq x i) xorP (eq y j) = {!!}

notP : Parity → Parity
notP ⟦ x ⟧ = ⟦ suc x ⟧
notP (eq x i) = eq (suc x) i
correctType : (Parity → Parity) ≡ (Bool → Bool)
correctType i = (p=b i) → (p=b i)

-- ∀correct : (x : Parity) → (y : Bool) → (PathP (λ i → p=b i) x y ) → PathP (λ i → p=b i) (notP x) (Data.Bool.not y)
-- ∀correct x y x=y i = {!!}
correct : (transport correctType notP) ≡ Data.Bool.not
correct i false = true
correct i true = false

-- record isCorrect {A B : Type} (f : A → B ) ⦃ x :  A ≡ C ⦄ ⦃ y : B ≡ D ⦄
--   field
--     g : C → D
--     gcor :

notnot : (b : Bool) → not (not b) ≡ b
notnot false i = false
notnot true i = true

b=b : Bool ≡ Bool
b=b = isoToPath (iso not not (notnot) (notnot))
bbb=bbb : (Bool → Bool → Bool) ≡ (Bool → Bool → Bool)
bbb=bbb i = b=b i → b=b i → b=b i
orcorrect : (transport bbb=bbb Data.Bool._∨_) ≡ Data.Bool._∧_
orcorrect i false false = false
orcorrect i false true = false
orcorrect i true false = false
orcorrect i true true = true

-- orcorrect : (Data.Bool._∨_) ≡ (Data.Bool._∧_)
-- orcorrect i false false = {!!}
-- orcorrect i false true = {!!}
-- orcorrect i true false = {!!}
-- orcorrect i true true = {!!}



--

data ℤ : Set where
  _-_ : ℕ → ℕ → ℤ
  eq : (a b : ℕ) →  a - b ≡  (suc a)  - (suc b)

five : ℤ
five = 5 - 0
minustwo : ℤ
minustwo = 0 - 2

inv : {a b : ℕ} → (suc a ) Data.Nat.Base.≤ (suc b) → a Data.Nat.Base.≤ b
inv (s≤s x) = x


-- sec : (a b : ℕ) → (p : (suc a) Data.Nat.Base.≤ (suc b) ) → s≤s ( inv p) ≡ p
-- sec a b p i = {!!}
-- 0≤_ : ℤ → Type
-- 0≤ (a - b) = a Data.Nat.Base.≤ b
-- 0≤ (eq a b i) = isoToPath (iso (s≤s {a} {b}) inv (sec a b) λ a₁ i₁ → a₁) i
-- addℤ : ℤ → ℤ → ℤ
-- addℤ (a - b) (x - y) =  ( a + x) - (b + y)
-- addℤ (p - q) (eq a b i) =  {!!} --eq (p + a) (q + b) i
-- addℤ (eq a b i) (p - q) =  eq (a + p) (b + q) i
-- addℤ (eq a b i) (eq x y j) =  {!!}

-- test : ℤ
-- test = addℤ five minustwo
-- open import Cubical.HITs.SetQuotients
-- ℤ1 : Type
-- ℤ1 = (ℕ × ℕ) / rel
--   where
--   rel : ℕ × ℕ → ℕ × ℕ → Type
--   rel (x₀ , y₀) (x₁ , y₁) = x₀ + y₁ ≡ x₁ + y₀


-- sucℤ : ℤ1 → ℤ1
-- sucℤ [ pos , neg ] =  [ suc pos , neg ]
-- sucℤ (eq/ a b r i) = {!!}
-- sucℤ (squash/ x x₁ p q i i₁) = {!!}

-- data _/_ (A : Type) (R : A → A → Type) : Type where
--   [_] : A → A / R
--   eq/ : (a b : A) → R a b → [ a ] ≡ [ b ]
--   trunc : isSet (A / R)
```
