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


```
