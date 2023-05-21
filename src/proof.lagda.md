

I think this file is only, ignore this.



```agda
import cartesian
import monoid
open import Data.Nat.Base
open import Felix.Instances.Function.Raw
open import Felix.Instances.Function.Type
open import Data.Sum
open import Data.Product
open Felix.Instances.Function.Raw.→-instances
open import Felix.Object hiding  ( _×_ )
open import Felix.Raw  hiding (_⊎_ ; _×_)
-- open Felix.Instances.Function.Type.→-instances
open →-raw-instances

open import Agda.Builtin.Sigma
instance
  monoidNat : monoid.monoidCategory {obj = Set} ⦃ prodmon = products Agda.Primitive.lzero ⦄ {_⇨_ = λ A B → A → B} ⦃ bruhcat = category Agda.Primitive.lzero ⦄ ⦃ brucat = cartesian Agda.Primitive.lzero ⦄ ℕ
  monoidNat = record
    { madd = λ x → (fst x) + (snd x)
    ; mzero = λ t → 0}

instance
  ps : Products Set
  ps = products Agda.Primitive.lzero
  pc : Coproducts Set
  pc = coproducts Agda.Primitive.lzero
  cat : Category (λ A B → (A × ℕ)  →  (B × ℕ) )
  cat = record
    { id = id
    ; _∘_ = λ a b  → a ∘ b }
  catcar : Cartesian (λ A B → (A × ℕ)  →  (B × ℕ) )
  catcar =  record
    {  _▵_ = λ A B → (A , B)
    ; exl = proj₁
    ; exr = proj₂ }
  catcarco : Cocartesian (λ A B → (A × ℕ)  →  (B × ℕ) )
  catcarco = cocartesian Agda.Primitive.lzero





```
