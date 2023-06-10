I don't know any more


```agda

open import Felix.Raw
open import monoid -- hiding (a ; b ; c)
open monoidCategory
open import Data.Nat.Base
module costCat
          (a : Set)
          {{ps : Products Set }}
          {{pa : Products a }}
             --⦃ p : Products (a × ℕ) ⦄
            -- ⦃ cp : Coproducts Set ⦄
         {_⇨_ : a  → a  → Set} (let infix 0 _⇨_; _⇨_ = _⇨_)
         ⦃ x : Category _⇨_ ⦄ ⦃ y : Cartesian _⇨_ ⦄
         -- ⦃ z : monoidCategory {{p}} {{x}} {{y}} a ⦄
         (b : a)

 where


_↦_ : a → a → Set
A ↦ B = (A × b) ⇨ (B × b)

instance
  category : Category _↦_
  category = record {
    id = id {{x}}
    ; _∘_ = _∘_ {{x}}
    }

  prods : Products a
  prods = record {
    _×_ = λ A B → Products._×_  pa ( A × b ) ( B × b )
    ; ⊤ = Products._×_ pa (Products.⊤ pa)  b
    }

  prods2 : Products a
  prods2 = record {
    _×_ = λ A B → Products._×_  pa ( A × b ) ( B × b )
    ; ⊤ = (Products.⊤ pa)
    }

  prods3 : Products Set
  prods3 = record {
     _×_ = λ A b →  Products._×_  ps ℕ ℕ
    ; ⊤ = Products.⊤ ps
    }


  cart2 : Cartesian {{prods3}} _⇨_
  cart2 = record {
    ! = ! {{y}}
    }
  !' : {A : a} → A ↦  (Products.⊤ pa)
  !' =  _▵_ {{pa}} {{x}} (! {{pa}} {{x}}) (exr {{pa}} )


  cartesian : Cartesian {{prods2}} _↦_
  cartesian = record {
    ! = !'
    ; _▵_ =  _▵_ {{pa}}
    ; exl =  (exl) {{pa}}
    ; exr =  _∘_ {{x}} (exl {{pa}} {{x}}) (exr {{pa}} {{x}})
    }





```
