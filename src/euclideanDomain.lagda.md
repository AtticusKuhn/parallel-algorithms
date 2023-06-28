

```agda
open import Felix.Object using (Products ;  Coproducts ;   _×_ ; ⊤ ; _⊎_)
open import Felix.Raw using (Category ; Cartesian ; Cocartesian ; id ; _∘_ ; _▵_ ; twice ; _⊗_ ; inl ; inr ; ! ; _▿_ ; dup ; exl ; exr ; unitorⁱʳ ; second)
open import Felix.Equiv using (_≈_ ; Equivalent)
module euclideanDomain
       {lvl}
       {S : Set lvl}
     {_⇨_ : S  → S  → Set} (let infix 0 _⇨_; _⇨_ = _⇨_)
         {{ps : Products S}}
     ⦃ x : Category _⇨_ ⦄
     ⦃ y : Cartesian _⇨_ ⦄
         {{ equiv : Equivalent Agda.Primitive.lzero _⇨_ }}
     where



record EuclideanDomain (A : S) : Set where
  field
    b0 b1 : ⊤ ⇨ A
    add mul : A × A ⇨ A
    euclideanDivision : A × A ⇨ A × A

  two : ⊤ ⇨ A
  two = add ∘ twice (b1) ∘ dup
  *2 : A ⇨ A
  *2 = add ∘ dup
  /2 : A ⇨ A
  /2 = exl ∘ euclideanDivision ∘ second (two) ∘ unitorⁱʳ
  %2 : A ⇨ A
  %2 = exr ∘ euclideanDivision ∘ second (two) ∘ unitorⁱʳ
```
