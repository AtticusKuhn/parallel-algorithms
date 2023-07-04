


```agda



open import Felix.Object using (Products ;  Coproducts ;   _×_ ; ⊤ ; _⊎_)
open import Felix.Raw using (Category ; Cartesian ; Cocartesian ; id ; _∘_ ; _▵_ ; twice ; _⊗_ ; inl ; inr ; ! ; _▿_ ; constʳ ; second ; transpose ; exl ; exr ; swap ; first ; dup)
open import Felix.Equiv using (_≈_ ; Equivalent)
module bitoperations
       {level}
       {S : Set level}
     {_⇨_ : S  → S  → Set} (let infix 0 _⇨_; _⇨_ = _⇨_)
     ⦃ x : Category _⇨_ ⦄
         {{ps : Products S}}
     ⦃ y : Cartesian _⇨_ ⦄
         {{ equiv : Equivalent Agda.Primitive.lzero _⇨_ }}
     where



record HasBitOperations (Bit : S) : Set (Agda.Primitive.lsuc level) where
  field
    bit0 bit1 : ⊤ ⇨ Bit
    xor or and : Bit × Bit  ⇨ Bit
    if : {A : S } →  Bit × (A × A) ⇨ A
    -- f(if(A,x,y)) = if(A,f(x), f(y))
    ifdistrib : {A B : S} {f : A ⇨ B } →  f ∘ if {A} ≈ if {B} ∘ second (twice f)
    -- g(if(A,w,x), if(B,y,z)) = if(A, if(B, g(w,x) ,g(w,z)  ), if(B, g(x,y), g(x,z)))
    -- ∀ A , B  if(A, if(B,x,y),z) = if(A ∧ B, x, if(A,y,z))
    -- nestedifswap : if ∘ second (first if) ≈  if ∘ (  ( and ∘ second exl ∘  second exl ) ▵ ())
    -- binaryifdistrib : {A B C : S  } {g : A × B ⇨ C} → g ∘ if
    -- if▵if : {A B C D : S} {f : A ⇨ Bit × (B  × B) } {g : A ⇨ Bit × (C × C)  } { add : B × C ⇨ D } →  add ∘ (if {B} ∘ f ▵ if {C} ∘  g) ≈ if ∘ if ∘ ( (exl ∘ exl ▵ (exl ∘ exr ▵ {! {! !} ∘ twice exr!}) ▵ {!!}) ∘ (f ▵ g))
    -- test : {A B C : S} {g : A × B ⇨ C} → g ∘ (if ∘ f ▵ if ∘ h) ≈ if ∘ (exl ∘ exl ▵  ( {! !} ∘ first exr ) ∘ second if )
    ifredundant : {B : S} → if {B} ∘ second (dup) ≈ exr


```
