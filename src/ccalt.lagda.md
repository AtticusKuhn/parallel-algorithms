```agda
open import Felix.Raw hiding (_⊗_ ; ! ; dup ; second  ; first ; _▵_ ; exl ; exr)
open import Level using (Level; _⊔_; suc)

module ccalt where

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj obj₁ obj₂ : Set o
    a b c d e s : obj

record Braided {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ)
         ⦃ _ : Category _⇨′_ ⦄
    : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  infixr 7 _⊗_
  field
    _⊗_ : (a ⇨ c) → (b ⇨ d) → (a × b ⇨ c × d)
  first : (a ⇨ b) → (a × c ⇨  b × c)
  first f = f ⊗ id
  second : (a ⇨ b) → ( c × a ⇨   c × b)
  second f = id ⊗ f
open Braided ⦃ … ⦄ public


record AlternateCartesian
       {obj : Set o}
       ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ)
         ⦃ _ : Category _⇨′_ ⦄
         ⦃ _ : Braided _⇨′_ ⦄
    : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ! : a ⇨ ⊤
    dup : a ⇨ a × a
  infixr 7 _▵_
  _▵_ : (a ⇨ c) → (a ⇨ d) → (a ⇨ c × d)
  f ▵ g = (f ⊗ g) ∘ dup
  exl : a × b ⇨ a × ⊤
  exl = second !
  exr : a × b ⇨ ⊤ × b
  exr = first !

open AlternateCartesian ⦃ … ⦄ public

open import Data.String
record StringCategory
       {obj : Set o}
       (string : obj)
       ⦃ _ : Products obj ⦄
       (_⇨′_ : obj → obj → Set ℓ)
       ⦃ _ : Category _⇨′_ ⦄
       : Set (o ⊔ ℓ) where
    private infix 0 _⇨_; _⇨_ = _⇨′_
    field
      stringLiteral : (String) → (⊤ ⇨  string)
      concatenateStrings : string × string ⇨ string

open StringCategory ⦃ … ⦄ public
record ConsoleCategory
       {obj : Set o}
       (console : obj)
       (string : obj)
       ⦃ _ : Products obj ⦄
       (_⇨′_ : obj → obj → Set ℓ)
       ⦃ _ : Category _⇨′_ ⦄
       ⦃ _ : Braided _⇨′_ ⦄
    : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    printLineConsole : console × string ⇨ console
    readLineConsole : console ⇨ console × string

open ConsoleCategory ⦃ … ⦄ public

postulate
  unitor : { obj : Set o } {C : obj} ⦃ _ : Products obj ⦄ {_⇨_ : obj → obj → Set ℓ } ⦃ _ : Category _⇨_ ⦄  → (C ⇨ (C × ⊤))
infixr 7 _>>_
_>>_ : { obj : Set o  } {a b c : obj} {_⇨_ : obj → obj → Set ℓ} ⦃ _ : Category _⇨_ ⦄ → (a ⇨ b) → (b ⇨ c) → (a ⇨ c)
f >> g = g ∘ f
greetUserProgram : { obj : Set o } {C S : obj} ⦃ _ : Products obj ⦄ {_⇨_ : obj → obj → Set ℓ } ⦃ _ : Category _⇨_ ⦄ ⦃ _ : Braided _⇨_ ⦄ ⦃ _ : ConsoleCategory C S _⇨_ ⦄ ⦃ _ : StringCategory S _⇨_ ⦄ → (C ⇨ C)
greetUserProgram =
  unitor
  >> second (stringLiteral "What is your name?")
  >> printLineConsole
  >> readLineConsole
  >> second (unitor >> second (stringLiteral "Greetings, ") >> concatenateStrings)
  >>  printLineConsole

```
