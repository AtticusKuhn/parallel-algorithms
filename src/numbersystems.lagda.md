
```agda

{-# OPTIONS --cubical #-}
module numbersystems where

open import Cubical.Core.Everything

data ℕ : Type where
  Z : ℕ
  _+1 : ℕ → ℕ

_+ℕ_ : ℕ → ℕ → ℕ
Z +ℕ y = y
(x +1 ) +ℕ y = (x +ℕ y) +1

data ℤ : Type where
  _-_ : ℕ → ℕ →  ℤ
  sucdiff : (m n : ℕ) → m - n ≡ (m +1) - (n +1)

five : ℕ
five = Z +1 +1 +1 +1 +1
two : ℕ
two = Z +1 +1
three : ℕ
three = Z +1 +1
trans : {A : Type} {a b c : A} → (a ≡ b) → (b ≡ c) → (a ≡ c)
trans (a=b) (b=c) i =   {!!}

sym : {A : Type} {a b : A} → a ≡ b → b ≡ a
sym a=b i = a=b (~ i)
-- testeq : (five - two) ≡ (three - Z)
-- testeq = trans (sucdiff {!!} {!!}) {!!}

ℤsuc : ℤ → ℤ
ℤsuc (a - b) = (a +1) - b
ℤsuc (sucdiff m n i) = sucdiff (m +1) n i

ℤpred : ℤ → ℤ
ℤpred (a - b) = a - (b +1)
ℤpred (sucdiff m n i) = sucdiff m (n +1) i


_ℕ+ℤ_ : ℕ → ℤ → ℤ
x ℕ+ℤ (a - b) = (a +ℕ x) - b
x ℕ+ℤ (sucdiff m n i) = sucdiff (m +ℕ x) n i

_+ℤ_ : ℤ  → ℤ → ℤ
(a - b) +ℤ y =  {!!} -- (a ℕ+ℤ y) - b
(sucdiff a b i) +ℤ y = {!!}

ℤtest : ℤ
ℤtest = ℤsuc (Z - Z)



data modN (n : ℕ) : Type where
  _%n : ℕ → modN n
  addmod : (a b : ℕ) → (a) %n ≡ (a +ℕ b) %n

data Bin : Type where
    b0 : Bin
    _*2 : Bin → Bin
    _*2+1 : Bin → Bin
    0*2 : b0 *2 ≡ b0

double : Bin → Bin
double x = x *2
refl : {A : Type} {x : A} → x ≡ x
refl {x = x} i = x
sucBin : Bin → Bin
sucBin b0 = b0 *2+1
sucBin (x *2) = x *2+1
sucBin (x *2+1) = (sucBin x) *2
sucBin (0*2 i) =  b0 *2+1


_+B_ : Bin → Bin → Bin
b0 +B y = y
x +B b0 = x
(x *2) +B (y *2) = (x +B y) *2
(x *2) +B (y *2+1) = (x +B y) *2+1
(x *2+1) +B (y *2) = (x +B y) *2+1
(x *2+1) +B (y *2+1) = (sucBin (x +B y)) *2
x +B y = {!x y!}


_l=_ : {A : Set} → A → A → Set₁
_l=_ {A} a b = ∀ (P : A → Set) → P a → P b

syml= : {A : Set} (a b : A) → a l= b → b l= a
syml= a b al=b P x = {!!}

funextl= : {A B : Set} → (f g : A → B) →  (∀ (x : A) → f x l= g x) → f l= g
funextl= f g x P a = {!!}


-- record Nats  : Set where
--   field
--     N : Set
--     zero : ⊤ ⇨ N
--     sucN : N ⇨ N
--     elim : {X : Set } → (⊤ ⇨ X) → (N ⇨ X) → N ⇨ X

-- addN : N × N


```
