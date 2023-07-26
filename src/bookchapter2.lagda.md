```agda
module bookchapter2 where
open import Data.Bool
open import Data.Nat
open import Relation.Binary.PropositionalEquality; open ≡-Reasoning
```
Define the parity of a natural number n to be false for even n and true for odd n.
Expressed inductively, zero is even, and the parity of suc n is opposite that of n:
```agda
ℕ′ : Set
ℕ′ = Bool
⟦_⟧ : ℕ → ℕ′
⟦ zero ⟧ = false
⟦ suc n ⟧ = not ⟦ n ⟧
```
If we think of N as representing Bool via this parity interpretation ⟦_⟧, then we would
want to know how to implement the standard boolean operations on N accordingly.
Exercise 2.1. Represent false and true, i.e., define false ′ true ′ : N and
```agda
false′ : ℕ
false′ = 0

true′ : ℕ
true′ = 1
⟦false′⟧ : ⟦ false′ ⟧ ≡ false
⟦false′⟧ = refl
⟦true′⟧ : ⟦ true′ ⟧ ≡ true
⟦true′⟧ = refl
```
Exercise 2.2. Define not ′ : N → N and
```agda
open import Data.Bool.Properties
not′ : ℕ → ℕ
not′ = suc
⟦not′⟧ : ∀ x → ⟦ not′ x ⟧ ≡ not ⟦ x ⟧
⟦not′⟧ 0 = refl
⟦not′⟧ (suc x) rewrite (not-involutive ⟦ x ⟧ ) = refl


sucsuc : ∀ x →  ⟦ suc (suc x) ⟧ ≡ ⟦ x ⟧
sucsuc  x = not-involutive ⟦ x ⟧

open import Agda.Builtin.Nat using (_-_)
not2 : ℕ → ℕ
not2 0 = 1
not2 1 = 0
not2 (suc (suc x)) = suc (suc (not2 x))

not2inv : ∀ x → (not2 (not2 x)) ≡ x
not2inv 0 = refl
not2inv 1 = refl
not2inv (suc (suc x)) rewrite (not2inv x) = refl

⟦not2⟧ : ∀ x → ⟦ not2 x ⟧ ≡ not ⟦ x ⟧
⟦not2⟧ 0 = refl
⟦not2⟧ 1 = refl
⟦not2⟧ (suc (suc x)) rewrite (sucsuc x) | (sucsuc (not2 x)) = ⟦not2⟧ x


_implies_ : Bool → Bool → Bool
true implies false = false
x implies y  = true

_implies′_ : ℕ → ℕ → ℕ
-- (x - 1) * y + (x - 1) + y = (x - 1) * (y + 1) + y = xy + x
x implies′ y = suc (x * y + x)

_⟦implies′⟧_ : ∀ x y → ⟦ x implies′ y ⟧  ≡ ⟦ x ⟧ implies ⟦ y ⟧
zero ⟦implies′⟧ zero = refl
zero ⟦implies′⟧ suc y = refl
suc x ⟦implies′⟧ zero = {!!}
suc x ⟦implies′⟧ suc y = {!!}

```
Exercise 2.3. Define _xor′ _ : N → N → N and
```agda



infixr 6 _xor′_ _⟦xor′⟧_
_xor′_ : ℕ → ℕ → ℕ
_xor′_ = _+_

notxor : ∀ (a b : Bool) → not (a xor b) ≡ not a xor b
notxor true b =  not-involutive b
notxor false b = refl

_⟦xor′⟧_ : ∀ x y → ⟦ x xor′ y ⟧ ≡ ⟦ x ⟧ xor ⟦ y ⟧
0 ⟦xor′⟧ y = refl
(suc x) ⟦xor′⟧ y rewrite (x ⟦xor′⟧ y) = notxor ⟦ x ⟧ ⟦ y ⟧
```
Exercise 2.4. Likewise for conjunction.
```agda
_∧′_ : ℕ → ℕ → ℕ
x ∧′ y = x * y

xor∧not∧ : ∀ (A B : Bool) → B xor A ∧ B ≡ not A ∧ B
xor∧not∧ false false = refl
xor∧not∧ false true = refl
xor∧not∧ true false = refl
xor∧not∧ true true = refl

_⟦∧′⟧_ : ∀ x y → ⟦ x ∧′ y ⟧ ≡ ⟦ x ⟧ ∧ ⟦ y ⟧
0 ⟦∧′⟧ y = refl
(suc x) ⟦∧′⟧ y rewrite (y ⟦xor′⟧ (x * y)) | ( x ⟦∧′⟧ y) =  xor∧not∧ ⟦ x ⟧ ⟦ y ⟧
```
Exercise 2.5. Likewise for disjunction.

```agda
-- (x + 1) * (y + 1) - 1 = xy + x + y + 1 - 1 = xy + x + y



open import Data.Nat.Properties
SFFT : ∀ x y → (((suc x) * (suc y))   - 1) ≡ (x * y + x + y)
SFFT x y rewrite (*-comm (x) (suc y)) | (+-comm (y) (x + y * x)) | (+-comm (x) (y * x)) | (*-comm y x) = refl
∨false : ∀ (A : Bool) → A ≡ A ∨ false
∨false false = refl
∨false true = refl
_∨′_ : ℕ → ℕ → ℕ
x ∨′ y = x * y + x + y
xor∧not : ∀ (x y : Bool) → y xor x ∧ not y ≡ x ∨ y
xor∧not false false = refl
xor∧not false true = refl
xor∧not true false = refl
xor∧not true true = refl
_⟦∨′⟧_ : ∀ x y → ⟦ x ∨′ y ⟧ ≡ ⟦ x ⟧ ∨ ⟦ y ⟧
x ⟦∨′⟧ y rewrite (sym (SFFT x y)) | (y ⟦xor′⟧ (x * suc y)) | ( x ⟦∧′⟧ (suc y)) = xor∧not ⟦ x ⟧ ⟦ y ⟧
-- 0 ⟦∨′⟧ 0 = refl
-- 0 ⟦∨′⟧ (suc y) = refl
-- (suc x) ⟦∨′⟧ 0 rewrite (*-zeroʳ x) | (+-identityʳ x) = ∨false (not ⟦ x ⟧ )
-- (suc x) ⟦∨′⟧ (suc y)  rewrite  (sym (SFFT (suc x) (suc y)))   = {! !}
```
3
4 Chapter 2. Parity
Does N form a boolean algebra using the primed operations above? The question
is subtler than in Chapter 1, as the following two exercises capture.
Exercise 2.6. Show that not ′ fails to satisfy the self-inverse (involutive) property of
not if we use propositional equality on the representation (N).
```agda
open import Data.Empty
notfailinvolute : ∀ x → not′ (not′ x) ≢  x
notfailinvolute x  = λ ()
```

This failure seems worrisome, but the problem is only that we used the wrong notion
of equivalence on representations. Since natural numbers represent booleans via ⟦_⟧,
distinguishing numbers with the same parity is an abstraction leak. Instead (and in
general), representations should be considered equivalent exactly when their meanings
are:
```agda
infix 0 _≈_
_≈_ : ℕ → ℕ → Set
x ≈ y = ⟦ x ⟧ ≡ ⟦ y ⟧
```
Exercise 2.7. Assuming semantic equivalence (_≈_), prove that not′ is involutive.

```agda
not′inv : ∀ x → not′ (not′ x) ≈ x
not′inv x = sucsuc x
```

Exercise 2.8. Assuming semantic equivalence, prove that _∧ ′ _ is associative, com-
mutative, and idempotent, as well as other laws of a boolean algebra.
```agda
∧′-assoc : ∀ x y z → (x ∧′ y) ∧′ z ≈ x ∧′ (y ∧′ z)
∧′-assoc x y z rewrite (*-assoc x y z) = refl

∧′-comm : ∀ x y → x ∧′ y ≈ y ∧′ x
∧′-comm x y rewrite (*-comm x y) = refl
∧′-idem : ∀ x → x ∧′ x ≈ x
∧′-idem x rewrite (x ⟦∧′⟧ x) = ∧-idem ⟦ x ⟧

```
Were we just lucky that all of the usual properties of booleans hold on N modulo
semantic equivalence? No:
Exercise 2.9. Assuming semantic equivalence, prove some of the boolean algebra laws
by appealing only to the homomorphism properties and the corresponding laws for the
denotation (Bool), i.e., without using the specific primed definitions.

```agda
∧′-assoc2 : ∀ x y z  → (x ∧′ y) ∧′ z ≈ x ∧′ (y ∧′ z)
∧′-assoc2 x y z rewrite  ((x ∧′ y) ⟦∧′⟧ z) | (x ⟦∧′⟧ y) | (x ⟦∧′⟧ (y ∧′ z)) | (y ⟦∧′⟧ z)  = ∧-assoc ⟦ x ⟧ ⟦ y ⟧ ⟦ z ⟧
∧′-comm2 :  ∀ x y → (x ∧′ y) ≈ (y ∧′ x)
∧′-comm2 x y rewrite (x ⟦∧′⟧ y) | (y ⟦∧′⟧ x) = ∧-comm ⟦ x ⟧ ⟦ y ⟧


∨′-comm :  ∀ x y → (x ∨′ y) ≈ (y ∨′ x)
∨′-comm x y rewrite (x ⟦∨′⟧ y) | (y ⟦∨′⟧ x) = ∨-comm ⟦ x ⟧ ⟦ y ⟧

∧′0 : ∀ x → x ∧′ false′ ≈ false′
∧′0 x rewrite (∧′-comm2 x false′) | (false′ ⟦∧′⟧ x ) = refl
∨′1 : ∀ x → x ∨′ true′ ≈ true′
∨′1 x rewrite (∨′-comm x true′) | (true′ ⟦∨′⟧ x ) = refl
∨′0 : ∀ x → x ∨′  false′  ≈ x
∨′0 x rewrite (∨′-comm x false′)  | ⟦false′⟧ = refl
∨′same : ∀ x → x ∨′ x ≈ x
∨′same x rewrite (x ⟦∨′⟧ x) = ∨-idem ⟦ x ⟧
∧′same :  ∀ x → x ∧′ x ≈ x
∧′same x rewrite (x ⟦∧′⟧ x) = ∧-idem ⟦ x ⟧
∧′not : ∀ x → x ∧′ not′ x ≈ false′
∧′not x  rewrite (x ⟦∧′⟧ (not′ x))  = ∧-inverseʳ ⟦ x ⟧

demorgan∨ : ∀ (x y : Bool) → not (x ∨ y) ≡ not x ∧ not y
demorgan∨ false y = refl
demorgan∨ true y = refl
demorgan∧ : ∀ (x y : Bool) → not (x ∧ y) ≡ not x ∨ not y
demorgan∧ false y = refl
demorgan∧ true y = refl
-- ∨′-comm : ∀ x y → x ∨′ y ≈ y ∨′ x
demorgan′∨ : ∀ x y → not′ (x ∨′ y) ≈ not′ x ∧′ not′ y
demorgan′∨ x y rewrite  (⟦not′⟧ (x ∨′ y)) | (⟦not′⟧ x) | (⟦not′⟧ y) | (x ⟦∨′⟧ y) | (((not′ x ) ⟦∧′⟧ (not′ y) ))   = demorgan∨ ⟦ x ⟧ ⟦ y ⟧
demorgan′∧ : ∀ x y → not′ (x ∧′ y) ≈ not′ x ∨′ not′ y
demorgan′∧ x y rewrite (⟦not′⟧ (x ∧′ y)) | ((not′ x) ⟦∨′⟧ (not′ y)) | (x ⟦∧′⟧ y)  = demorgan∧ ⟦ x ⟧ ⟦ y ⟧


-- Correct : (f : Bool → Bool → Bool) → Set
-- Correct f =

-- _∧2_ : Correct _∧_
```
The upshot of this result is that equational properties reliably transport from model to
implementation, as long as we use semantic equivalence and homomorphic correctness.
There is thus only one property we ever need care about: (homomorphically defined)
correctness. Correctness implies laws but not vice versa.
