We’ll need some basic imports from the Agda standard library:
```agda
module bookchapter1 where
open import Data.Bool
open import Relation.Binary.PropositionalEquality
private variable x y : Bool
```
As a first simple example of compositionally correct computation, let’s consider
representing booleans by their negations. This choice might sound silly at first, but it’s
close to a popular technique in hardware design, referred to as “negative logic”.1 By
convention—but not necessity—we’ll refer to the interpretation function as “⟦_⟧”:
```agda
⟦_⟧ : Bool → Bool
⟦_⟧ = not
```
Each of the conventional (positive) boolean operations has a negative counterpart.
For instance, the negative representation of false is true and vice verse
```agda
false′ : Bool
false′ = true
true′ : Bool
true′ = false
```
The correctness theorems are that false ′ represents false and true ′ represents true via
our negative interpretation:
```agda
⟦false′⟧ : ⟦ false′ ⟧ ≡ false
⟦false′⟧ = refl
⟦true′⟧ : ⟦ true′ ⟧ ≡ true
⟦true′⟧ = refl
```
1 Really, “negative logic” refers to interpretations of continuous electrical voltages as booleans,
specifically with low voltages corresponding to ‘true‘ and high voltages to ‘false‘, and opposed to the
reversed interpretation, known as “positive logic”.
1
2 Chapter 1. Negative Logic
Exercise 1.1. Define ⟦false ′ ⟧ and ⟦true′ ⟧, thus proving correctness of false ′ and true ′ .
More generally, correctness for operations with arguments requires that the meaning
function distributes over the operations:
```agda
not′ : Bool → Bool
not′ true = false
not′ false = true
⟦not′⟧ : ∀ x → ⟦ not′ x ⟧ ≡ not ⟦ x ⟧
⟦not′⟧ true = refl
⟦not′⟧ false = refl
```
Exercise 1.2. Define not’ (implementation) and ⟦not′ ⟧ (correctness proof).
Conjunction follows the same pattern but with two arguments:
```agda
infixr 6 _∧′_ _⟦∧′⟧_
_∧′_ : Bool → Bool → Bool
false ∧′ y = y
true ∧′ y = true
_⟦∧′⟧_ : ∀ x y → (⟦ (x ∧′ y) ⟧) ≡ ⟦ x ⟧ ∧ ⟦ y ⟧
false ⟦∧′⟧ y = refl
true ⟦∧′⟧ y = refl
```
Exercise 1.3. Define _∧′_ and ⟦_∧ ′ _⟧.
Exercise 1.4. Likewise for disjunction.
```agda
infixr 6 _∨′_ _⟦∨′⟧_
_∨′_ : Bool → Bool → Bool
false ∨′ y = false
true ∨′ y = y
_⟦∨′⟧_ : ∀ x y → (⟦ (x ∨′ y) ⟧) ≡ ⟦ x ⟧ ∨ ⟦ y ⟧
false ⟦∨′⟧ y = refl
true ⟦∨′⟧ y = refl
```
Exercise 1.5. Likewise for exclusive-or.
```agda
infixr 6 _⊕_ _⟦⊕⟧_
_⊕_  : Bool → Bool → Bool
false ⊕ x = not x
true ⊕ x =   x

_⟦⊕⟧_ : ∀ x y → ⟦ x ⊕ y ⟧ ≡ ⟦ x ⟧ xor ⟦ y ⟧
false ⟦⊕⟧ y = refl
true ⟦⊕⟧ y = refl
```
Next, let’s consider some equational properties we would want our inverted boolean
representation to satisfy. Since we’re using negative booleans to represent positive
booleans, it had better be the case that properties of the former transport to properties
of the latter. Any failure of this expectation is an abstraction leak, i.e., an observable
inconsistency between model and implementation.
Exercise 1.6. Prove that not ′ is its own inverse, i.e.,
```agda
not′-involutive : ∀ x → not′ (not′ x) ≡ x
not′-involutive true = refl
not′-involutive false = refl
```
Exercise 1.7. Prove that _∧ ′ _ is associative, commutative, and idempotent, as well
as other laws of a boolean algebra

I don't know the laws of boolean algebra, so I looked them up at
[Laws of Boolean Algebra and Boolean Algebra Rules](https://www.electronics-tutorials.ws/boolean/bool_6.html).

```agda
∧-assoc : ∀ (x y z : Bool) → (x ∧′ y) ∧′ z ≡ x ∧′ (y ∧′ z)
∧-assoc false false false = refl
∧-assoc false false true = refl
∧-assoc false true false = refl
∧-assoc false true true = refl
∧-assoc true false false = refl
∧-assoc true false true = refl
∧-assoc true true false = refl
∧-assoc true true true = refl

∧-comm :  ∀ x y → (x ∧′ y) ≡ (y ∧′ x)
∧-comm false false = refl
∧-comm false true = refl
∧-comm true false = refl
∧-comm true true = refl

∧-idem : ∀ x y → x ∧′ y ≡ (x ∧′ y) ∧′ y
∧-idem false false = refl
∧-idem false true = refl
∧-idem true false = refl
∧-idem true true = refl


∧0 : ∀ x → x ∧′ ⟦ false ⟧ ≡ ⟦ false ⟧
∧0 true = refl
∧0 false = refl

∨1 : ∀ x → x ∨′ ⟦ true ⟧ ≡ ⟦ true ⟧
∨1 true = refl
∨1 false = refl


∨0 : ∀ x → x ∨′ ⟦ false ⟧ ≡ x
∨0 true = refl
∨0 false = refl

∨same : ∀ x → x ∨′ x ≡ x
∨same true = refl
∨same false = refl


∧same :  ∀ x → x ∧′ x ≡ x
∧same true = refl
∧same false = refl

∧not : ∀ x → x ∧′ not′ x ≡ ⟦ false ⟧
∧not true = refl
∧not false = refl
∨not : ∀ x → x ∨′ not′ x ≡ ⟦ true ⟧
∨not true = refl
∨not false = refl


∨-comm : ∀ x y → x ∨′ y ≡ y ∨′ x
∨-comm false false = refl
∨-comm false true = refl
∨-comm true false = refl
∨-comm true true = refl

demorgan∨ : ∀ x y → not′ (x ∨′ y) ≡ not′ x ∧′ not′ y
demorgan∨ false false = refl
demorgan∨ false true = refl
demorgan∨ true false = refl
demorgan∨ true true = refl

demorgan∧ : ∀ x y → not′ (x ∧′ y) ≡ not′ x ∨′ not′ y
demorgan∧ false false = refl
demorgan∧ false true = refl
demorgan∧ true false = refl
demorgan∧ true true = refl
```
