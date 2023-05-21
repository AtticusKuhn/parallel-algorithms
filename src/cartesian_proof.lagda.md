


⇉ represents a tracked computation, i.e. a computation where the number of steps needed to execute the computation is tracked by a nat representing the number of steps.

# Imports
```agda
open import cartesian
open import monoid

open import Data.Nat.Base
open import Felix.Object hiding (_⊎_ ; _×_)

open import Data.Product -- hiding (_×_)
open import Felix.Raw  hiding (_⊎_ ; _×_)

open import Data.Product -- for tuples
open import Agda.Builtin.Sigma

open import Data.Sum.Base
open import Felix.Instances.Function.Raw
open →-raw-instances
open →-instances

```

# Instances
The idea is that we create custom categorical instances for our ⇉ operation to capture its custom semantics.
The semantics are that ⇉ represents a function which returns a pair of the result and a natural number representing the number of steps it took to
compute that result.
```agda
instance
  ps : Products Set
  ps = products Agda.Primitive.lzero
  pc : Coproducts Set
  pc = coproducts Agda.Primitive.lzero
 -- cat : Category (λ A B → A → B)
 -- cat = category Agda.Primitive.lzero
  --catcar : Cartesian (λ A B → A → B)
 -- catcar = cartesian Agda.Primitive.lzero
--  catcarco : Cocartesian (λ A B → A → B)
--  catcarco = cocartesian Agda.Primitive.lzero


_⇉_ : Set → Set → Set
a ⇉ b =  a × ℕ  → b × ℕ

variable
  A B C D : Set
comp : (B ⇉ C) → (A ⇉ B) → ( A ⇉ C)
comp f g ( a , n )= f ( g ( a , n ) )

triangle : (A ⇉ C) → (A ⇉ D) → (A ⇉ (C × D))
triangle f g  a =   ( ( fst (f a) , fst (g a)  )  , (snd (f a)) ⊔ snd (g a) )

myexl : (A × B) ⇉ A
myexl ( ( a , b ) , n) = (a , n)
myexr : (A × B) ⇉ B
myexr ( ( a , b ) , n) = (b , n)

flippedTriangle : (A ⇉ C) → (B ⇉ C) → ((A ⊎ B) ⇉ C)
flippedTriangle f g ((inj₁ a) , n) = f (a , n)
flippedTriangle f g ((inj₂ b) , n) = g ( b , n)
instance
  trackedCategory : Category _⇉_
  trackedCategory = record {
    id = λ a → a
    ; _∘_ = comp
    }

  trackedCartesian : Cartesian _⇉_
  trackedCartesian  = record {
    _▵_ = triangle
    ; exl = myexl
    ; exr = myexr
    ; ! = λ (a , n) → ( tt , n )
    }

  trackedCocartesian : Cocartesian _⇉_
  trackedCocartesian = record {
    _▿_ = flippedTriangle
    ; inl = λ (a , n) → (inj₁ a , n)
    ; inr = λ (b , n) → (inj₂ b , n)
    ; ¡ = λ ()
    }


instance
  monoidNat : monoid.monoidCategory {_⇨_ = _⇉_} {{bruhcat = trackedCategory}} {{brucat = trackedCartesian}} ℕ
  monoidNat = record
    { madd = λ ((a , b) , n) → (a + b , suc n)
    ; mzero = λ (t , n) →  ( 0 , n )}

```
# Proof
```agda

--testTree : boundedTree ℕ 2 ℕ
--testTree = (( 1 , 2 ) , ( 3 , 4 ))

--testTrackedReduce : ℕ × ℕ
--testTrackedReduce = reduceBoundedTree ℕ {{z = monoidNat}} 2 (testTree , 0)

open import Agda.Builtin.Equality
testMax : 4 ⊔ 5 ≡ 5
testMax = refl

open import Relation.Binary.PropositionalEquality
maxIdempotent : (n : ℕ) → n ⊔ n ≡ n
maxIdempotent zero  = refl
maxIdempotent (suc b) = cong suc (maxIdempotent b)

open ≡-Reasoning
trackedTheorem : (size :  ℕ) → (tree : boundedTree ℕ size ℕ ) → snd (reduceBoundedTree ℕ size ( tree , 0 )) ≡ size
trackedTheorem zero a = refl
trackedTheorem (suc n) (a , b)  =
  begin
    snd (reduceBoundedTree ℕ (suc n) ((a , b) , 0))
    ≡⟨⟩
    suc ((snd (reduceBoundedTree ℕ n (a  , 0))) ⊔ (snd (reduceBoundedTree ℕ n (b  , 0))))
    ≡⟨ cong (λ x → suc (x ⊔ (snd (reduceBoundedTree ℕ n (b , 0))))) (trackedTheorem n a) ⟩
    suc (n ⊔ (snd (reduceBoundedTree ℕ n ( b , 0 ))))
    ≡⟨ cong (λ x → suc (n ⊔ x)) (trackedTheorem n b) ⟩
    suc (n ⊔ n)
    ≡⟨ cong suc (maxIdempotent n) ⟩
    suc n
  ∎


```
