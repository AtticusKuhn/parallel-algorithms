test the cost of categories
```
open import costCat2
open import monoid -- hiding (a ; b ; c)
open monoidCategory
open import Felix.Raw
module testcostcat where
open import Felix.Instances.Function.Raw
open Felix.Instances.Function.Raw.→-instances
open →-raw-instances
open import Agda.Builtin.Sigma using (fst ; snd ; _,_)
open import Data.Nat.Base
open import Data.Nat.Properties using (+-comm ; +-assoc)
instance
  ps2 : Products Set
  ps2 = products Agda.Primitive.lzero
  cat : Category (λ A B → A → B)
  cat = category Agda.Primitive.lzero
  catcar : Cartesian (λ A B → A → B)
  catcar = cartesian Agda.Primitive.lzero




instance
  orderedℕ : totallyOrderedCategory ℕ ℕ
  orderedℕ = record {
    max  = λ A → (fst A)  ⊔  (snd A)
    ; inc = λ A → A + 1
    ; monoidZero = λ A → 0
    }

  monoidℕ : monoidCategory ℕ
  monoidℕ = record {
    madd = λ A → (fst A) + (snd A)
    ; mzero = λ A → 0
    }

  monoidMax : monoidCategory ℕ
  monoidMax = record {
    madd = λ A → (fst A) ⊔ (snd A)
    ; mzero = λ A → 0
    }

  functorℕ : monoidCategory (ℕ × ℕ)
  functorℕ = functor ℕ monoidℕ

  maxSecond : monoidCategory (ℕ × ℕ)
  maxSecond = record {
    madd = λ A → (0 , (snd (fst A)) ⊔ (snd (snd (A))))
    ; mzero = λ A → (0 , 0)
    }

tree : ℕ → Set →  Set
tree zero a = a
tree (suc n) a = (tree n a) × (tree n a)

reduce : {A : Set} {{mon : monoidCategory A}} (n : ℕ) → (tree n A) → A
reduce zero  = id
reduce {{mon}} (suc n) = madd mon ∘ twice (reduce n)



open import Relation.Binary.PropositionalEquality
test2 : reduce {ℕ × ℕ} 1 ( (1 , 2) , (2 , 4) ) ≡  ( 3 , 5 )
test2 = refl


test : reduce 2 (( (1 , 2) , (2 , 4) ) , ( (3 , 6) , ( 4 , 8 ))) ≡  ( 10 , 10 )
test = refl

maxIdempotent : (n : ℕ) → n ⊔ n ≡ n
maxIdempotent zero  = refl
maxIdempotent (suc b) = cong suc (maxIdempotent b)


maxOut : (n a b : ℕ) → ((n + a) ⊔ (n + b)) ≡ (n + (a ⊔ b))
maxOut 0 a b = refl
maxOut (suc n) a b = cong suc (maxOut n a b)


open ≡-Reasoning
proof : (n : ℕ) (t : tree n (ℕ × ℕ)) → snd  (reduce {ℕ × ℕ} {{functorℕ}} n t) ≡ n + snd (reduce {ℕ × ℕ} {{maxSecond}} n t)
proof 0 x = refl
proof (suc n) (a , b) rewrite (proof n a) | (proof n b) | (+-comm (n + snd (reduce {ℕ × ℕ} {{functorℕ}} n b)) 1) | (+-assoc n (snd (reduce {ℕ × ℕ} {{functorℕ}} n b)) 1) |  (maxOut n (snd (reduce {ℕ × ℕ} {{functorℕ}} n a)) (snd (reduce {ℕ × ℕ} {{functorℕ}} n b))) = begin
      ( (n + snd (reduce n a)) ⊔ (n + snd (reduce n b))) + 1
        ≡⟨ cong (λ x → x + 1) (maxOut n (snd (reduce n a)) (snd (reduce n b))) ⟩
      (n  + (snd (reduce n a) ⊔ snd (reduce n b))) + 1
        ≡⟨ +-comm (n + (snd (reduce n a) ⊔  snd (reduce n b))) 1 ⟩
      1 + (n + (snd (reduce n a) ⊔ snd (reduce n b)))
      ∎

```
