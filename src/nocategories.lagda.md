NO CATEGORIES


# Imports
Import some required libraries
```agda
-- open import Data.List
open import Data.Vec
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality hiding ([_])

-- open import Agda.Builtin.Sigma
open import Data.Product hiding (zip) -- hiding (_,_)
module nocategories where
```

```agda
variable
 a b c d : Bool
 n m l o p : ℕ

-- record ⟦_⟧≡_ (Bit : Set) : Set where
--   field
--     toD : Bit → ℕ
infix 7 ⟦_⟧≡_
record ⟦_⟧≡_ (x y : Set) : Set where
  field
    conv : x → y
  --   dummy : ⊤


infix 7 ⟦_⟧
⟦_⟧ : {A B : Set} ⦃ h :  ⟦ A ⟧≡ B ⦄ → A →  B
⟦_⟧ ⦃ h ⦄ a = ⟦_⟧≡_.conv h a
-- pattern ⟦_⟧ x = (HasDenotation.⟦_⟧ x)




Bit : Set
Bit = Bool
Bits :  ℕ  → Set
Bits n =  Vec Bool n

-- infix 7 p⟦_⟧

cast :  {x y : Set} → x ≡ y → x → y
cast refl x = x

pattern [_,,_] a b =  a ∷ b ∷ []
variable
  A B : Bits n

bitD : Bool → ℕ
bitD b = if b then 1 else 0
bitsD : Bits n → ℕ
bitsD {0} [] = 0
bitsD {suc n} (head ∷  rest) = ( bitD head ) + 2 * (bitsD rest)
-- infix 7 ⟦_⟧≡_
-- record ⟦_⟧≡_ (x y : Set) : Set where
--   field
--     conv : x → y
--   --   dummy : ⊤

-- infix 7 t⟦_⟧
-- t⟦_⟧ : {x y : Set} ⦃ t : hasT x y ⦄ → x → y
-- t⟦_⟧ ⦃ t ⦄ x = hasT.t⟦_⟧ t x
-- open hasT
-- instance
--   tbit : ⟦ Bit ⟧≡ ℕ
--   tbit = record {
--     conv = λ x → if x then 1 else 0
--  --    dummy = tt
--     }
--   tbits :  ⟦ (Bits n) ⟧≡ ℕ
--   tbits = record {
--     conv = bitsD
--     -- dummy = tt
--     }
--   postulate
--     tfun : {A B C D : Set} → ⦃  ⟦ A ⟧≡ C ⦄ → ⦃  ⟦ B ⟧≡ D ⦄ →  ⟦ (A → B) ⟧≡ (C → D)
-- infix 7 p⟦_⟧
-- p⟦_⟧ : {a b : Set} ⦃ t :  ⟦ a ⟧≡ b ⦄ → a → b
-- p⟦_⟧ ⦃ t ⦄ = ⟦_⟧≡_.conv t
-- postulate
--   -- t⟦_⟧ : Set → Set
--   -- tbit : t⟦ Bit ⟧ ≡ ℕ
--   -- tbits : t⟦ Bits n ⟧ ≡ ℕ
--   -- tfun : {A B : Set } → t⟦  (A → B) ⟧ ≡ (t⟦ A ⟧ → t⟦ B ⟧)
--   -- p⟦_⟧ : {a b : Set}  → ⦃ t : hasT a b ⦄ → a → b
--   -- ptrue : p⟦ true ⟧ ≡  1
--   -- pfalse : p⟦ false ⟧ ≡  0
--   -- pbits : {x : Bit} { xs : Bits n } → p⟦ x ∷ xs ⟧ ≡ p⟦ x ⟧ + 2 * p⟦ xs ⟧
--   -- (∀ x → ⟦ f x ⟧ ≡ g ⟦ x ⟧) →  ⟦ f ⟧ ≡ g
--   -- pfunext : {x y a b : Set} {f : x → y} {g : a → b} → ⦃ tyb : hasT y b ⦄ → ⦃ txa : hasT x a ⦄  →  ( (h : x) → (p⟦_⟧ {y} {b} ⦃ tyb ⦄  (f h)) ≡ g (p⟦_⟧ {x} {a} ⦃ txa ⦄ h  )) → p⟦ f ⟧ ≡ g
--   pfunext : {x y a b : Set} {f : x → y} {g : a → b} → ⦃ yb :  ⟦ y ⟧≡ b ⦄ → ⦃ xa :   ⟦ x ⟧≡ a ⦄  →  ( (h : x) → (p⟦ f h ⟧) ≡ g (p⟦ h ⟧)) → p⟦ f ⟧ ≡ g
--   -- pbits : {x : Bit} {xs : Bits n} → p⟦ x ∷ xs ⟧ ≡ cast (sym tbits) (cast (tbit) p⟦ x ⟧ + 2 *  cast (tbits) p⟦ xs ⟧)
--   pfunext2 : {x y z  px py pz : Set} {f : x → y → z} { pf : px → py → pz } → ⦃ xpx :  ⟦ x ⟧≡ px ⦄ → ⦃ ypy : ⟦ y ⟧≡ py ⦄ → ⦃ zpz :  ⟦ z ⟧≡ pz ⦄ →  ( (p : x) → (q : y) → ( p⟦ f p q ⟧ ) ≡ pf p⟦ p ⟧ p⟦ q ⟧   )  → p⟦ f ⟧ ≡ pf
-- -- pfunext2 {x} {y} {z} {px} {py} {pz} {f} {pf} eq rewrite (pfunext {x} {y → z} {px} {py → pz} {f = f}  eq ) = {!!}

instance
  denotationBool :  ⟦ Bool ⟧≡ ℕ
  denotationBool = record {
    conv = bitD
    }
  denotationBits :  ⟦ Bits n ⟧≡ ℕ
  denotationBits = record {
    conv = bitsD
    }
  postulate
    denotationFunction : {A B C D : Set} → ⦃  ⟦ A ⟧≡ C ⦄ → ⦃  ⟦ B ⟧≡ D ⦄ →  ⟦ (A → B) ⟧≡ (C → D)

postulate
  pfunext : {x y a b : Set} {f : x → y} {g : a → b} → ⦃ yb :  ⟦ y ⟧≡ b ⦄ → ⦃ xa :   ⟦ x ⟧≡ a ⦄  →  ( (h : x) → (⟦ f h ⟧) ≡ g (⟦ h ⟧)) → ⟦ f ⟧ ≡ g
  pfunext2 : {x y z  px py pz : Set} {f : x → y → z} { pf : px → py → pz } → ⦃ xpx :  ⟦ x ⟧≡ px ⦄ → ⦃ ypy : ⟦ y ⟧≡ py ⦄ → ⦃ zpz :  ⟦ z ⟧≡ pz ⦄ →  ( (p : x) → (q : y) → (⟦ f p q ⟧ ) ≡ pf ⟦ p ⟧ ⟦ q ⟧   )  → ⟦ f ⟧ ≡ pf

∀p∧* : (p q : Bit) → ⟦ p ∧ q ⟧ ≡ ⟦ p ⟧ * ⟦ q ⟧
∀p∧* false _ = refl
∀p∧* true c = sym (+-identityʳ ⟦ c ⟧)
p∧* : ⟦ _∧_ ⟧ ≡ _*_
p∧* =  pfunext2 ∀p∧*


-- f : A → B
-- ⟦ f ⟧ = ∀ (a : A) → ⟦ f a ⟧ = f ⟦ a ⟧


example : ⟦  [ true ] ⟧ ≡ 1
example = refl


_+H_ : Bit → Bit → Bits 2
A +H B = [ A xor B ,,  A ∧ B ]


∧* : ⟦ a ∧ b ⟧ ≡ ⟦ a ⟧ * ⟦ b ⟧
∧* {false} {b} = refl
∧* {true} {b} = sym (+-identityʳ ⟦ b ⟧)
-- this is not true
-- todo, prove about _xor_
halfAdderSpec : ⟦ a +H b ⟧ ≡ ⟦ a ⟧ + ⟦ b ⟧
halfAdderSpec {false} {false} = refl
halfAdderSpec {false} {true} = refl
halfAdderSpec {true} {false} = refl
halfAdderSpec {true} {true} = refl


∀+H+ : (a b : Bit) → ⟦ a +H b ⟧ ≡ ⟦ a ⟧ + ⟦ b ⟧
∀+H+ false c = +-identityʳ ⟦ c ⟧
∀+H+ true false = refl
∀+H+ true true = refl

+H+ : ⟦ _+H_ ⟧ ≡ _+_
+H+ = pfunext2 ∀+H+

_+F_+F_ : Bit → Bit → Bit → Bits 2
A +F B +F C =   [ head second ,,  head (tail first) ∨ head (tail second) ]
  where
  -- why can't I pattern match?
    first : Bits 2
    first = A +H B
    second : Bits 2
    second = head first  +H C

fullAdderSpec : ⟦ a +F b +F c ⟧ ≡ ⟦ a ⟧ + ⟦ b ⟧ + ⟦ c ⟧
fullAdderSpec {false} {false} {a} = +-identityʳ ⟦ a ⟧
fullAdderSpec {false} {true} {false} = refl
fullAdderSpec {false} {true} {true} = refl
fullAdderSpec {true} {false} {false} = refl
fullAdderSpec {true} {false} {true} = refl
fullAdderSpec {true} {true} {false} = refl
fullAdderSpec {true} {true} {true} = refl




_+B_+B_ : Bit → Bits n → Bits n → Bits (suc n)
_+B_+B_ {0} c A B = [ c ]
_+B_+B_ {suc n} c0 (a0 ∷ A) (b0 ∷ B) with c0 +F a0 +F b0
...                  |  [ r0 ,, c1 ] = (r0 ∷ (c1 +B A +B B))




_+Ba_ : Bit → Vec (Bit × Bit) n → Bits (suc n)
c +Ba [] = [ c ]
c0 +Ba ((a0 , b0) ∷ A) with c0 +F a0 +F b0
...                  |  [ r0 ,, c1 ] = (r0 ∷ (c1 +Ba A))

alternateSpec : ⟦ c +Ba zip A B ⟧ ≡ ⟦ c ⟧ + ⟦ A ⟧ + ⟦ B ⟧
alternateSpec {c} {0} {[]} {[]} rewrite +-identityʳ ⟦ c  ⟧ = sym (+-identityʳ ⟦ c ⟧)
alternateSpec {c} {suc n} {a ∷ A} {b ∷ B} rewrite +-identityʳ ⟦ c  ⟧ | fullAdderSpec {c} {a} {b}
  | +-identityʳ (⟦ B ⟧)
  | +-identityʳ( ⟦ A ⟧  )
  | +-identityʳ ⟦ c +B A +B B ⟧
  | alternateSpec {((c ∧ a ∨ (c xor a) ∧ b))} {n} {A} {B}
  | +-identityʳ  ((if c ∧ a ∨ (c xor a) ∧ b then 1 else 0) + bitsD A + bitsD B)
  | fullAdderSpec {c} {a} {b}
  -- | aux {⟦ B ⟧} {⟦ A ⟧ } { ⟦ B ⟧  }
  | +-assoc ⟦ A ⟧ ⟦ B ⟧ ( ⟦ A ⟧ + ⟦ B ⟧  )
  | +-assoc ⟦ A ⟧ ⟦ A ⟧ ( ⟦ B ⟧ + ⟦ B ⟧  ) | +-identityʳ (bitsD ((c ∧ a ∨ (c xor a) ∧ b) +B A +B B))
  = {! !}
aux : n + (m + l) ≡ m + (n + l)
aux {n} {m} {l} rewrite sym (+-assoc n m l) | +-comm n m = +-assoc m n l

aux2 : (n) + ((m) + l + o + ((m) + l + o)) ≡ (n + m + m) + (l + l) + (o + o)
aux2 = {! !}


-- lem1 : ⟦ (c xor a) xor b ⟧ + ⟦ c ∧ a ∨  (c xor b)
--
+FLemma : ⟦ (c xor a) xor b ⟧ + ( ⟦ c ∧ a ∨ (c xor a) ∧ b ⟧ + ⟦ c ∧ a ∨ (c xor a) ∧ b ⟧) ≡ ⟦ c ⟧ + ⟦ a ⟧ + ⟦ b ⟧
+FLemma {c} {a} {b} rewrite (sym (fullAdderSpec {c} {a} {b} ))
  | +-identityʳ ⟦ c ∧ a ∨ (c xor a) ∧ b ⟧  | +-identityʳ ⟦ c ∧ a ∨ (c xor a) ∧ b ⟧ = refl

aux3 : n + m + l + o + p ≡ n + (m + o) + (l + p)
aux3 = {!!}
open ≡-Reasoning
-- not done yet
rippleAdderSpec : ⟦ c +B A +B B ⟧ ≡ ⟦ c ⟧ + ⟦ A ⟧ + ⟦ B ⟧
rippleAdderSpec {c} {0} {[]} {[]} rewrite  +-identityʳ ⟦ c ⟧ = sym (+-identityʳ (if c then 1 else 0))
rippleAdderSpec {c} {suc n} {a ∷ A} {b ∷ B} rewrite fullAdderSpec {c} {a} {b}
  | +-identityʳ (⟦ B ⟧)
  | +-identityʳ( ⟦ A ⟧  )
  | +-identityʳ ⟦ c +B A +B B ⟧
  | rippleAdderSpec {((c ∧ a ∨ (c xor a) ∧ b))} {n} {A} {B}
  | +-identityʳ  ((if c ∧ a ∨ (c xor a) ∧ b then 1 else 0) + bitsD A + bitsD B)
  | fullAdderSpec {c} {a} {b}
  | aux {⟦ B ⟧} {⟦ A ⟧ } { ⟦ B ⟧  }
  | +-assoc ⟦ A ⟧ ⟦ B ⟧ ( ⟦ A ⟧ + ⟦ B ⟧  )
  | +-assoc ⟦ A ⟧ ⟦ A ⟧ ( ⟦ B ⟧ + ⟦ B ⟧  ) | +-identityʳ (bitsD ((c ∧ a ∨ (c xor a) ∧ b) +B A +B B))
  | aux2 {⟦ (c xor a) xor b ⟧} {⟦ c ∧ a ∨ (c xor a) ∧ b  ⟧ } {⟦ A ⟧ } {⟦ B ⟧}
  | (fullAdderSpec {c} {a} {b})
  | +FLemma {c} {a} {b}
  | +-assoc ⟦ (c xor a) xor b ⟧   ⟦ c ∧ a ∨ (c xor a) ∧ b ⟧  ⟦ c ∧ a ∨ (c xor a) ∧ b ⟧
  -- | sym ( +-identityʳ ⟦ c ∧ a ∨ (c xor a) ∧ b ⟧)
  | +FLemma {c} {a} {b}
  | +-assoc ⟦ c ⟧ ⟦ a ⟧ (⟦ b ⟧ + (⟦ A ⟧ + ⟦ A ⟧) + (⟦ B ⟧ + ⟦ B ⟧))
  | aux3  {⟦ c ⟧} {⟦ a ⟧} {⟦ b ⟧} {⟦ A ⟧ + ⟦ A ⟧} {⟦ B ⟧ + ⟦ B ⟧} = refl
  -- = begin
  -- ((if (c xor a) xor b then 1 else 0) +
  --   ((if c ∧ a ∨ (c xor a) ∧ b then 1 else 0)
  --   + (if c ∧ a ∨ (c xor a) ∧ b then 1 else 0)))
  --   + (bitsD A + bitsD A)
  --   + (bitsD B + bitsD B)
  --   ≡⟨ cong (λ x → (x + (⟦ A ⟧ + ⟦ A ⟧) + (⟦ B ⟧ + ⟦ B ⟧))) (+FLemma {c} {a} {b}) ⟩
  -- (⟦ c ⟧ + ⟦ a ⟧ + ⟦ b ⟧) + (⟦ A ⟧ + ⟦ A ⟧) + (⟦ B ⟧ + ⟦ B ⟧)
  -- ≡⟨ {! !} ⟩
  --   ⟦ c ⟧ + (⟦ a ⟧ + (⟦ A ⟧ + ⟦ A ⟧  )) + ( ⟦ b ⟧ +  (⟦ B ⟧ + ⟦ B ⟧ ) )
  -- ∎




_*S_ : Bit → Bits n → Bits n
b *S [] = []
b *S (a ∷ A) = (b ∧ a) ∷ (b *S A)


∀*Sspec : (p : Bits n) (q : Bit) → ⟦ q *S p ⟧ ≡ ⟦ p ⟧ * ⟦ q ⟧
∀*Sspec [] q = refl
∀*Sspec (bit ∷ bits ) false rewrite (∀*Sspec bits false) | *-zeroʳ ⟦ bits ⟧ | *-zeroʳ ((if bit then 1 else 0) + (bitsD bits + (bitsD bits + 0)))    = refl
∀*Sspec (bit ∷ bits ) true rewrite (∀*Sspec bits true) | *-identityʳ ⟦ bits ⟧ | *-identityʳ (((if bit then 1 else 0) + (bitsD bits + (bitsD bits + 0))) ) = refl
-- ∀*Sspec  (bit ∷ bits)  q rewrite (∀*Sspec bits q) | (+-identityʳ ⟦ bits ⟧) | (+-identityʳ (⟦ bits ⟧ * ⟦ q ⟧)) | sym (*-distribʳ-+ ⟦ bits ⟧ (⟦ bits ⟧ ) ⟦ q ⟧) =
--   begin
--     (if q ∧ bit then 1 else 0) +  (bitsD bits * (if q then 1 else 0) + bitsD bits * (if q then 1 else 0))
--     ≡⟨ cong (λ x → ⟦ q ∧ bit ⟧ + x) (sym (*-distribʳ-+ ⟦ q ⟧ (⟦ bits ⟧ ) ⟦ bits ⟧)) ⟩
--     ⟦ q ∧ bit ⟧ + ((⟦ bits ⟧ + ⟦ bits ⟧ ) * ⟦ q ⟧ )
--     -- ≡⟨ cong (λ x → ((⟦ bits ⟧ + ⟦ bits ⟧ ) * ⟦ q ⟧ )) ({! !})  ⟩
--     -- ⟦ q ⟧ * ⟦ bit ⟧ + ((⟦ bits ⟧ + ⟦ bits ⟧ ) * ⟦ q ⟧ )
--     ≡⟨ {! !} ⟩
--     ((if bit then 1 else 0) + (bitsD bits + bitsD bits)) * (if q then 1 else 0)
--   ∎

*Sspec : ⟦ (λ (b : Bits n) →  _*S b) ⟧ ≡ _*_
*Sspec = pfunext2 ∀*Sspec

bitMulSpec : ⟦ c *S A ⟧ ≡ ⟦ c ⟧ * ⟦ A ⟧
bitMulSpec {true} {0} {[]} = refl
bitMulSpec {false} {0} {[]} = refl
bitMulSpec {true} {suc n} {true ∷ A} rewrite bitMulSpec {true} {n} {A} | +-identityʳ ⟦ A ⟧ | +-identityʳ ( ⟦ A ⟧ + ⟦ A ⟧ ) | +-identityʳ ⟦ A ⟧  = refl
bitMulSpec {true} {suc n} {false ∷ A} rewrite bitMulSpec {true} {n} {A} | +-identityʳ ⟦ A ⟧ | +-identityʳ ( ⟦ A ⟧ + ⟦ A ⟧ ) | +-identityʳ ⟦ A ⟧  = refl
bitMulSpec {false} {suc n} {true ∷ A} rewrite bitMulSpec {false} {n} {A} | +-identityʳ ⟦ A ⟧ | +-identityʳ ( ⟦ A ⟧ + ⟦ A ⟧ ) | +-identityʳ ⟦ A ⟧  = refl
bitMulSpec {false} {suc n} {false ∷ A} rewrite bitMulSpec {false} {n} {A} | +-identityʳ ⟦ A ⟧ | +-identityʳ ( ⟦ A ⟧ + ⟦ A ⟧ ) | +-identityʳ ⟦ A ⟧  = refl

_<<_ : Bits n → (m : ℕ) → Bits (m + n  )
A << 0 =  A -- subst (λ n → Bits n)  (sym (+-identityʳ n)) A
A << (suc n) = false ∷ A << n


∀<<*2 : (m : ℕ) (b : Bits n) → ⟦ b << m ⟧ ≡ ⟦ b ⟧ * (2 ^ m)
∀<<*2 0 bs =  sym (*-identityʳ ⟦ bs ⟧)
∀<<*2 (suc m) bs rewrite (∀<<*2 m bs) | +-identityʳ (2 ^ m) | +-identityʳ (⟦ bs << m ⟧ +  ⟦ bs << m ⟧) | +-identityʳ ⟦ (bs) << m ⟧ | +-identityʳ ⟦ bs ⟧ | +-identityʳ (⟦ bs ⟧ * 2 ^ m)  = sym (*-distribˡ-+ ⟦ bs ⟧ (2 ^ m) ( 2 ^ m ))

<<*2 :  (m : ℕ) →  ⟦  (λ (b : Bits n) →  b <<  m) ⟧ ≡ _*  (2 ^ m)
<<*2 n = pfunext  (∀<<*2 n )


_*Ba_ : Bits n → Bits m → Bits (n + m)
_*Ba_ {m = m} [] B =  subst (λ a → Bits a) (  (+-identityʳ m) ) ([] << (m))
_*Ba_ {n = suc n} (a ∷ A) B = false +B (( a *S B ) << n)  +B (A *Ba B)

_*Ba'_ : Bits n → Bits m → Bits (n + m)
A *Ba' B = (reverse A) *Ba B


-- 10 * 10 =

-- not done yet
mulSpec : ⟦ A *Ba' B ⟧ ≡ ⟦ A ⟧ * ⟦ B ⟧
mulSpec = {! !}


example* : ⟦ ( false ∷ false ∷ true ∷ false ∷ []) *Ba' (false ∷ true ∷ false ∷ false ∷  false ∷  []) ⟧ ≡ 8
example* = refl

```
