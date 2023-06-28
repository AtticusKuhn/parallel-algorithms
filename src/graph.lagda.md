


```agda
open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.List
open import Data.String
open import Felix.Object hiding (⊤ ; _×_)
open import Felix.Raw hiding (⊤ ; _×_)
open import Category.Monad
open RawMonad
Port : Set
Port = ℕ

data Ports : Set →  Set₁ where
  UnitP : Ports ⊤
  BoolP : Port → Ports Bool
  NatP : Port → Ports ℕ
  PairP : {A B : Set} → Ports A → Ports B → Ports (A × B)

-- data Comp  : Set → Set₁ → Set₁  Set₁ where
--  mkComp : {a b : Set} → Comp String (Ports a) (Ports b)
data Comp : Set₁ where
  mkComp : {A B : Set} → String → (Ports A) → (Ports B) → Comp

-- State : Set₁ → Set₁ → Set₁
-- State A B = A → (A × B)

data _→S_ : Set₁ → Set₁ → Set₁ where
  State : {A B : Set₁} → (A → A × B) → (A →S B)

GraphM : Set₁ →  Set₁
GraphM  A =  (Port × (List Comp)) →S A

data _→G_ : Set → Set → Set₁ where
  Graph : {A B : Set} → (Ports A → GraphM (Ports B)) → A →G B


graphid : {A : Set} →  A →G A
graphid = Graph ( λ portsA → (State (λ (port , listcomp) → (( port , listcomp  ) , portsA ) )  ))


graph∘ : {A B C : Set} → (B →G C) → (A →G B) → (A →G C)
graph∘ (Graph bc) (Graph ab) = Graph (λ portsA  → State λ (port , listcomp ) → ((port , listcomp) , (ab portsA) ) )
  where
    State f = ab portsA
    ((port2 , listcomp2), portsB) = f portsA
    State g = {! !}



-- graph∘ : {A B C : Set} → (Ports A → Port → (Port × List Comp) → (Port × List Comp ) × Port B) →r

instance
  monad : RawMonad GraphM

  CatGraph : Category _→G_
  CatGraph = record {
    id =  graphid --Graph return
    -- ; _∘_ = graph∘
    }

```
