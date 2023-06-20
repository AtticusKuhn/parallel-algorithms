


```agda
open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.List
open import Data.String
open import Felix.Object hiding (⊤ ; _×_)
open import Felix.Raw hiding (⊤ ; _×_)
Port : Set
Port = ℕ

data Ports : Set →  Set₁ where
  UnitP : Ports ⊤
  BoolP : Port → Ports Bool
  NatP : Port → Ports ℕ
  PairP : {A B : Set} → Ports A → Ports B → Ports (A × B)

-- data Comp  : Set → Set₁ → Set₁  Set₁ where
--  mkComp : {a b : Set} → Comp String (Ports a) (Ports b)
Comp : Set₁
Comp = {A B : Set} → String × (Ports A) × (Ports B)

State : Set₁ → Set₁ → Set₁
State A B = A → (A × B)

GraphM : Set₁ →  Set₁
GraphM  A = Port → State (Port × (List Comp)) A

_→G_ : Set → Set → Set₁
A →G B = Ports A → GraphM (Ports B)


graphid : {A : Set} →  Ports A → Port → (Port × List Comp) →  ((Port × List Comp) × (Ports A))
graphid portsA port (port1 , listcomp) = ((port , listcomp) ,  portsA)

instance
  CatGraph : Category _→G_
  CatGraph = record {
    id = graphid
    }

```
