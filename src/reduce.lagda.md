# Parallel Algorithms

I am going to define a parallel sum over a tree and hopefully prove some properties about it




First, let us define a tree
```agda
data Tree (a : Set) :  Set where
  Leaf : a -> Tree a
  Branch : Tree a -> Tree a -> Tree a


open import Data.Nat.Base
height : {b : Set} → (Tree b) → ℕ
height (Leaf x) = 0
height (Branch t t₁) =  (( height t) ⊔ (height t₁)) + 1

testTree : Tree ℕ
testTree = Branch (Branch (Leaf 1) (Leaf 2)) (Branch (Leaf 3) (Leaf 4))

testTree2 : Tree ℕ
testTree2 =
  Branch (
    Branch (
    Branch (Leaf 1) (Leaf 2))
    (Branch (Leaf 3) (Leaf 4))
  )
    (Branch (
    Branch (Leaf 1) (Leaf 2))
    (Branch (Leaf 3) (Leaf 4)))

```

My idea is to use the idea of arrows to separate the denonational semantics from the operational semantics.

Arrows represent a computation, and we can give the arrow multiple interpretations later. I define two interpretations of
arrow here.

The first one just executes the arrow, and the second one returns a pair of the result and how many steps it took
to execute the algorithm. We can use this step count to measure the efficiency of the algorithm.

The second interpretation measures how much "work" was done in the computation.

```agda
open import Data.Product -- for tuples
open import Agda.Builtin.Sigma

record Arrow (A : Set → Set → Set) : Set₁ where
  field
    arr    : ∀ {B C} → (B → C) → A B C
    _>>>_  : ∀ {B C D} → A B C → A C D → A B D
    first  : ∀ {B C D} → A B C → A (B × D) (C × D)
    second : ∀ {B C D} → A B C → A (D × B) (D × C)
    _***_  : ∀ {B C B' C'} → A B C → A B' C' → A (B × B') (C × C')
    _&&&_  : ∀ {B C C'} → A B C → A B C' → A B (C × C')


open import Data.Sum.Base
-- arrow choice allows us to choose between different computations
record ArrowChoice ( A : Set → Set → Set ) : Set₁ where
  field
    left : ∀{b c d : Set} → A b c → A (b ⊎ d) (c ⊎ d)
    right : ∀ {b c d : Set} → A b c  → A ( d ⊎ b ) ( d ⊎ c )
    _+++_ : ∀{ b c b′ c′ : Set } → A b c → A b′ c′ → A (b ⊎ b′ ) (c ⊎ c′)
    _|||_ : ∀{b c d : Set} → A b d → A c d → A (b ⊎ c) d

open import Function.Base


variable
  b c d : Set
  c′ b′ : Set

-- this code is very ugly, but at least I only have to write it once (hopefully)
choiceLeft : {b c d : Set} → ( (b × ℕ) → (c × ℕ)) → ( (b ⊎ d) × ℕ) → ( (c ⊎ d) × ℕ)
choiceLeft f (inj₁ x , n) = ( inj₁ (proj₁ (f (x , n))),  snd ( f ( x , n ) ) )
choiceLeft f (inj₂ y , n) = ( inj₂ y , n)

choiceRight : (b × ℕ → c × ℕ) → ((d ⊎ b) × ℕ) → ((d ⊎ c) × ℕ)
choiceRight f (inj₁ x , n) = inj₁ x , (n)
choiceRight f (inj₂ y , n) = inj₂ (proj₁ (f (y , n))) , snd (f ( y , n ))

choicePlus : (b × ℕ → c × ℕ) → (b′ × ℕ → c′ × ℕ ) → ((b ⊎ b′) × ℕ) → (c ⊎ c′) × ℕ
choicePlus f g (inj₁ x , n) = inj₁ (proj₁ (f (x , n))) , snd ( f ( x , n ) )
choicePlus f g (inj₂ y , n) = inj₂ (proj₁ (g (y , n))) , snd ( g ( y , n ) )

choiceOr : (b × ℕ → d × ℕ) → (c × ℕ → d × ℕ) → ((b ⊎ c) × ℕ) → d × ℕ
choiceOr f g (inj₁ x , n) = proj₁ (f (x , n)) , snd (f ( x , n ))
choiceOr f g (inj₂ y , n) = proj₁ (g (y , n)) , snd ( g ( y , n ) )


instance
  fnRawArrow : Arrow (λ A B → (A → B))
  fnRawArrow = record
    { arr    = λ f → f
    ; _>>>_  = λ g f x → f (g x)
    ; first  = λ { f (x , y) → (f x , y) }
    ; second = λ { f (x , y) → (x , f y) }
    ; _***_  = λ { f g (x , y) → (f x , g y) }
    ; _&&&_  = λ f g x → (f x , g x)
    }
  fnArrowChoice : ArrowChoice ( λ A B → (A → B) )
  fnArrowChoice = record
    { left = λ f → [ inj₁ ∘ f , inj₂ ∘ id ]
    ; right = λ f → [ inj₁ ∘ id , inj₂ ∘ f ]
    ; _+++_ = λ f g → [ inj₁ ∘ f , inj₂ ∘ g ]
    ; _|||_ = λ f g → [  f , g ]
    }
  fnCountArrow : Arrow (λ A B → ( ( A × ℕ )  →  (B × ℕ )  ))
  fnCountArrow = record
    { arr    = λ f (a , n) → (f a , n + 1)
    ; _>>>_  = λ g f x → f (g x)
    ; first  = λ { f ((x , y), n) →  ( ( ( fst (f (x , n )) , y) ) , snd (f ( x , n )) )   }
    ; second = λ { f ((x , y), n) → ( (x , fst (f (y , n))), snd (f ( y , n )) ) }
    ; _***_  = λ { f g ((x , y), n) →  ( ( fst (f (x , n)) , fst (g (  y , n ) ))  , (snd (f ( x , n ))) ⊔ (snd ( g ( y , n ) )))}
    ; _&&&_  = λ f g ( x , n) →  ( ( fst (f ( x , n )), fst ( g ( x , n ) ) ) , (snd ( f ( x , n ) ) ) ⊔ ( snd ( g ( x , n ) ))  )
    }
  fnCountArrowChoice : ArrowChoice (λ A B → ( ( A × ℕ )  →  (B × ℕ )  ))
  fnCountArrowChoice = record
    { left = choiceLeft
    ; right = choiceRight
    ; _+++_ = choicePlus
    ; _|||_ = choiceOr
    }

```



Now we will actually define the parallel sum algorithm. Unfortunately, Agda can't figure out that it's terminating, but at least it works.
The benefit of using arrows is that it frees the definition of the computation from its executution, so we are free to give the same algorithm
many different interpretations.
```agda
open import Data.Nat.Base
open Arrow {{ ... }} public
open ArrowChoice {{ ... }} public

open import Data.Product -- for tuples
variable
  A : Set → Set → Set
  B : Set
  --instance
  --  Arr : Arrow A
 --   ArrC : ArrowChoice A

variable
  Arr : Arrow A
  ArrC : ArrowChoice A


sumPair :  ( ℕ × ℕ  ) → ℕ
sumPair  (x , y) = x + y

comb :  {{Arrow A}} → A ( ℕ × ℕ ) ℕ
comb   = arr sumPair

treeCase : Tree B  → B ⊎ (Tree B × Tree B)
treeCase (Leaf a) = inj₁ a
treeCase (Branch x y) = inj₂ (x , y)


parallelSum :  {{Arr : Arrow A}} → {{ArrC : ArrowChoice A}} → A (Tree ℕ) ℕ
parallelSum  = (arr treeCase)
  >>>  (arr  (λ x → x) |||  ( (  parallelSum *** parallelSum) >>>  comb ))


testSum : ℕ
testSum = parallelSum testTree

testTrace : ℕ × ℕ
testTrace = parallelSum {{Arr = fnCountArrow }} {{ArrC = fnCountArrowChoice}} (testTree , 0)

open import Agda.Builtin.Equality
-- testSumWorks : testSum ≡ 10
-- testSumWorks = refl

```
Let's define a function which takes an algorithm and a value and returns how many steps the algorithm took on that value
```agda


runTime : {A B : Set} → (A × ℕ → B × ℕ) → A → ℕ
runTime f a = snd ( f ( a , 0 )  )
```

Now let's define some theorems about the parallel sum algorithm. First, I will prove that the time the algorithm takes
to execute is equal to twice the height of the tree plus two.

This is because we parallelize each branch of the tree
```agda

parallelTime : (t : Tree ℕ) → runTime parallelSum t ≡ 2 *  height t + 2
parallelTime (Leaf x) = {!refl!}
parallelTime (Branch t t₁) = {!!}

```

We can also use this same technique on lists. You will see that summing a list is slower than summing a tree
because a list is sequential

```agda
open import Data.List
open import Agda.Builtin.Unit

listCase : List B → (⊤ ⊎ (B × List B))
listCase [] = inj₁ tt
listCase (x ∷ xs) = inj₂ ( x , xs )
sumList : {{Arrow A}} → {{ArrowChoice A}} → A (List ℕ) ℕ
sumList = (arr listCase) >>> ( (arr (λ x → 0) ) ||| ( (second sumList) >>> comb)  )

testList : List ℕ
testList = 1  ∷ 2 ∷ 3 ∷ []

testSumList : ℕ
testSumList = sumList testList

testSumListPerformance : ℕ × ℕ
testSumListPerformance = sumList (testList ,  0)
```
