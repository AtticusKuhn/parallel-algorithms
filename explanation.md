


A conparison of `Cost` with some other Functors.


| Name | Input | Output | Requirement |
| -----|-------|--------|-------------|
| D    | A ⇨ B | A ⇨ (B × A ⊸ B)| _⊸_ must be linear|
| StackFun| A ⇨ B | A × Z ⇨ B × Z | Z must be unchanged|
| Cost | A ⇨ B | A × Z ⇨ B × Z | Z must be monotonically increasing |




in haskell


```haskell
newtype Cost a b = C (∀ Z. A × Z → B × Z)

```
This must be a cartesian functor

```haskell
Cost g ∘ Cost f

```



Writing this in Agda

```agda
-- trivial cost
lift : (A ⇨ B) → (A × Z ⇨ B × Z)
lift f = first f

```
