# Cost

Here I will try to define a cost function


```agda
-- evidence that cost is a cost function
data isCostFunction (cost : (A ⇨ B) → A → ℝ) where
  costId : {x} → cost id x ≡ 0
  costTriangle : (f : B ⇨ C) → (g : A ⇨ B) → (x : A) → cost (f ∘ g) x ≤ cost f (g x) + cost g x
```
