{-# OPTIONS --safe --cubical-compatible #-}
module Function.Partial where

open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

private variable
  x y r r' z : Level


Fun₂ : (X : Set x) (Y : Set y) → (X → Y → Set r) → (Z : Set z) → Set (x ⊔ y ⊔ r ⊔ z)
Fun₂ X Y R Z = (x : X) (y : Y) → R x y → Z

Op₂ : {X : Set x} → (X → X → Set r) → Set (x ⊔ r)
Op₂ {X = X} R = Fun₂ X X R X

Preserves₂ : ∀ {X : Set x} {Y : Set y} {R : X → X → Set r} {R' : Y → Y → Set r'}
          → (f : X → Y) (f-mono : Monotonic₁ R R' f)
          → (g : Op₂ R) (g' : Op₂ R')
          → Set (x ⊔ y ⊔ r)
Preserves₂ {X = X} {Y = Y} {R = R} {R' = R'} f f-mono g g'
  = ∀ {x y} (r : R x y) → f (g x y r) ≡ g' (f x) (f y) (f-mono r)
