{-# OPTIONS --safe --without-K #-}

open import Algebra.Structures
open import Function
open import Relation.Binary.PropositionalEquality

module Algebra.Structure.PointedSet where

record PointedSet : Set₁ where
  constructor PSet
  field
    Carrier : Set
    ε : Carrier
open PointedSet

record PointedSetMorphism (A B : PointedSet) : Set where
  constructor PSetMorphism
  private
    module A = PointedSet A
    module B = PointedSet B
  field
    fun : Carrier A → Carrier B
    preserves-ε : fun (A.ε) ≡ B.ε
open PointedSetMorphism

pset-id : ∀ {A} → PointedSetMorphism A A
PointedSetMorphism.fun pset-id = Function.id
PointedSetMorphism.preserves-ε pset-id = refl

pset-comp : ∀ {A B C} → PointedSetMorphism A B → PointedSetMorphism B C → PointedSetMorphism A C
PointedSetMorphism.fun (pset-comp f g) = (fun g) ∘ (fun f)
PointedSetMorphism.preserves-ε (pset-comp f g) = trans (cong (fun g) (preserves-ε f)) (preserves-ε g)
