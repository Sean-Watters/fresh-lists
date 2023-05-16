{-# OPTIONS --safe --without-K #-}

open import Algebra.Structures
open import Function
open import Relation.Binary.PropositionalEquality

module Algebra.Structure.Monoid where

record Monoid : Set₁ where
  constructor Mon
  field
    Carrier : Set
    _∙_ : Carrier → Carrier → Carrier
    ε : Carrier
    proof : IsMonoid _≡_ _∙_ ε
open Monoid

record MonoidMorphism (A B : Monoid) : Set where
  constructor MonMorphism
  private
    module A = Monoid A
    module B = Monoid B
  field
    fun : Carrier A → Carrier B
    preserves-ε : fun (A.ε) ≡ B.ε
    preserves-∙ : ∀ x y → fun (x A.∙ y) ≡ (fun x) B.∙ (fun y)
open MonoidMorphism

mon-id : ∀ {A} → MonoidMorphism A A
fun mon-id = Function.id
preserves-ε mon-id = refl
preserves-∙ mon-id _ _ = refl

mon-comp : ∀ {A B C} → MonoidMorphism A B → MonoidMorphism B C → MonoidMorphism A C
fun (mon-comp f g) = (fun g) ∘ (fun f)
preserves-ε (mon-comp f g) = trans (cong (fun g) (preserves-ε f)) (preserves-ε g)
preserves-∙ (mon-comp f g) _ _ = trans (cong (fun g) (preserves-∙ f _ _)) (preserves-∙ g _ _)

