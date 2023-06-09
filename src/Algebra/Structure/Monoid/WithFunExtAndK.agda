{-# OPTIONS --with-K --safe #-}

open import Axiom.Extensionality.Propositional
open import Axiom.UniquenessOfIdentityProofs.WithK

open import Algebra.Structure.Monoid
open import Relation.Binary.PropositionalEquality

module Algebra.Structure.Monoid.WithFunExtAndK (funext : Extensionality _ _) where
  open MonoidMorphism

  eqMonMorphism : ∀ {A B} → {f g : MonoidMorphism A B} → fun f ≡ fun g → f ≡ g
  eqMonMorphism {A} {B} {MonMorphism .f refl p∙} {MonMorphism f refl q∙} refl
    = cong (MonMorphism f refl) (funext λ x → funext (λ y → uip (p∙ x y) (q∙ x y)))
