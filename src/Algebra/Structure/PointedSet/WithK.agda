{-# OPTIONS --with-K --safe #-}

open import Algebra.Structure.PointedSet
open import Relation.Binary.PropositionalEquality hiding (Extensionality)

module Algebra.Structure.PointedSet.WithK  where
  open PointedSetMorphism

  eqPsetMorphism : ∀ {A B} → {f g : PointedSetMorphism A B} → fun f ≡ fun g → f ≡ g
  eqPsetMorphism {A} {B} {PSetMorphism .f refl} {PSetMorphism f refl} refl = refl
