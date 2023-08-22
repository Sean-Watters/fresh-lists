{-# OPTIONS --safe --cubical-compatible #-}

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Free.ReflexivePartialMonoid.Adjunction
  (A : Set)
  (A-set : Irrelevant (_≡_ {A = A}))
  where
