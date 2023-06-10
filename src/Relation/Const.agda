{-# OPTIONS --without-K --safe #-}
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

module Relation.Const where


R⊤ : {A B : Set} → (a : A) (b : B) → Set
R⊤ _ _ = ⊤

R⊥ : {A B : Set} → (a : A) (b : B) → Set
R⊥ _ _ = ⊥

R⊤-irr : ∀ {A} {x y : A} → Irrelevant (R⊤ x y)
R⊤-irr tt tt = refl

R⊥-irr : ∀ {A} {x y : A} → Irrelevant (R⊥ x y)
R⊥-irr ()
