{-# OPTIONS --safe --without-K #-}

open import Level
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

module Index where

open import Data.FreshList.InductiveInductive

Definition-1 = List#

Proposition-2 : {n m : Level} {X : Set n}
              → (R : X → X → Set m) → (R-irr : ∀ {x y} → Irrelevant (R x y))
              → {x : X} {xs : List# R} → Irrelevant (x # xs)
Proposition-2 = WithIrr.#-irrelevant

Corollary-3 : {n m : Level} {X : Set n}
            → (R : X → X → Set m) → (R-irr : ∀ {x y} → Irrelevant (R x y))
            → {x y : X} {xs ys : List# R} {x#xs : x # xs} {y#ys : y # ys}
            → x ≡ y → xs ≡ ys
            → cons x xs x#xs ≡ cons y ys y#ys
Corollary-3 = WithIrr.cons-cong
