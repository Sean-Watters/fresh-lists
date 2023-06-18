{-# OPTIONS --safe --without-K #-}

open import Level
open import Relation.Nullary
open import Relation.Binary hiding (Irrelevant)
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

Lemma-4 : {n m : Level} {X : Set n} {R : X → X → Set m}
        → Transitive R → (a x : X) (xs : List# R) → R a x → x # xs → a # xs
Lemma-4 = #-trans

Definition-5 = Any

Definition-6 : {n m : Level} {X : Set n} (R : X → X → Set m)
             → {_≈_ : X → X → Set m} (≈-isEq : IsEquivalence _≈_) (R-resp-≈ : R Respects₂ _≈_)
             → X → List# R → Set (n ⊔ m)
Definition-6 = WithEq._∈_
