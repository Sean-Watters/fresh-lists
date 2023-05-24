{-# OPTIONS --safe --without-K #-}

open import Algebra.Structure.OICM
open import Data.Empty
open import Data.FreshList.InductiveInductive
open import Function
open import Relation.Binary.Isomorphism
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module Data.FreshList.FreeCommMonoid.Properties
  {X : Set} {_≈_ : X → X → Set} {_≤_ : X → X → Set}
  (≤-PDTO : IsPropDecTotalOrder _≈_ _≤_)
  (≈-prop : {x y : X} → Irrelevant (x ≈ y))
  -- our notion of equation must be propositional for the proof of extensionality to work
  where

open import Data.FreshList.FreeCommMonoid ≤-PDTO
open _≃_

private
  ≤-prop = IsPropDecTotalOrder.≤-prop ≤-PDTO
  _≟_ = IsPropDecTotalOrder._≟_ ≤-PDTO
  total = IsPropDecTotalOrder.total ≤-PDTO
  ≤-refl = IsPropDecTotalOrder.refl ≤-PDTO
  ≤-trans = IsPropDecTotalOrder.trans ≤-PDTO
  ≤-antisym = IsPropDecTotalOrder.antisym ≤-PDTO
  ≤-resp-≈ = IsPropDecTotalOrder.≤-resp-≈ ≤-PDTO
  ≈-isEq = IsPropDecTotalOrder.isEquivalence ≤-PDTO

open Data.FreshList.InductiveInductive.WithIrr _≤_ ≤-prop
open Data.FreshList.InductiveInductive.WithEq _≤_ ≈-isEq ≤-resp-≈


peel-∈-iso-fun' : {b : X} {xs ys : SortedList} {b#xs : b # xs} {b#ys : b # ys}
               → (iso : ∀ a → (a ∈ cons b xs b#xs) ≃ (a ∈ cons b ys b#ys))
               → (a : X)
               → (p : a ∈ xs)
               → (to-there : a ∈ cons b ys b#ys)
               → to-there ≡ to (iso a) (there p)
               → a ∈ ys
peel-∈-iso-fun' {b} iso a p (here a≈b) eq with to (iso a) (here a≈b) in eq'
... | here a≈b' = ⊥-elim (here≢there ( sym $ to-inj (iso a) (trans (sym eq) (trans (cong here (≈-prop a≈b a≈b') ) (sym eq')))))
... | there u = u
peel-∈-iso-fun' {b} iso a p (there a∈ys) eq = a∈ys

peel-∈-iso-fun : {b : X} {xs ys : SortedList} {b#xs : b # xs} {b#ys : b # ys}
               → (∀ a → (a ∈ cons b xs b#xs) ≃ (a ∈ cons b ys b#ys))
               → (∀ a → a ∈ xs → a ∈ ys)
peel-∈-iso-fun iso a p = peel-∈-iso-fun' iso a p (to (iso a) (there p)) refl

