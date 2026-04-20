
module Data.FreshList.Multiplication where

open import Algebra.Definitions
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality

open import Data.FreshList.InductiveInductive

private variable
  X : Set
  R : X → X → Set

-- Right-regular append. ie, _++_ except it drops non-fresh things on the left
mutual
  appendʳ : Decidable₂ R → List# R → List# R → List# R
  appendʳ _R?_ [] ys = ys
  appendʳ _R?_ (cons x xs x#xs) ys with fresh? _R?_ x ys
  ... | yes x#ys = cons x (appendʳ _R?_ xs ys) (appendʳ-fresh _R?_ x xs x#xs ys x#ys)
  ... | no ¬x#ys = appendʳ _R?_ xs ys

  appendʳ-fresh : (_R?_ : Decidable₂ R)
               → ∀ a xs (a#xs : a # xs) ys (a#ys : a # ys)
               → a # (appendʳ _R?_ xs ys)
  appendʳ-fresh _R?_ a [] a#xs ys a#ys = a#ys
  appendʳ-fresh _R?_ a (cons x xs x#xs) (aRx ∷ a#xs) ys a#ys with fresh? _R?_ x ys
  ... | yes x#ys = aRx ∷ appendʳ-fresh _R?_ a xs a#xs ys a#ys
  ... | no ¬x#ys = appendʳ-fresh _R?_ a xs a#xs ys a#ys

-- Alternative syntax to work with our generalised _R?_
----------------
-- Properties --
----------------

module _ (_R?_ : Decidable₂ R) where
  private
    _++_ = appendʳ _R?_
    infixl 20 _++_

  appendʳ-idˡ : LeftIdentity _≡_ [] _++_
  appendʳ-idˡ _ = refl

  mutual
    appendʳ-idʳ : RightIdentity _≡_ [] _++_
    appendʳ-idʳ [] = refl
    appendʳ-idʳ (cons x xs x#xs) = cons-dcong refl (appendʳ-idʳ xs) {!!}

    appendʳ-fresh-idʳ : ∀ {x} xs x#xs
                      → (eq : xs ≡ xs ++ [])
                      → appendʳ-fresh _R?_ x xs x#xs [] [] ≡ subst (x #_) eq x#xs
    appendʳ-fresh-idʳ [] [] refl = refl
    appendʳ-fresh-idʳ (cons y ys y#ys) (xRy ∷ x∷ys) eq = {!!}

  appendʳ-assoc : Associative _≡_ _++_
  appendʳ-assoc = {!!}

  -- If (some condition on R), then the right graphic identity holds.
  -- More interesting: if the right graphic identity holds, what does that tell us about R?
  appendʳ-graphicʳ : ∀ (xs ys : List# R) → xs ++ ys ≡ xs ++ ys ++ xs
  appendʳ-graphicʳ = {!!}

  -- No matter what R is, this can never be commutative
  ¬appendʳ-comm : ¬ (Commutative _≡_ _++_)
  ¬appendʳ-comm = {!!}
