{-# OPTIONS --without-K --safe #-}
open import Algebra
open import Data.Product
open import Relation.Binary hiding (Irrelevant)

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty

module Algebra.Structure.OICM where

record IsPropDecTotalOrder
  { S : Set }
  ( _≈_ : S → S → Set )
  ( _≤_ : S → S → Set )
  : Set where
  constructor MkDto
  field
    isDTO : IsDecTotalOrder _≈_ _≤_
    ≤-prop : ∀ {x y} → Irrelevant (x ≤ y)
  open IsDecTotalOrder isDTO public

-- This is going to be such a pain
-- irrelevant : {S : Set} {_≈_ _≤_ : S → S → Set} → Irrelevant (IsPropDecTotalOrder _≈_ _≤_)
-- irrelevant S T = {!IsPropDecTotalOrder.≤-prop S!}

-- NB: **Necessarily** strictly ordered when idempotent, non-strict when not.
record IsOrderedCommutativeMonoid
  { S : Set }
  ( _≈_ : S → S → Set )
  ( _≤_ : S → S → Set )
  ( _∙_ : S → S → S )
  ( ε : S )
  : Set where
  field
    isICM : IsCommutativeMonoid _≈_ _∙_ ε
    isPDTO : IsPropDecTotalOrder _≈_ _≤_
  open IsPropDecTotalOrder isPDTO
  open IsCommutativeMonoid isICM hiding (refl; sym; trans) public

record IsOrderedIdempotentCommutativeMonoid
  { S : Set }
  ( _≈_ : S → S → Set )
  ( _<_ : S → S → Set )
  ( _∙_ : S → S → S )
  ( ε : S )
  : Set where
  field
    isICM : IsIdempotentCommutativeMonoid _≈_ _∙_ ε
    isSTO : IsStrictTotalOrder _≈_ _<_

    -- This is a sensible thing to ask, but is not true for sorted lists with lexicographic order.
    -- ∙-preservesˡ-< : ∀ {a b} x → a < b → (x ∙ a) < (x ∙ b)

    -- This is also too strong, but might be an interesting thing to think about.
    -- ε-minimal : ∀ {a} → ε ≢ a → ε < a

  open IsStrictTotalOrder
  open IsIdempotentCommutativeMonoid hiding (refl; sym; trans) public

  -- These follow from ∙-preservesˡ-<
  {-
  ∙-preservesʳ-< : ∀ {a b} x → a < b → (a ∙ x) < (b ∙ x)
  ∙-preservesʳ-< {a} {b} x a<b = <-respˡ-≈ isSTO (comm isICM x a) (<-respʳ-≈ isSTO (comm isICM x b) (∙-preservesˡ-< x a<b))

  ∙-preserves-< : ∀ {x y x' y'} → x < x' → y < y' → (x ∙ y) < (x' ∙ y')
  ∙-preserves-< {x} {y' = y'} px py = IsStrictTotalOrder.trans isSTO (∙-preservesˡ-< x py) (∙-preservesʳ-< y' px)
  -}

--apparently partially ordered monoids are monoidal categories that are both skeletal and thin.
--(is that with the ∙-preserves-< condition???)
--wonder what the categorical view on totally ordered idempotent commmutative monoids are.
