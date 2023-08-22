{-# OPTIONS --safe --without-K #-}
module Algebra.Structure.PartialMonoid where

open import Level
open import Algebra.Core
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)

record IsPartialMonoid
  {a b c} {A : Set a}
  (_≈_ : Rel A b) (_R_ : Rel A c)
  (∙[_] : {x y : A} → x R y → A)
  (ε : A)
  : Set (a ⊔ b ⊔ c) where
  field
    isEquivalence : IsEquivalence _≈_
    A-set : Irrelevant (_≡_ {A = A})
    R-prop : Irrelevant _R_
    ε-compatˡ : ∀ {x} → ε R x
    ε-compatʳ : ∀ {x} → x R ε
    identityˡ : ∀ {x} → ∙[ ε-compatˡ {x} ] ≈ x
    identityʳ : ∀ {x} → ∙[ ε-compatʳ {x} ] ≈ x
    assoc : ∀ {x y z} → (yz : y R z) → (p : x R (∙[ yz ])) → Σ[ xy ∈ x R y ] Σ[ q ∈ ∙[ xy ] R z ] (∙[ p ] ≈ ∙[ q ])

record IsReflexivePartialMonoid
  {a b c} {A : Set a}
  (_≈_ : Rel A b) (_R_ : Rel A c)
  (∙[_] : {x y : A} → x R y → A)
  (ε : A)
  : Set (a ⊔ b ⊔ c) where
  field
    isPMon : IsPartialMonoid _≈_ _R_ ∙[_] ε
    reflexive : ∀ {x} → x R x
  open IsPartialMonoid public
