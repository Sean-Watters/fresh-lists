{-# OPTIONS --safe --cubical-compatible #-}
module Everything where

-- Freshlists defined inductive-inductively and as a sigma type, and a
-- proof that this gives isomorphic definitions
open import Data.FreshList.InductiveInductive
open import Data.FreshList.Sigma

-- Definitions of various variations on ordered monoids
open import Algebra.Structure.OICM
open import Algebra.Structure.PartialMonoid

-- Bits and pieces
open import Relation.Const
open import Relation.Unary.Finiteness
open import Relation.Binary.Isomorphism
open import Data.PosNat
open import Axiom.UniquenessOfIdentityProofs.Properties

-- Definitions of categories, functors, adjunctions
open import Category.Base

-- Freshlists for a strict total order
open import Free.IdempotentCommutativeMonoid.Base
open import Free.IdempotentCommutativeMonoid.Properties
open import Free.IdempotentCommutativeMonoid.Adjunction

-- Freshlists for a reflexive total order
open import Free.CommutativeMonoid.Base
open import Free.CommutativeMonoid.Properties
open import Free.CommutativeMonoid.Adjunction

-- Freshlists for an apartness relation
open import Free.LeftRegularMonoid.Base
open import Free.LeftRegularMonoid.Properties
open import Free.LeftRegularMonoid.Adjunction

-- Freshlists for constantly true relation
open import Free.Monoid.Base
open import Free.Monoid.Adjunction

-- Freshlists for constantly false relation
open import Free.PointedSet.Base
open import Free.PointedSet.Properties
open import Free.PointedSet.Adjunction

-- Freshlists for equality relation
open import Free.ReflexivePartialMonoid.Base
open import Free.ReflexivePartialMonoid.Properties
open import Free.ReflexivePartialMonoid.Power
open import Free.ReflexivePartialMonoid.Adjunction

-- Equivalence between Ordering Principle and Set ≃ STO
open import OrderingPrinciple.Base






