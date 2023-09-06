{-# OPTIONS --safe --without-K #-}

module Data.PosNat where

open import Data.Product
open import Data.Nat

ℕ⁺ : Set
ℕ⁺ = Σ[ n ∈ ℕ ] NonZero n
