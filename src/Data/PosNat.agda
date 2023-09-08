{-# OPTIONS --safe --without-K #-}

module Data.PosNat where

open import Data.Product
open import Data.Nat
open import Data.Unit
open import Relation.Binary.PropositionalEquality

ℕ⁺ : Set
ℕ⁺ = Σ[ n ∈ ℕ ] NonZero n

ℕ⁺-cong : {n m : ℕ} {p : NonZero n} {q : NonZero m} → n ≡ m → (n , p) ≡ (m , q)
ℕ⁺-cong {suc _} {suc _} {record { nonZero = tt }} {record { nonZero = tt }} refl = refl
