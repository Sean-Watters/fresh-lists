{-# OPTIONS --safe --without-K #-}

open import Level
open import Algebra.Structure.PartialMonoid

module Free.ReflexivePartialMonoid.Power
  {a b c : Level} {A : Set a}
  {_≈_ : A → A → Set b} {_R_ : A → A → Set c}
  {∙ : (x y : A) → x R y → A}
  {ε : A}
  (X-RPMon : IsReflexivePartialMonoid _≈_ _R_ ∙ ε)
  where

-- Theorem : Exponentiation is defined for any reflexive partial monoid.
--
-- Proof Sketch :
---- (1) By reflexivity, x^(2^n) is trivially defined for all (x : X) and (n : ℕ).
---- (2) To produce x^k, we:
-------- (a) Choose n such that (2^n)>k.
-------- (b) Re-write x^(2^n) to be right-bracketed using associativity.
-------- (c) Chop off outer x's until we have k many x's in term. This is now x^k.
--
-- We can make this easier by talking about "cute lists", thanks to conor. More at 6
