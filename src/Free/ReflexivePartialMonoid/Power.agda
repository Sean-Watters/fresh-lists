{-# OPTIONS --safe --without-K #-}

open import Level renaming (suc to lsuc; zero to lzero)
open import Algebra.Structure.PartialMonoid
open import Relation.Binary.PropositionalEquality

module Free.ReflexivePartialMonoid.Power
  {a b : Level} {A : Set a}
  {_R_ : A → A → Set b}
  {∙ : (x y : A) → x R y → A}
  {ε : A}
  (X-RPMon : IsReflexivePartialMonoid _≡_ _R_ ∙ ε)
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



------- Direct approach -----------------------------

open import Function
open import Data.Product hiding (assocˡ; assocʳ)
open import Data.Nat
open IsReflexivePartialMonoid X-RPMon


private
  ∙-syntax = ∙
  infix 5 ∙-syntax
  syntax ∙-syntax x y r = x ∙[ r ] y


-- lemma : ∀ {x y z} → y R z → (xy↓ : x R y) → x R (x ∙[ xy↓ ] y)

lemma : ∀ {x y} → (xy↓ : x R y) → y R (x ∙[ xy↓ ] y)
lemma {x} {y} xy↓ = proj₁ $ assocʳ {x} {y} {x ∙[ xy↓ ] y} xy↓ reflexive

lemmaR : ∀ {y z} → (yz↓ : y R z) → (y ∙[ yz↓ ] z) R y
lemmaR {y} {z} yz↓ = proj₁ $ assocˡ {y ∙[ yz↓ ] z} {y} {z} yz↓ reflexive

mutual
  pow : ℕ → A → A
  pow zero x = ε
  pow (suc zero) x = x
  pow (suc (suc n)) x = x ∙[ pow-R (suc n) x ] pow (suc n) x

  powR : ℕ → A → A
  powR zero x = ε
  powR (suc zero) x = x
  powR (suc (suc n)) x = powR (suc n) x ∙[ powR-R (suc n) x ] x

  pow-commutes-gen : (n : ℕ) → (x y : A) →
                     ((xy↓ : x R y) (yx↓ : y R x) → (x ∙[ xy↓ ] y ≡ y ∙[ yx↓ ] x)) →
                     (r : x R pow n y) → (r' : powR n y R x) →
                      x ∙[ r ] pow n y ≡ powR n y ∙[ r' ] x
  pow-commutes-gen zero x y xy=yx r r' = trans (iʳ r) (sym (iˡ r'))
    where
      iʳ = identityʳ'
      iˡ = identityˡ'
  pow-commutes-gen (suc zero) x y xy=yx r r' = xy=yx r r'
  pow-commutes-gen (suc (suc n)) x y xy=yx r r' =
    let
      p = proj₁ (A← (pow-R (suc n) y) r)
      p' = proj₁ (proj₂ (A← (pow-R (suc n) y) r))
      q = proj₁ (A→ (powR-R (suc n) y) r')
      q' = proj₁ (proj₂ (A→ (powR-R (suc n) y) r'))
      q'' = subst (powR (suc n) y R_) (sym (xy=yx p q)) q'
      xyy=yxy : (xyy↓ : (x ∙[ _ ] y) R y) → (yxy↓ : y R (x ∙[ _ ] y)) →
                        (x ∙[ _ ] y) ∙[ xyy↓ ] y ≡ y ∙[ yxy↓ ] (x ∙[ _ ] y)
      xyy=yxy xyy↓ yxy↓ = begin
        (x ∙[ p ] y) ∙[ xyy↓ ] y
          ≡⟨ dcong₂ (λ z w → z ∙[ w ] y) (xy=yx p q) refl ⟩
        (y ∙[ q ] x) ∙[ subst (_R y) (xy=yx p q) xyy↓ ] y
          ≡⟨ A→₃ {y} {x} {y} q (subst (_R y) (xy=yx p q) xyy↓) p yxy↓ ⟩
        y ∙[ yxy↓ ] (x ∙[ p ] y)
          ∎
    in begin
    x ∙[ r ] (y ∙[ pow-R (suc n) y ] pow (suc n) y)
      ≡⟨ proj₂ (proj₂ (A← (pow-R (suc n) y) r)) ⟩
    (x ∙[ p ] y) ∙[ p' ] pow (suc n) y
      ≡⟨ pow-commutes-gen (suc n) (x ∙[ p ] y) y
                          xyy=yxy p' q'' ⟩
    powR (suc n) y ∙[ q'' ] (x ∙[ p ] y)
      ≡⟨ dcong₂ (λ z w → powR (suc n) y ∙[ w ] z) (xy=yx p q) (subst-subst-sym (xy=yx p q)) ⟩
    powR (suc n) y ∙[ q' ] (y ∙[ q ] x)
      ≡⟨ sym (proj₂ (proj₂ (A→ (powR-R (suc n) y) r'))) ⟩
    (powR (suc n) y ∙[ powR-R (suc n) y ] y) ∙[ r' ] x
      ∎ where
        open ≡-Reasoning
        A← = assocˡ
        A→ = assocʳ
        A→₃ = assocʳ₃

  pow-commutes : (n : ℕ) → (x : A) → (r : x R pow n x) → (r' : powR n x R x) →
                 x ∙[ r ] pow n x ≡ powR n x ∙[ r' ] x
  pow-commutes n x r r' =
    pow-commutes-gen n x x (λ p q → cong (∙ x x) (R-prop p q)) r r'

  pow-R : (n : ℕ) → (x : A) → x R pow n x
  pow-R zero x = ε-compatʳ
  pow-R (suc zero) x = reflexive
  pow-R (suc (suc n)) x = subst (x R_)
                                (sym (pow-commutes (suc n) x _ _))
                                (lemma (powR-R (suc n) x))

  powR-R : (n : ℕ) → (x : A) → powR n x R x
  powR-R zero x = ε-compatˡ
  powR-R (suc zero) x = reflexive
  powR-R (suc (suc n)) x = subst (_R x)
                                 (pow-commutes (suc n) x _ _)
                                 (lemmaR (pow-R (suc n) x))


-- Simple consequence: pow and powR agree
pow=powR : (n : ℕ) → (x : A) → pow n x ≡ powR n x
pow=powR zero x = refl
pow=powR (suc zero) x = refl
pow=powR (suc (suc n)) x = pow-commutes (suc n) x _ _
