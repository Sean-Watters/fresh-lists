open import Level renaming (suc to lsuc; zero to lzero)
open import Algebra.Structure.PartialMonoid
open import Relation.Binary.PropositionalEquality

module Free.ReflexivePartialMonoid.Power
  {ℓa ℓb : Level} {A : Set ℓa}
  {_R_ : A → A → Set ℓb}
  {∙ : (x y : A) → x R y → A}
  {ε : A}
  (X-RPMon : IsReflexivePartialMonoid _≡_ _R_ ∙ ε)
  where

open import Function
open import Data.Product hiding (assocˡ; assocʳ)
open import Data.Nat
open import Data.Nat.Properties
open IsReflexivePartialMonoid X-RPMon


private
  ∙-syntax = ∙
  infix 5 ∙-syntax
  syntax ∙-syntax x y r = x ∙[ r ] y

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

----------------
-- Properties --
----------------


∙-cong : ∀ {x y x' y'} {r : x R y} {r' : x' R y'}
       → x ≡ x' → y ≡ y' → x ∙[ r ] y ≡ x' ∙[ r' ] y'
∙-cong {x} {y} refl refl = cong (∙-syntax x y) (R-prop _ _)

-- computes the new R
∙-cong' : ∀ {x y x' y'} (r : x R y)
       → x ≡ x' → y ≡ y'
       → Σ[ r' ∈ (x' R y') ] (x ∙[ r ] y ≡ x' ∙[ r' ] y')
∙-cong' {x} {y} r refl refl = r , cong (∙-syntax x y) (R-prop _ _)


-- pow and powR agree
pow=powR : (n : ℕ) → (x : A) → pow n x ≡ powR n x
pow=powR zero x = refl
pow=powR (suc zero) x = refl
pow=powR (suc (suc n)) x = pow-commutes (suc n) x _ _

-- And so we don't need to talk about powR at all any more.
powR-R' : (n : ℕ) → (x : A) → pow n x R x
powR-R' n x = subst (_R x) (sym $ pow=powR n x) (powR-R n x)


pow-commutes' : (n : ℕ) (x : A) (r : x R pow n x) (r' : pow n x R x)
              → x ∙[ r ] pow n x ≡ pow n x ∙[ r' ] x
pow-commutes' n x r r' = trans (pow-commutes n x r (subst (_R x) (pow=powR n x) r')) (∙-cong (sym $ pow=powR n x) refl)

-- x(x^n) ≡ x^(n+1)
pow-suc : ∀ n x → (r : x R pow n x) → x ∙[ r ] pow n x ≡ pow (suc n) x
pow-suc zero x r = trans (cong (∙ x ε) (R-prop _ _)) (identityʳ {x})
pow-suc (suc n) x r =
  begin
    x ∙[ r ] (pow (suc n) x)
  ≡⟨ ∙-cong refl (sym $ pow-suc n x (pow-R n x)) ⟩
    x ∙[ subst (x R_) (sym $ pow-suc n x (pow-R n x)) (pow-R (suc n) x) ] (x ∙[ pow-R n x ] (pow n x))
  ≡⟨ ∙-cong refl (pow-suc n x (pow-R n x))  ⟩
    pow (suc (suc n)) x
  ∎ where open ≡-Reasoning

-- If (x^n)(x^m) is defined, then (x^n+1)(x^m-1) is defined.
pow-R-step : ∀ n m x → (pow n x) R (pow (suc m) x) → (pow (suc n) x) R (pow m x)
pow-R-step zero m x r = pow-R m x
pow-R-step (suc n) zero x r = ε-compatʳ
pow-R-step (suc n) (suc m) x xˢⁿRxxˢᵐ = xxˢⁿRxˢᵐ where
  -- The monomials that appear in the derivation.
  xᵐ  = pow m x
  xⁿ  = pow n x
  xˢᵐ = pow (suc m) x
  xˢⁿ = pow (suc n) x

  -- The required proofs that the individual monomials are related to x in various directions.
  xRxᵐ  = pow-R m x
  xRxⁿ  = pow-R n x
  xRxˢⁿ = pow-R (suc n) x
  xRxˢᵐ = pow-R (suc m) x
  xˢⁿRx = powR-R' (suc n) x
  xⁿRx  = powR-R' n x

  -- The proofs that involve one layer of multiplication. These are required to state the types of later steps.
  xRxxᵐ : x R (x ∙[ xRxᵐ ] xᵐ)
  xRxxᵐ = subst (x R_) (sym $ pow-suc m x xRxᵐ) xRxˢᵐ

  xxⁿRx : (x ∙[ xRxⁿ ] xⁿ) R x
  xxⁿRx = subst (_R x) (sym $ pow-suc n x xRxⁿ) xˢⁿRx

  xRxⁿx : x R (xⁿ ∙[ xⁿRx ] x)
  xRxⁿx = subst (x R_) (trans (sym $ pow-suc n x xRxⁿ) (pow-commutes' n x xRxⁿ xⁿRx)) xRxˢⁿ

  -- The derivation proper, starting from the assumption and arriving at the goal.
  xxⁿRx∙xxᵐ : (x ∙[ xRxⁿ ] xⁿ) R (x ∙[ xRxxᵐ ] (x ∙[ xRxᵐ ] xᵐ))
  xxⁿRx∙xxᵐ = subst₂ _R_ (sym $ pow-suc n x xRxⁿ) (∙-cong refl (sym $ pow-suc m x xRxᵐ)) xˢⁿRxxˢᵐ -- the assumption

  xxⁿ∙xRxxᵐ : ((x ∙[ xRxⁿ ] xⁿ) ∙[ xxⁿRx ] x) R (x ∙[ xRxᵐ ] xᵐ)
  xxⁿ∙xRxxᵐ = subst (_R (x ∙[ xRxᵐ ] xᵐ)) (∙-cong refl refl) (proj₂ $ assocL1 xRxxᵐ xxⁿRx∙xxᵐ)

  x∙xⁿxRxxᵐ : (x ∙[ xRxⁿx ] (xⁿ ∙[ xⁿRx ] x)) R (x ∙[ xRxᵐ ] xᵐ)
  x∙xⁿxRxxᵐ = subst (_R (x ∙[ xRxᵐ ] xᵐ)) (assocʳ₃ xRxⁿ xxⁿRx xⁿRx xRxⁿx) xxⁿ∙xRxxᵐ

  xxˢⁿRxˢᵐ : (x ∙[ xRxˢⁿ ] xˢⁿ) R xˢᵐ -- the goal
  xxˢⁿRxˢᵐ = subst₂ _R_ (∙-cong refl (trans (sym $ pow-commutes' n x xRxⁿ xⁿRx) (pow-suc n x xRxⁿ))) (pow-suc m x xRxᵐ) x∙xⁿxRxxᵐ



-- We can apply the above step lemma k many times, so that
-- if any bracketing of x^n is defined, they all are.
pow-R-steps : ∀ k n m x → (pow n x) R (pow (m + k) x) → (pow (n + k) x) R (pow m x)
pow-R-steps zero n m x r = subst₂ (λ u v → pow u x R pow v x) (sym $ +-identityʳ n) (+-identityʳ m) r
pow-R-steps (suc k) n m x r = subst (λ z → pow z x R pow m x) (sym $ +-suc n k) (pow-R-step (n + k) m x (pow-R-steps k n (suc m) x (subst (λ z → pow n x R pow z x) (+-suc m k) r)))

-- And therefore, (x^n)(x^m) is always defined for all n and m.
powRpow : ∀ n m x → (pow n x) R (pow m x)
powRpow n m x = pow-R-steps n 0 m x ε-compatˡ

-- (x^n)(x^m) ≡ x^(n+m)
pow-mult : ∀ n m x → (r : pow n x R pow m x) → pow n x ∙[ r ] pow m x ≡ pow (n + m) x
pow-mult zero m x r = trans (cong (∙ ε (pow m x)) (R-prop r ε-compatˡ)) (identityˡ {pow m x})
pow-mult (suc n) m x r =
  begin
    (pow (suc n) x) ∙[ r ] xᵐ
  ≡⟨ ∙-cong (sym $ pow-suc n x xRxⁿ) refl ⟩
    (x ∙[ xRxⁿ ] xⁿ) ∙[ xxⁿRxᵐ ] xᵐ
  ≡⟨ assocʳ₃ {x} {xⁿ} {xᵐ} xRxⁿ xxⁿRxᵐ xⁿRxᵐ xRxⁿxᵐ ⟩
    x ∙[ xRxⁿxᵐ ] (xⁿ ∙[ xⁿRxᵐ ] xᵐ)
  ≡⟨ ∙-cong refl (pow-mult n m x xⁿRxᵐ) ⟩
    x ∙[ pow-R (n + m) x ] xⁿ⁺ᵐ
  ≡⟨ pow-suc (n + m) x xRxⁿ⁺ᵐ ⟩
    pow (suc n + m) x
  ∎ where
    open ≡-Reasoning
    xⁿ = pow n x
    xᵐ = pow m x
    xⁿ⁺ᵐ = pow (n + m) x
    xRxⁿ = pow-R n x
    xRxⁿ⁺ᵐ = pow-R (n + m) x
    xⁿRxᵐ = powRpow n m x

    xxⁿRxᵐ : (x ∙[ xRxⁿ ] xⁿ) R xᵐ
    xxⁿRxᵐ = subst (_R xᵐ) (sym $ pow-suc n x xRxⁿ) r

    xRxⁿxᵐ : x R (xⁿ ∙[ xⁿRxᵐ ] xᵐ)
    xRxⁿxᵐ = subst (x R_) (sym $ pow-mult n m x xⁿRxᵐ) (pow-R (n + m) x)
