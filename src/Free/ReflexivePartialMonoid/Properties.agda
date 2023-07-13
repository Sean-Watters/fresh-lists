{-# OPTIONS --safe --without-K #-}

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Free.ReflexivePartialMonoid.Properties
  (A : Set)
  (A-set : Irrelevant (_≡_ {A = A}))
  where

open import Algebra.Structure.PartialMonoid

open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Unit

open import Function

open import Relation.Binary.Isomorphism

open import Data.FreshList.InductiveInductive
open import Free.ReflexivePartialMonoid.Base A A-set

private
  cons-cong = WithIrr.cons-cong _≡_ A-set
  open _≃_

----------------------------
-- Isomorphism to 1+(A×ℕ⁺) --
----------------------------

to-from-alt : (x : ⊤ ⊎ (A × ℕ⁺)) → to-alt (from-alt x) ≡ x
to-from-alt (inj₁ _) = refl
to-from-alt (inj₂ (a , suc n , record { nonZero = tt })) rewrite length-repeat a n = refl

from-to-alt : (xs :  FreeRPMon) → from-alt (to-alt xs) ≡ xs
from-to-alt [] = refl
from-to-alt (cons x xs x#xs) = cons-cong refl (lemma xs x#xs)
  where
    lemma : ∀ {x} xs → x # xs → repeat x (length xs) ≡ xs
    lemma [] p = refl
    lemma (cons x xs x#xs) (refl ∷ p) = cons-cong refl (lemma xs p)

iso : FreeRPMon ≃ (⊤ ⊎ (A × ℕ⁺))
to iso = to-alt
from iso = from-alt
from-to iso = sym ∘ from-to-alt
to-from iso = sym ∘ to-from-alt

----------------------------
-- Observational Equality --
----------------------------

data Eq : FreeRPMon → FreeRPMon → Set where
  [] : Eq [] []
  _∷_ : {x y : A} {xs ys : FreeRPMon} {x#xs : x # xs} {y#ys : y # ys}
      → x ≡ y → Eq xs ys → Eq (cons x xs x#xs) (cons y ys y#ys)

Eq→≡ : ∀ {xs ys} → Eq xs ys → xs ≡ ys
Eq→≡ [] = refl
Eq→≡ (p ∷ ps) = cons-cong p (Eq→≡ ps)

≡→Eq : ∀ {xs ys} → xs ≡ ys → Eq xs ys
≡→Eq {[]} refl = []
≡→Eq {cons x xs x#xs} refl = refl ∷ (≡→Eq {xs} refl)

Eq→≡→Eq : ∀ {xs ys} → (p : Eq xs ys) → ≡→Eq (Eq→≡ p) ≡ p
Eq→≡→Eq {[]} [] = refl
Eq→≡→Eq {cons x xs x#xs} (refl ∷ ps) = {!!}

≡→Eq→≡ : ∀ {xs ys} → (p : xs ≡ ys) → Eq→≡ (≡→Eq p) ≡ p
≡→Eq→≡ {[]} refl = refl
≡→Eq→≡ {cons x xs x#xs} refl = {!!}

≡→Eq-injective : ∀ {xs ys} → (p q : xs ≡ ys) → ≡→Eq p ≡ ≡→Eq q → p ≡ q
≡→Eq-injective {[]} refl refl r = refl
≡→Eq-injective {cons x xs x#xs} refl q r = {!!}

Eq-prop : ∀ {xs ys} → (p q : Eq xs ys) → p ≡ q
Eq-prop [] [] = refl
Eq-prop (p ∷ ps) (q ∷ qs) = cong₂ _∷_ (A-set p q) (Eq-prop ps qs)

is-set : {x y : FreeRPMon} → (p q : x ≡ y) → p ≡ q
is-set p q = {!!}

------------------------------
-- Reflexive Partial Monoid --
------------------------------

-- The minimal compatibility relation which satisfies the reflexive
-- partial monoid axioms.
data _~_ : FreeRPMon → FreeRPMon → Set where
  nill : ∀ x → [] ~ x
  nilr : ∀ x → x ~ []
  refl : ∀ x → x ~ x

-- Double, except with a type that looks more like refl pmon multiplication
double' : {x y : FreeRPMon} → x ~ y → FreeRPMon
double' (nill x) = x
double' (nilr x) = x
double' (refl x) = double x

isPartialMonoid : IsPartialMonoid {A = FreeRPMon} _≡_ _~_ double' []
IsPartialMonoid.isEquivalence isPartialMonoid = isEquivalence
IsPartialMonoid.ε-compatˡ isPartialMonoid = nill
IsPartialMonoid.ε-compatʳ isPartialMonoid = nilr
IsPartialMonoid.identityˡ isPartialMonoid _ = refl
IsPartialMonoid.identityʳ isPartialMonoid _ = refl
IsPartialMonoid.assoc isPartialMonoid = {!!}

isReflexivePartialMonoid : IsReflexivePartialMonoid {A = FreeRPMon} _≡_ _~_ double' []
IsReflexivePartialMonoid.isPMon isReflexivePartialMonoid = isPartialMonoid
IsReflexivePartialMonoid.refl isReflexivePartialMonoid = refl
