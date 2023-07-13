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

---------------------------
-- Partial Concatenation --
---------------------------

-- Because we may only concatenate lists which contain copies of the same element,
-- we define the domain of concatenation to be a compatibility relation which encodes
-- this invarient.

-- Compatibility: two lists are compatible if they contain
-- (potentially different numbers of copies of) the same element
data _~_ : FreeRPMon → FreeRPMon → Set where
  nill : ∀ {xs} → [] ~ xs
  nilr : ∀ {xs} → xs ~ []
  cons : ∀ {x y} {xs ys : FreeRPMon} {p : x # xs} {q : y # ys}
       → x ≡ y → xs ~ ys → cons x xs p ~ cons y ys q

-- We can concatenate two compatible lists.
∙ : {xs ys : FreeRPMon} → xs ~ ys → FreeRPMon
∙-fresh : {x : A} {xs ys : FreeRPMon} (p : xs ~ ys) → x # xs → x # ys → x # (∙ p)

∙ (nill {x}) = x
∙ (nilr {x}) = x
∙ {cons x xs p} {cons y ys q} (cons refl z) = cons x (cons x (∙ z) (∙-fresh z p q)) (refl ∷ (∙-fresh z p q))

∙-fresh (nill) p q = q
∙-fresh (nilr) p q = p
∙-fresh (cons refl z) (refl ∷ ps) (q ∷ qs) = refl ∷ (refl ∷ ∙-fresh z ps qs)

----------------------------------------------------
-- Properties of Compatibility and Multiplication --
----------------------------------------------------

-- Note that ~ is not transitive. a~[]~b does not imply a~b.
-- It is transitive for nonempty lists, however.

~-reflexive : Reflexive _~_
~-reflexive {[]} = nill
~-reflexive {cons x xs x#xs} = cons refl (~-reflexive {xs})

~-sym : Symmetric _~_
~-sym nill = nilr
~-sym nilr = nill
~-sym (cons refl p) = cons refl (~-sym p)

~-weakenʳ : ∀ {y xs ys} {y#ys : y # ys} → xs ~ cons y ys y#ys → xs ~ ys
~-weakenʳ nill = nill
~-weakenʳ {y#ys = []} (cons refl p) = nilr
~-weakenʳ {y#ys = q ∷ qs} (cons refl p) = cons q (~-weakenʳ p)

∙-assoc : {x y z : FreeRPMon} (yz : y ~ z) (p : x ~ ∙ yz)
             → Σ[ xy ∈ (x ~ y) ] Σ[ q ∈ (∙ xy ~ z) ] (∙ p ≡ ∙ q)
∙-assoc nill p = nilr , p , refl
∙-assoc nilr p = p , nilr , refl
∙-assoc (cons refl yz) nill = nill , (cons refl yz) , refl
∙-assoc {cons x xs x#xs} {cons .x ys y#ys} {cons .x zs z#zs} (cons refl yz) (cons refl p) = cons refl {!!} , cons refl {!!} , {!!}


isPartialMonoid : IsPartialMonoid {A = FreeRPMon} _≡_ _~_ ∙ []
IsPartialMonoid.isEquivalence isPartialMonoid = isEquivalence
IsPartialMonoid.ε-compatˡ isPartialMonoid = nill
IsPartialMonoid.ε-compatʳ isPartialMonoid = nilr
IsPartialMonoid.identityˡ isPartialMonoid = refl
IsPartialMonoid.identityʳ isPartialMonoid = refl
IsPartialMonoid.assoc isPartialMonoid = ∙-assoc

isReflexivePartialMonoid : IsReflexivePartialMonoid {A = FreeRPMon} _≡_ _~_ ∙ []
IsReflexivePartialMonoid.isPMon isReflexivePartialMonoid = isPartialMonoid
IsReflexivePartialMonoid.refl isReflexivePartialMonoid = ~-reflexive
