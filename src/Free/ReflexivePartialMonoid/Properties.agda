{-# OPTIONS --safe --without-K #-}

open import Axiom.UniquenessOfIdentityProofs

module Free.ReflexivePartialMonoid.Properties
  (A : Set)
  (A-set : UIP A)
  where

open import Algebra.Structure.PartialMonoid

open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Sum.Properties
open import Data.Product
open import Data.Product.Properties
open import Data.Unit

open import Function

open import Relation.Binary renaming (Irrelevant to Irrelevant₂)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Isomorphism
open import Relation.Nullary

open import Data.FreshList.InductiveInductive
open import Free.ReflexivePartialMonoid.Base A A-set


private
  cons-cong = WithIrr.cons-cong _≡_ A-set
  open _≃_

----------------------------
-- Isomorphism to 1+(A×ℕ⁺) --
----------------------------

to-from-alt : (x : FreeRPMon') → to-alt (from-alt x) ≡ x
to-from-alt (inj₁ _) = refl
to-from-alt (inj₂ (a , suc n , nonZero)) rewrite length-repeat a n = refl

rep-len : ∀ {x} xs → x # xs → repeat x (length xs) ≡ xs
rep-len [] p = refl
rep-len (cons x xs x#xs) (refl ∷ p) = cons-cong refl (rep-len xs p)

from-to-alt : (xs :  FreeRPMon) → from-alt (to-alt xs) ≡ xs
from-to-alt [] = refl
from-to-alt (cons x xs x#xs) = cons-cong refl (rep-len xs x#xs)

iso : FreeRPMon ≃ FreeRPMon'
to iso = to-alt
from iso = from-alt
from-to iso = sym ∘ from-to-alt
to-from iso = sym ∘ to-from-alt

------------
-- Is Set --
------------

suc-lem : ∀ {n m} (p : suc n ≡ suc m) → p ≡ cong suc (suc-injective p)
suc-lem refl = refl

UIP-ℕ : UIP ℕ
UIP-ℕ {zero} {zero} refl refl = refl
UIP-ℕ {suc n} {suc m} p q = trans (trans (suc-lem p) (cong (cong suc) (UIP-ℕ {n} {m} (suc-injective p) (suc-injective q)))) (sym $ suc-lem q)

pred⁺ : ℕ⁺ → ℕ
pred⁺ (suc n , p) = n

suc⁺ : ℕ → ℕ⁺
suc⁺ n = (suc n , nonZero)

UIP-ℕ⁺ : UIP ℕ⁺
UIP-ℕ⁺ = UIP-Retract suc⁺ pred⁺ (λ { (suc n , p) → refl }) UIP-ℕ

FreeRPMon'-set : UIP FreeRPMon'
FreeRPMon'-set = UIP-⊎ UIP-⊤ (UIP-× A-set UIP-ℕ⁺)

-- Likewise for the fresh list presentation.
FreeRPMon-set : UIP FreeRPMon
FreeRPMon-set = UIP-List#


-----------------------------------------------------------
-- Reflexive Partial Monoid (for Alternate Presentation) --
-----------------------------------------------------------

-- Because we may only concatenate lists which contain copies of the same element,
-- we define the domain of concatenation to be a compatibility relation which encodes
-- this invarient.

-- Compatibility: two FreeRPMons are compatible if it least one
-- is the unit, or both have the same X.
data _~'_ : FreeRPMon' → FreeRPMon' → Set where
  oneb : inj₁ tt ~' inj₁ tt
  onel : ∀ {p} → inj₁ tt ~' inj₂ p
  oner : ∀ {p} → inj₂ p ~' inj₁ tt
  rep : ∀ {n m x y} → x ≡ y → inj₂ (x , n) ~' inj₂ (y , m)

+-nonzero : (n m : ℕ⁺) → NonZero (proj₁ n + proj₁ m)
+-nonzero (suc n , _) m = record { nonZero = tt }

-- We can concatenate two compatible FreeRPMons
∙' : {xs ys : FreeRPMon'} → xs ~' ys → FreeRPMon'
∙' oneb = inj₁ tt
∙' (onel {x}) = inj₂ x
∙' (oner {x}) = inj₂ x
∙' (rep {n} {m} {x} refl) = inj₂ (x , (proj₁ n + proj₁ m) , +-nonzero n m)

~'-compatˡ-tt : ∀ {xs} → (inj₁ tt) ~' xs
~'-compatˡ-tt {inj₁ tt} = oneb
~'-compatˡ-tt {inj₂ y} = onel

~'-compatʳ-tt : ∀ {xs} → xs ~' (inj₁ tt)
~'-compatʳ-tt {inj₁ tt} = oneb
~'-compatʳ-tt {inj₂ y} = oner

~'-prop : Irrelevant₂ _~'_
~'-prop oneb oneb = refl
~'-prop onel onel = refl
~'-prop oner oner = refl
~'-prop (rep p) (rep q) = cong rep $ A-set p q

~'-reflexive : Reflexive _~'_
~'-reflexive {inj₁ tt} = oneb
~'-reflexive {inj₂ (fst , snd)} = rep refl

~'-sym : Symmetric _~'_
~'-sym oneb = oneb
~'-sym onel = oner
~'-sym oner = onel
~'-sym (rep x) = rep (sym x)

∙'-assoc₁ : {x y z : FreeRPMon'} (yz : y ~' z) → x ~' ∙' yz  → x ~' y
∙'-assoc₁ oneb p = p
∙'-assoc₁ {inj₁ tt} onel p = oneb
∙'-assoc₁ {inj₂ _} onel p = oner
∙'-assoc₁ oner p = p
∙'-assoc₁ {inj₁ tt} (rep refl) p = onel
∙'-assoc₁ {inj₂ _} (rep refl) (rep refl) = (rep refl)

∙'-assoc₂ : {x y z : FreeRPMon'} (p : y ~' z) (q : x ~' ∙' p) → ∙' (∙'-assoc₁ p q) ~' z
∙'-assoc₂ oneb oneb = oneb
∙'-assoc₂ oneb oner = oner
∙'-assoc₂ onel onel = onel
∙'-assoc₂ onel (rep refl) = (rep refl)
∙'-assoc₂ oner onel = oner
∙'-assoc₂ oner (rep refl) = oner
∙'-assoc₂ (rep refl) onel = (rep refl)
∙'-assoc₂ (rep refl) (rep refl) = (rep refl)

ℕ⁺-eq : {m n : ℕ} {pm : NonZero m} {pn : NonZero n} → m ≡ n → (m , pm) ≡ (n , pn)
ℕ⁺-eq {suc m} {pm = record { nonZero = tt }} {record { nonZero = tt }} refl = refl

∙'-assoc-eq : {x y z  : FreeRPMon'} (p : y ~' z) (q : x ~' ∙' p) → ∙' q ≡ ∙' (∙'-assoc₂ p q)
∙'-assoc-eq oneb oneb = refl
∙'-assoc-eq oneb oner = refl
∙'-assoc-eq onel onel = refl
∙'-assoc-eq onel (rep refl) = refl
∙'-assoc-eq oner onel = refl
∙'-assoc-eq oner (rep refl) = refl
∙'-assoc-eq (rep refl) onel = refl
∙'-assoc-eq {inj₂ (x , m)} {inj₂ (.x , n)} {inj₂ (.x , o)} (rep refl) (rep refl) = cong (λ z → inj₂ (x , z)) (ℕ⁺-eq (sym $ +-assoc (proj₁ m) (proj₁ n) (proj₁ o)))

∙'-identityˡ : ∀ {x} → ∙' {inj₁ tt} {x} ~'-compatˡ-tt ≡ x
∙'-identityˡ {inj₁ tt} = refl
∙'-identityˡ {inj₂ y} = refl

∙'-identityʳ : ∀ {x} → ∙' {x} {inj₁ tt} ~'-compatʳ-tt ≡ x
∙'-identityʳ {inj₁ tt} = refl
∙'-identityʳ {inj₂ y} = refl

∙'-assoc : ∀ {x y z} (yz : y ~' z) (p : x ~' ∙' yz)
         → Σ[ xy ∈ (x ~' y) ] Σ[ q ∈ (∙' xy ~' z) ] (∙' p ≡ ∙' q)
∙'-assoc yz p = (∙'-assoc₁ yz p) , (∙'-assoc₂ yz p) , (∙'-assoc-eq yz p)


isPartialMonoid' : IsPartialMonoid {A = FreeRPMon'} _≡_ _~'_ ∙' (inj₁ tt)
IsPartialMonoid.isEquivalence isPartialMonoid' = isEquivalence
IsPartialMonoid.A-set isPartialMonoid' = FreeRPMon'-set
IsPartialMonoid.R-prop isPartialMonoid' = ~'-prop
IsPartialMonoid.ε-compatˡ isPartialMonoid' = ~'-compatˡ-tt
IsPartialMonoid.ε-compatʳ isPartialMonoid' = ~'-compatʳ-tt
IsPartialMonoid.identityˡ isPartialMonoid' = ∙'-identityˡ
IsPartialMonoid.identityʳ isPartialMonoid' = ∙'-identityʳ
IsPartialMonoid.assoc isPartialMonoid' = ∙'-assoc

isReflexivePartialMonoid' : IsReflexivePartialMonoid {A = FreeRPMon'} _≡_ _~'_ ∙' (inj₁ tt)
IsReflexivePartialMonoid.isPMon isReflexivePartialMonoid' = isPartialMonoid'
IsReflexivePartialMonoid.reflexive isReflexivePartialMonoid' = ~'-reflexive

-------------------------------------------------------
-- Reflexive Partial Monoid (for FList Presentation) --
-------------------------------------------------------

-- We define compatibility of the list presentation in terms of
-- the alternate one, using the isomorphism.
_~_ : FreeRPMon → FreeRPMon → Set
x ~ y = (to-alt x) ~' (to-alt y)

-- And likewise for multiplication:
∙ : {x y : FreeRPMon} → x ~ y → FreeRPMon
∙ p = from-alt $ ∙' p

-- We can now use this to prove associativity for cheap. This would have been
-- rather hard to do directly for the fresh lists presentation.
∙-assoc₁ : {x y z : FreeRPMon} (yz : y ~ z) → x ~ ∙ yz  → x ~ y
∙-assoc₁ {x} p q
  rewrite to-from-alt (∙' p)
  = ∙'-assoc₁ p q

∙-assoc₂ : {x y z : FreeRPMon} (p : y ~ z) (q : x ~ ∙ p) → ∙ (∙-assoc₁ p q) ~ z
∙-assoc₂ p q
  rewrite to-from-alt (∙' p)
  rewrite to-from-alt (∙' (∙'-assoc₁ p q))
  = ∙'-assoc₂ p q

∙-assoc-eq : {x y z  : FreeRPMon} (p : y ~ z) (q : x ~ ∙ p) → ∙ q ≡ ∙ (∙-assoc₂ p q)
∙-assoc-eq p q
  rewrite to-from-alt (∙' p)
  rewrite to-from-alt (∙' (∙'-assoc₁ p q))
  = cong from-alt (∙'-assoc-eq p q)

∙-assoc : ∀ {x y z} (yz : y ~ z) (p : x ~ ∙ yz)
         → Σ[ xy ∈ (x ~ y) ] Σ[ q ∈ (∙ xy ~ z) ] (∙ p ≡ ∙ q)
∙-assoc yz p = (∙-assoc₁ yz p) , (∙-assoc₂ yz p) , (∙-assoc-eq yz p)

-- Identity was always going to be easy, at least.
∙-identityˡ : ∀ {x} → ∙ {[]} {x} ~'-compatˡ-tt ≡ x
∙-identityˡ {x} = trans (cong from-alt (∙'-identityˡ {to-alt x})) (from-to-alt x)

∙-identityʳ : ∀ {x} → ∙ {x} {[]} ~'-compatʳ-tt ≡ x
∙-identityʳ {x} = trans (cong from-alt (∙'-identityʳ {to-alt x})) (from-to-alt x)


-- So we get the reflexive partial monoid proof for cheap:
isPartialMonoid : IsPartialMonoid {A = FreeRPMon} _≡_ _~_ ∙ []
IsPartialMonoid.isEquivalence isPartialMonoid = isEquivalence
IsPartialMonoid.A-set isPartialMonoid = FreeRPMon-set
IsPartialMonoid.R-prop isPartialMonoid = ~'-prop
IsPartialMonoid.ε-compatˡ isPartialMonoid = ~'-compatˡ-tt
IsPartialMonoid.ε-compatʳ isPartialMonoid = ~'-compatʳ-tt
IsPartialMonoid.identityˡ isPartialMonoid = ∙-identityˡ
IsPartialMonoid.identityʳ isPartialMonoid = ∙-identityʳ
IsPartialMonoid.assoc isPartialMonoid = ∙-assoc

isReflexivePartialMonoid : IsReflexivePartialMonoid {A = FreeRPMon} _≡_ _~_ ∙ []
IsReflexivePartialMonoid.isPMon isReflexivePartialMonoid = isPartialMonoid
IsReflexivePartialMonoid.reflexive isReflexivePartialMonoid = ~'-reflexive
