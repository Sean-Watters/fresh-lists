open import Axiom.UniquenessOfIdentityProofs
open import Axiom.UniquenessOfIdentityProofs.Properties

module Free.ReflexivePartialMonoid.Properties
  (A : Set)
  (A-set : UIP A)
  where

open import Algebra.Structure.PartialMonoid

open import Data.Nat
open import Data.Nat.Properties
open import Data.PosNat
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


open _≃_
open WithIrr _≡_ A-set
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

FreeRPMon'-set : UIP FreeRPMon'
FreeRPMon'-set = UIP-⊎ UIP-⊤ (UIP-× A-set UIP-ℕ⁺)

-- Likewise for the fresh list presentation.
FreeRPMon-set : UIP FreeRPMon
FreeRPMon-set = UIP-List# A-set


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
∙' : (xs ys : FreeRPMon') → xs ~' ys → FreeRPMon'
∙' _ _ oneb = inj₁ tt
∙' _ _ (onel {x}) = inj₂ x
∙' _ _ (oner {x}) = inj₂ x
∙' _ _ (rep {n} {m} {x} refl) = inj₂ (x , (proj₁ n + proj₁ m) , +-nonzero n m)

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

∙'-assocL1 : {x y z : FreeRPMon'} (yz : y ~' z) → x ~' ∙' y z yz  → x ~' y
∙'-assocL1 oneb p = p
∙'-assocL1 {inj₁ tt} onel p = oneb
∙'-assocL1 {inj₂ _} onel p = oner
∙'-assocL1 oner p = p
∙'-assocL1 {inj₁ tt} (rep refl) p = onel
∙'-assocL1 {inj₂ _} (rep refl) (rep refl) = (rep refl)

∙'-assocL2 : {x y z : FreeRPMon'} (p : y ~' z) (q : x ~' ∙' y z p) → ∙' x y (∙'-assocL1 p q) ~' z
∙'-assocL2 oneb oneb = oneb
∙'-assocL2 oneb oner = oner
∙'-assocL2 onel onel = onel
∙'-assocL2 onel (rep refl) = (rep refl)
∙'-assocL2 oner onel = oner
∙'-assocL2 oner (rep refl) = oner
∙'-assocL2 (rep refl) onel = (rep refl)
∙'-assocL2 (rep refl) (rep refl) = (rep refl)

∙'-assocR1 : {x y z : FreeRPMon'} (xy : x ~' y) → ∙' x y xy ~' z  → y ~' z
∙'-assocR1 oneb oneb = oneb
∙'-assocR1 oneb onel = onel
∙'-assocR1 onel oner = oner
∙'-assocR1 onel (rep refl) = rep refl
∙'-assocR1 oner oner = oneb
∙'-assocR1 oner (rep refl) = onel
∙'-assocR1 (rep refl) oner = oner
∙'-assocR1 (rep refl) (rep refl) = rep refl

∙'-assocR2 : {x y z : FreeRPMon'} (p : x ~' y) (q : ∙' x y p ~' z) → x ~' ∙' y z (∙'-assocR1 p q)
∙'-assocR2 oneb oneb = oneb
∙'-assocR2 oneb onel = onel
∙'-assocR2 onel oner = onel
∙'-assocR2 onel (rep refl) = onel
∙'-assocR2 oner oner = oner
∙'-assocR2 oner (rep refl) = rep refl
∙'-assocR2 (rep refl) oner = rep refl
∙'-assocR2 (rep refl) (rep refl) = rep refl

ℕ⁺-eq : {m n : ℕ} {pm : NonZero m} {pn : NonZero n} → m ≡ n → (m , pm) ≡ (n , pn)
ℕ⁺-eq {suc m} {pm = record { nonZero = tt }} {record { nonZero = tt }} refl = refl

∙'-assoc-Leq : {x y z  : FreeRPMon'} (p : y ~' z) (q : x ~' ∙' y z p) → ∙' _ _ q ≡ ∙' _ _ (∙'-assocL2 p q)
∙'-assoc-Leq oneb oneb = refl
∙'-assoc-Leq oneb oner = refl
∙'-assoc-Leq onel onel = refl
∙'-assoc-Leq onel (rep refl) = refl
∙'-assoc-Leq oner onel = refl
∙'-assoc-Leq oner (rep refl) = refl
∙'-assoc-Leq (rep refl) onel = refl
∙'-assoc-Leq {inj₂ (x , m)} {inj₂ (.x , n)} {inj₂ (.x , o)} (rep refl) (rep refl) = cong (λ z → inj₂ (x , z)) (ℕ⁺-eq (sym $ +-assoc (proj₁ m) (proj₁ n) (proj₁ o)))

∙'-assoc-Req : {x y z  : FreeRPMon'} (p : x ~' y) (q : ∙' x y p ~' z) → ∙' _ _ q ≡ ∙' _ _ (∙'-assocR2 p q)
∙'-assoc-Req oneb oneb = refl
∙'-assoc-Req oneb onel = refl
∙'-assoc-Req onel oner = refl
∙'-assoc-Req onel (rep refl) = refl
∙'-assoc-Req oner oner = refl
∙'-assoc-Req oner (rep refl) = refl
∙'-assoc-Req (rep refl) oner = refl
∙'-assoc-Req {inj₂ (x , m)} {inj₂ (x , n)} {inj₂ (x , o)} (rep refl) (rep refl) =  cong (λ z → inj₂ (x , z)) (ℕ⁺-eq (+-assoc (proj₁ m) (proj₁ n) (proj₁ o)))

∙'-identityˡ : ∀ {x} → ∙' (inj₁ tt) x ~'-compatˡ-tt ≡ x
∙'-identityˡ {inj₁ tt} = refl
∙'-identityˡ {inj₂ y} = refl

∙'-identityʳ : ∀ {x} → ∙' x (inj₁ tt) ~'-compatʳ-tt ≡ x
∙'-identityʳ {inj₁ tt} = refl
∙'-identityʳ {inj₂ y} = refl

∙'-assocˡ : ∀ {x y z} (yz : y ~' z) (p : x ~' ∙' _ _ yz)
         → Σ[ xy ∈ (x ~' y) ] Σ[ q ∈ (∙' _ _ xy ~' z) ] (∙' _ _ p ≡ ∙' _ _ q)
∙'-assocˡ yz p = (∙'-assocL1 yz p) , (∙'-assocL2 yz p) , (∙'-assoc-Leq yz p)

∙'-assocʳ : ∀ {x y z} (xy : x ~' y) (p : ∙' x y xy ~' z)
         → Σ[ yz ∈ (y ~' z) ] Σ[ q ∈ (x ~' ∙' y z yz) ] (∙' _ _ p ≡ ∙' _ _ q)
∙'-assocʳ xy p = ∙'-assocR1 xy p , ∙'-assocR2 xy p , ∙'-assoc-Req xy p

isPartialMonoid' : IsPartialMonoid {A = FreeRPMon'} _≡_ _~'_ ∙' (inj₁ tt)
IsPartialMonoid.isEquivalence isPartialMonoid' = isEquivalence
IsPartialMonoid.A-set isPartialMonoid' = FreeRPMon'-set
IsPartialMonoid.R-prop isPartialMonoid' = ~'-prop
IsPartialMonoid.ε-compatˡ isPartialMonoid' = ~'-compatˡ-tt
IsPartialMonoid.ε-compatʳ isPartialMonoid' = ~'-compatʳ-tt
IsPartialMonoid.identityˡ isPartialMonoid' = ∙'-identityˡ
IsPartialMonoid.identityʳ isPartialMonoid' = ∙'-identityʳ
IsPartialMonoid.assocˡ isPartialMonoid' = ∙'-assocˡ
IsPartialMonoid.assocʳ isPartialMonoid' = ∙'-assocʳ

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
∙ : (x y : FreeRPMon) → x ~ y → FreeRPMon
∙ _ _ p = from-alt $ ∙' _ _ p

-- We can now use this to prove associativity for cheap. This would have been
-- rather hard to do directly for the fresh lists presentation.
∙-assocL1 : {x y z : FreeRPMon} (yz : y ~ z) → x ~ ∙ y z yz  → x ~ y
∙-assocL1 {x} p q
  rewrite to-from-alt (∙' _ _ p)
  = ∙'-assocL1 p q

∙-assocL2 : {x y z : FreeRPMon} (p : y ~ z) (q : x ~ ∙ y z p) → ∙ _ _ (∙-assocL1 p q) ~ z
∙-assocL2 p q
  rewrite to-from-alt (∙' _ _ p)
  rewrite to-from-alt (∙' _ _ (∙'-assocL1 p q))
  = ∙'-assocL2 p q

∙-assoc-Leq : {x y z  : FreeRPMon} (p : y ~ z) (q : x ~ ∙ y z p) → ∙ x _ q ≡ ∙ _ _ (∙-assocL2 p q)
∙-assoc-Leq p q
  rewrite to-from-alt (∙' _ _ p)
  rewrite to-from-alt (∙' _ _ (∙'-assocL1 p q))
  = cong from-alt (∙'-assoc-Leq p q)

∙-assocˡ : ∀ {x y z} (yz : y ~ z) (p : x ~ ∙ _ _ yz)
         → Σ[ xy ∈ (x ~ y) ] Σ[ q ∈ (∙ _ _ xy ~ z) ] (∙ _ _ p ≡ ∙ _ _ q)
∙-assocˡ yz p = (∙-assocL1 yz p) , (∙-assocL2 yz p) , (∙-assoc-Leq yz p)

∙-assocR1 : {x y z : FreeRPMon} (xy : x ~ y) → ∙ x y xy ~ z  → y ~ z
∙-assocR1 {x} p q
  rewrite to-from-alt (∙' _ _ p)
  = ∙'-assocR1 p q

∙-assocR2 : {x y z : FreeRPMon} (p : x ~ y) (q : ∙ x y p ~ z) → x ~ ∙ _ _ (∙-assocR1 p q)
∙-assocR2 p q
  rewrite to-from-alt (∙' _ _ p)
  rewrite to-from-alt (∙' _ _ (∙'-assocR1 p q))
  = ∙'-assocR2 p q

∙-assoc-Req : {x y z  : FreeRPMon} (p : x ~ y) (q : ∙ x y p ~ z) → ∙ _ _ q ≡ ∙ _ _ (∙-assocR2 p q)
∙-assoc-Req p q
  rewrite to-from-alt (∙' _ _ p)
  rewrite to-from-alt (∙' _ _ (∙'-assocR1 p q))
  = cong from-alt (∙'-assoc-Req p q)

∙-assocʳ : ∀ {x y z} (xy : x ~ y) (p : ∙ x y xy ~ z)
         → Σ[ yz ∈ (y ~ z) ] Σ[ q ∈ (x ~ ∙ y z yz) ] (∙ _ _ p ≡ ∙ _ _ q)
∙-assocʳ xy p = ∙-assocR1 xy p , ∙-assocR2 xy p , ∙-assoc-Req xy p

-- Identity was always going to be easy, at least.
∙-identityˡ : ∀ {x} → ∙ [] x ~'-compatˡ-tt ≡ x
∙-identityˡ {x} = trans (cong from-alt (∙'-identityˡ {to-alt x})) (from-to-alt x)

∙-identityʳ : ∀ {x} → ∙ x [] ~'-compatʳ-tt ≡ x
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
IsPartialMonoid.assocˡ isPartialMonoid = ∙-assocˡ
IsPartialMonoid.assocʳ isPartialMonoid = ∙-assocʳ

isReflexivePartialMonoid : IsReflexivePartialMonoid {A = FreeRPMon} _≡_ _~_ ∙ []
IsReflexivePartialMonoid.isPMon isReflexivePartialMonoid = isPartialMonoid
IsReflexivePartialMonoid.reflexive isReflexivePartialMonoid = ~'-reflexive


-----------------
-- Relatedness --
-----------------

-- If xn ~ ym, then x ≡ y.
~'→≡ : {x y : A} {n m : ℕ⁺} → (inj₂ $ x , n) ~' (inj₂ $ y , m) → x ≡ y
~'→≡ (rep refl) = refl
