{-# OPTIONS --safe --without-K #-}

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Free.ReflexivePartialMonoid.Properties
  (A : Set)
  (A-set : Irrelevant (_≡_ {A = A}))
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

open import Relation.Binary.Isomorphism

open import Data.FreshList.InductiveInductive
open import Free.ReflexivePartialMonoid.Base A A-set

open import Axiom.UniquenessOfIdentityProofs

private
  cons-cong = WithIrr.cons-cong _≡_ A-set
  open _≃_

----------------------------
-- Isomorphism to 1+(A×ℕ⁺) --
----------------------------

to-from-alt : (x : FreeRPMon') → to-alt (from-alt x) ≡ x
to-from-alt (inj₁ _) = refl
to-from-alt (inj₂ (a , suc n , record { nonZero = tt })) rewrite length-repeat a n = refl

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

-- Lemma: UIP is closed under coproducts

inj₁-lem : ∀ {ℓx ℓy} {X : Set ℓx} {Y : Set ℓy} {x y : X} (p : _≡_ {A = X ⊎ Y} (inj₁ x) (inj₁ y)) → p ≡ cong inj₁ (inj₁-injective p)
inj₁-lem refl = refl

inj₁-injective-injective : ∀ {ℓx ℓy} {X : Set ℓx} {Y : Set ℓy} {x y : X} (p q : _≡_ {A = X ⊎ Y} (inj₁ x) (inj₁ y)) → inj₁-injective p ≡ inj₁-injective q → p ≡ q
inj₁-injective-injective p q u = trans (inj₁-lem p) (trans (cong (cong inj₁) u) (sym $ inj₁-lem q))

inj₂-lem : ∀ {ℓx ℓy} {X : Set ℓx} {Y : Set ℓy} {x y : Y} (p : _≡_ {A = X ⊎ Y} (inj₂ x) (inj₂ y)) → p ≡ cong inj₂ (inj₂-injective p)
inj₂-lem refl = refl

inj₂-injective-injective : ∀ {ℓx ℓy} {X : Set ℓx} {Y : Set ℓy} {x y : Y} (p q : _≡_ {A = X ⊎ Y} (inj₂ x) (inj₂ y)) → inj₂-injective p ≡ inj₂-injective q → p ≡ q
inj₂-injective-injective p q u = trans (inj₂-lem p) (trans (cong (cong inj₂) u) (sym $ inj₂-lem q))

UIP-⊎ : ∀ {ℓx ℓy} {X : Set ℓx} {Y : Set ℓy} → UIP X → UIP Y → UIP (X ⊎ Y)
UIP-⊎ uipX uipY {inj₁ x} {inj₁ y} p q = inj₁-injective-injective p q $ uipX (inj₁-injective p) (inj₁-injective q) 
UIP-⊎ uipX uipY {inj₂ x} {inj₂ y} p q = inj₂-injective-injective p q $ uipY (inj₂-injective p) (inj₂-injective q)

-- Lemma: UIP is closed under non-dependent pairs (idk about the dependent case, it might be true but it's probably harder and not needed)

-- dependent double map, or something like that? whatever it is, it's the thing we need
plumb : ∀ {ℓa ℓb ℓc ℓd} {A : Set ℓa} {B : Set ℓb} {C : A → A → Set ℓc} {D : B → B → Set ℓd}
      → (f : (x y : A) → C x y) (g : (x y : B) → D x y)
      → (p q : A × B) → C (proj₁ p) (proj₁ q) × D (proj₂ p) (proj₂ q)
plumb f g (a1 , b1) (a2 , b2) = f a1 a2 , g b1 b2

,-lem : ∀ {ℓx ℓy} {X : Set ℓx} {Y : Set ℓy} {x1 x2 : X} {y1 y2 : Y} (p : (x1 , y1) ≡ (x2 , y2))
          → p ≡ cong₂ _,_ (proj₁ $ ,-injective p) (proj₂ $ ,-injective p)
,-lem refl = refl

repackage : ∀ {ℓx ℓy} {X : Set ℓx} {Y : Set ℓy} {x1 x2 : X} {y1 y2 : Y}
          → (p q : (x1 , y1) ≡ (x2 , y2))
          → proj₁ (,-injective p) ≡ proj₁ (,-injective q) × proj₂ (,-injective p) ≡ proj₂ (,-injective q)
          → p ≡ q
repackage p q (u , v) = trans (,-lem p) (trans (cong₂ (cong₂ _,_) u v) (sym $ ,-lem q))

UIP-× : ∀ {ℓx ℓy} {X : Set ℓx} {Y : Set ℓy} → UIP X → UIP Y → UIP (X × Y)
UIP-× uipX uipY {x1 , y1} {x2 , y2} p q = repackage p q $ plumb uipX uipY (,-injective p) (,-injective q)

-- Lemma: UIP is preserved by isomorphism.

UIP-≃ : ∀ {ℓ} {X : Set ℓ} {Y : Set ℓ} → UIP X → X ≃ Y → UIP Y
UIP-≃ uipX iso p q =
  begin
    p
  ≡⟨ (sym $ cong-id p) ⟩
    cong id p
  ≡⟨ subst (λ f → cong f p ≡ cong f q) {!sym ∘ to-from iso!} lem  ⟩ -- requires extensionality! :(
    cong id q
  ≡⟨ cong-id q ⟩
    q
  ∎ where
  open ≡-Reasoning
  lem : cong (λ x → to iso (from iso x)) p ≡ cong (λ x → to iso (from iso x)) q
  lem =
    begin
      cong (to iso ∘ from iso) p
    ≡⟨ cong-∘ p ⟩
      cong (to iso) (cong (from iso) p)
    ≡⟨ cong (cong (to iso)) $ uipX (cong (from iso) p) (cong (from iso) q) ⟩
      cong (to iso) (cong (from iso) q)
    ≡⟨ sym $ cong-∘ q ⟩
      cong (to iso ∘ from iso) q
    ∎


FreeRPMon'-set : {x y : FreeRPMon'} (a b : x ≡ y) → a ≡ b
FreeRPMon'-set = {!!}

-- Likewise for the fresh list presentation.
FreeRPMon-set : {x y : FreeRPMon} (a b : x ≡ y) → a ≡ b
FreeRPMon-set = {!Constant⇒UIP.≡-irrelevant!}


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

~'-prop : Irrelevant _~'_
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
