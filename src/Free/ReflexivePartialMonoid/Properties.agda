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
open import Data.Product
open import Data.Product.Properties
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
-- Compatibility --
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

~-reflexive : Reflexive _~_
~-reflexive {[]} = nill
~-reflexive {cons x xs x#xs} = cons refl (~-reflexive {xs})

~-sym : Symmetric _~_
~-sym nill = nilr
~-sym nilr = nill
~-sym (cons refl p) = cons refl (~-sym p)

~-comm : ∀ {x y} → x ~ y → y ~ x
~-comm nill = nilr
~-comm nilr = nill
~-comm (cons refl p) = cons refl (~-comm p)

~-weakenʳ : ∀ {y xs ys} {y#ys : y # ys} → xs ~ cons y ys y#ys → xs ~ ys
~-weakenʳ nill = nill
~-weakenʳ {y#ys = []} (cons refl p) = nilr
~-weakenʳ {y#ys = q ∷ qs} (cons refl p) = cons q (~-weakenʳ p)

~-weakenˡ : ∀ {x xs ys} {x#xs : x # xs} → cons x xs x#xs ~ ys → xs ~ ys
~-weakenˡ nilr = nilr
~-weakenˡ {x#xs = []} (cons refl p) = nill
~-weakenˡ {x#xs = q ∷ qs} (cons refl p) = cons (sym q) (~-weakenˡ p)

~-repeat : ∀ x n m → repeat x n ~ repeat x m
~-repeat x zero m = nill
~-repeat x (suc n) zero = nilr
~-repeat x (suc n) (suc m) = cons refl (~-repeat x n m)

~fromAll : ∀ {a xs ys} → All (a ≡_) xs → All (a ≡_) ys → xs ~ ys
~fromAll [] q = nill
~fromAll (refl ∷ p) [] = nilr
~fromAll (refl ∷ p) (refl ∷ q) = cons refl (~fromAll p q)

ne-toAll : {x : A} {xs : FreeRPMon} (x#xs : x # xs) → All (x ≡_) (cons x xs x#xs)
ne-toAll [] = refl ∷ []
ne-toAll {xs = cons _ _ p} (refl ∷ _) = refl ∷ (ne-toAll _)

-- Note that ~ is only transitive when the middle list is nonempty;
-- a~[]~b does not imply a~b.
~-trans-ne : ∀ {xs y ys} {y#ys : y # ys} {zs}
           → xs ~ cons y ys y#ys → cons y ys y#ys ~ zs → xs ~ zs
~-trans-ne nill q = nill
~-trans-ne (cons refl p) nilr = nilr
~-trans-ne (cons refl p) (cons refl q) = ~fromAll (ne-toAll _) (ne-toAll _)

-----------------------------
-- Alternate Compatibility --
-----------------------------

-- We can also define compatibility for the alternate form.
data _~'_ : FreeRPMon' → FreeRPMon' → Set where
  onel : ∀ {xs} → inj₁ tt ~' xs
  oner : ∀ {xs} → xs ~' inj₁ tt
  rep : ∀ {n m x} → inj₂ (x , n) ~' inj₂ (x , m) -- we insist on definitional equality here to hopefully make life easier

from-alt~ : ∀ {xs ys} → xs ~' ys → (from-alt xs) ~ (from-alt ys)
from-alt~ onel = nill
from-alt~ oner = nilr
from-alt~ rep = ~-repeat _ _ _

to-alt~ : ∀ {xs ys} → xs ~ ys → (to-alt xs) ~' (to-alt ys)
to-alt~ nill = onel
to-alt~ nilr = oner
to-alt~ (cons refl p) = rep

-- -- These don't typecheck as is, because the indices don't match. And don't want to use het eq with K... subst hell the only option?
-- to-from-alt~ : ∀ {xs ys} → (p : xs ~' ys) → to-alt~ (from-alt~ p) ≡ p
-- to-from-alt~ = {!!}

-- from-to-alt~ : ∀ {xs ys} → (p : xs ~ ys) → from-alt~ (to-alt~ p) ≡ p
-- from-to-alt~ = {!!}



----------------------------
-- Partial Multiplication --
----------------------------

-- We can concatenate two compatible lists.
∙ : {xs ys : FreeRPMon} → xs ~ ys → FreeRPMon
∙-fresh : {x : A} {xs ys : FreeRPMon} (p : xs ~ ys) → x # xs → x # ys → x # (∙ p)

∙ (nill {x}) = x
∙ (nilr {x}) = x
∙ {cons x xs p} {cons y ys q} (cons refl z) = cons x (cons x (∙ z) (∙-fresh z p q)) (refl ∷ (∙-fresh z p q))

∙-fresh (nill) p q = q
∙-fresh (nilr) p q = p
∙-fresh (cons refl z) (refl ∷ ps) (q ∷ qs) = refl ∷ (refl ∷ ∙-fresh z ps qs)

+-nonzero : (n m : ℕ⁺) → NonZero (proj₁ n + proj₁ m)
+-nonzero (suc n , _) m = record { nonZero = tt }

-- Concatenation is easier too; no freshness wrangling.
∙' : {xs ys : FreeRPMon'} → xs ~' ys → FreeRPMon'
∙' (onel {x}) = x
∙' (oner {x}) = x
∙' (rep {n} {m} {x}) = inj₂ (x , (proj₁ n + proj₁ m) , +-nonzero n m)

----------------------------------------------------
-- Properties of Compatibility and Multiplication --
----------------------------------------------------

∙-assoc'₁ : {x y z : FreeRPMon'} (yz : y ~' z) → x ~' ∙' yz  → x ~' y
∙-assoc'₁ onel p = oner
∙-assoc'₁ oner p = p
∙-assoc'₁ {inj₁ tt} rep p = onel
∙-assoc'₁ {inj₂ _} rep rep = rep

∙-assoc'₂ : {x y z : FreeRPMon'} (p : y ~' z) (q : x ~' ∙' p) → ∙' (∙-assoc'₁ p q) ~' z
∙-assoc'₂ onel q = q
∙-assoc'₂ oner q = oner
∙-assoc'₂ rep onel = rep
∙-assoc'₂ rep rep = rep

ℕ⁺-eq : {m n : ℕ} {pm : NonZero m} {pn : NonZero n} → m ≡ n → (m , pm) ≡ (n , pn)
ℕ⁺-eq {suc m} {pm = record { nonZero = tt }} {record { nonZero = tt }} refl = refl

∙-assoc'-eq : {x y z  : FreeRPMon'} (p : y ~' z) (q : x ~' ∙' p) → ∙' q ≡ ∙' (∙-assoc'₂ p q)
∙-assoc'-eq onel q = refl
∙-assoc'-eq oner q = refl
∙-assoc'-eq rep onel = refl
∙-assoc'-eq {inj₂ (x , m)} {inj₂ (.x , n)} {inj₂ (.x , o)} rep rep = cong (λ z → inj₂ (x , z)) (ℕ⁺-eq (sym $ +-assoc (proj₁ m) (proj₁ n) (proj₁ o)))

-- The theorem is morally proved now, but we have to enter subst hell to actually finish it.
-- Turns out subst'ing in 2D is hard...

to-alt~∙ : {x y z : FreeRPMon} (p : y ~ z) → x ~ ∙ p → to-alt x ~' ∙' (to-alt~ p)
to-alt~∙ nill q = to-alt~ q
to-alt~∙ nilr q = to-alt~ q
to-alt~∙ (cons refl p) nill = onel
to-alt~∙ (cons refl p) (cons refl q) = rep

∙-assoc₁ : {x y z : FreeRPMon} (yz : y ~ z) (p : x ~ ∙ yz) → (x ~ y)
∙-assoc₁ {x} {y} {z} p q = subst₂ _~_ (from-to-alt x) (from-to-alt y) (from-alt~ (∙-assoc'₁ (to-alt~ p) (to-alt~∙ p q)))

subst-nilr : ∀ {x y} → (p : x ≡ y) → subst₂ _~_ p refl (nilr {x}) ≡ nilr {y}
subst-nilr refl = refl

subst-nill : ∀ {x y} → (p : x ≡ y) → subst₂ _~_ refl p (nill {x}) ≡ nill {y}
subst-nill refl = refl

subst-cons : {a : A} {xs ys xs' ys' : FreeRPMon}
           → (a#xs : a # xs) (a#ys : a # ys) (a#xs' : a # xs') (a#ys' : a # ys')
           → (p : xs ≡ xs') (q : ys ≡ ys')
           → (r : xs ~ ys) (r' : xs' ~ ys')
           → subst₂ _~_ (cons-cong {x#xs = a#xs} {y#ys = a#xs'} refl p) (cons-cong {x#xs = a#ys} {y#ys = a#ys'} refl q) (cons refl r) ≡ cons refl r'
subst-cons [] [] [] [] refl refl nill nill = refl
subst-cons [] [] [] [] refl refl nill nilr = {!!}
subst-cons [] [] [] [] refl refl nilr nill = {!!}
subst-cons [] [] [] [] refl refl nilr nilr = {!!}
subst-cons [] (x ∷ a#ys) [] (x₁ ∷ a#ys') refl refl r r' = {!!}
subst-cons (x ∷ a#xs) a#ys a#xs' a#ys' refl refl r r' = {!!}

~-comm-eq : ∀ {xs ys} → (p : xs ~ ys) → ∙ (~-comm p) ≡ ∙ p
~-comm-eq nill = refl
~-comm-eq nilr = refl
~-comm-eq (cons refl p) = cons-cong refl (cons-cong refl (~-comm-eq p))

~-distrib-∙ˡ : ∀ {a x y} → (p : x ~ y) → a ~ (∙ p) → a ~ x
~-distrib-∙ˡ = {!!}

~-distrib-∙ʳ : ∀ {a x y} → (p : x ~ y) → a ~ (∙ p) → a ~ y
~-distrib-∙ʳ = {!!}

rep-len' : ∀ {x xs ys} (x#xs : x # xs) (x#ys : x # ys) (p : xs ~ ys) (q : x # ∙ p) → repeat x (length xs + length ys) ≡ ∙ p
rep-len' [] x#ys nill q = rep-len _ x#ys
rep-len' [] x#ys nilr q = refl
rep-len' {x} {cons _ xs _} (refl ∷ x#xs) x#ys nilr q = cons-cong refl (trans (cong (repeat x) (+-comm (length xs) 0)) (rep-len _ x#xs))
rep-len' {x} {cons _ xs _} {cons _ ys _} (refl ∷ x#xs) (_ ∷ x#ys) (cons refl p) (_ ∷ (_ ∷ q))
  = cons-cong refl (trans (cong (repeat x) (+-comm (length xs) (suc $ length ys))) (cons-cong refl (trans (rep-len' x#ys x#xs (~-comm p) (subst (x #_) (sym $ ~-comm-eq p) q)) (~-comm-eq p))))

rep-len₂ : ∀ {x xs ys} (x#xs : x # xs) (x#ys : x # ys) (p : xs ~ ys) (q : x # ∙ p) → repeat x (length xs + suc (length ys)) ≡ cons x (∙ p) q
rep-len₂ {x} {xs} {ys} x#xs x#ys p q
  = trans (cong (repeat x) (+-comm (length xs) (suc $ length ys))) (cons-cong refl (trans (rep-len' x#ys x#xs (~-comm p) (subst (x #_) (sym $ ~-comm-eq p) q)) (~-comm-eq p)))

∙-assoc₂ : {x y z : FreeRPMon} (p : y ~ z) (q : x ~ ∙ p) → ∙ (∙-assoc₁ p q) ~ z
∙-assoc₂ {x} {y} {z} p q = subst₂ _~_ (lem p q) (from-to-alt z) (from-alt~ (∙-assoc'₂ (to-alt~ p) (to-alt~∙ p q))) where
  lem : {x y z : FreeRPMon} (p : y ~ z) (q : x ~ ∙ p)
      → from-alt (∙' (∙-assoc'₁ (to-alt~ p) (to-alt~∙ p q))) ≡ ∙ (∙-assoc₁ p q)
  lem nill nill = refl
  lem {x} nill nilr = trans (from-to-alt x) (cong ∙ (sym $ subst-nilr (from-to-alt x)))
  lem {cons x xs x#xs} nill (cons refl q) = trans (cons-cong refl (rep-len xs x#xs)) $ cong ∙ (sym $ subst-nilr (cons-cong refl (rep-len xs x#xs)))
  lem {y = y} nilr nill = trans (from-to-alt y) (cong ∙ (sym $ subst-nill (from-to-alt y)))
  lem {x} nilr nilr = trans (from-to-alt x) (cong ∙ (sym $ subst-nilr (from-to-alt x)))
  lem {cons x xs x#xs} {cons .x ys x#ys} nilr (cons refl q) = trans (cons-cong {y#ys = refl ∷ ∙-fresh q x#xs x#ys} refl (rep-len₂ x#xs x#ys q (∙-fresh q x#xs x#ys))) {!!}
  lem {[]} {cons y ys y#ys} {cons .y zs y#zs} (cons refl p) nill = trans (cons-cong refl (rep-len ys y#ys)) (cong ∙ (sym $ subst-nill (cons-cong refl (rep-len ys y#ys))))
  lem {cons x xs x#xs} {cons .x ys x#ys} {cons .x zs x#zs} (cons refl p) (cons refl q)
    = trans {!!} (cong ∙ $ sym $ subst-cons {!!} {!!} x#xs x#ys (rep-len xs x#xs) (rep-len ys x#ys) (~-repeat x (length xs) (length ys)) (~-distrib-∙ˡ p (~-weakenʳ q)))

∙-assoc : {x y z : FreeRPMon} (yz : y ~ z) (p : x ~ ∙ yz)
             → Σ[ xy ∈ (x ~ y) ] Σ[ q ∈ (∙ xy ~ z) ] (∙ p ≡ ∙ q)
∙-assoc p q = ∙-assoc₁ p q , ∙-assoc₂ p q , {!!}

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
