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

-- We can also define compatibility for the alternate form.
data _~'_ : FreeRPMon' → FreeRPMon' → Set where
  oneb : inj₁ tt ~' inj₁ tt
  onel : ∀ {p} → inj₁ tt ~' inj₂ p
  oner : ∀ {p} → inj₂ p ~' inj₁ tt
  rep : ∀ {n m x y} → x ≡ y → inj₂ (x , n) ~' inj₂ (y , m)

+-nonzero : (n m : ℕ⁺) → NonZero (proj₁ n + proj₁ m)
+-nonzero (suc n , _) m = record { nonZero = tt }

-- Concatenation is easier for the alternate presentation; no freshness wrangling.
∙' : {xs ys : FreeRPMon'} → xs ~' ys → FreeRPMon'
∙' oneb = inj₁ tt
∙' (onel {x}) = inj₂ x
∙' (oner {x}) = inj₂ x
∙' (rep {n} {m} {x} refl) = inj₂ (x , (proj₁ n + proj₁ m) , +-nonzero n m)

~'-compatˡ-[] : ∀ {xs} → (inj₁ tt) ~' xs
~'-compatˡ-[] {a} = ?

~'-compatʳ-[] : ∀ {xs} → xs ~' (inj₁ tt)
~'-compatʳ-[] {a} = ?

~'-reflexive : Reflexive _~'_
~'-reflexive {a} = ?

~'-sym : Symmetric _~'_
~'-sym = ?

∙'-assoc₁ : {x y z : FreeRPMon'} (yz : y ~' z) → x ~' ∙' yz  → x ~' y
∙'-assoc₁ oneb p = p
∙'-assoc₁ {inj₁ tt} onel p = oneb
∙'-assoc₁ {inj₂ _} onel p = oner
∙'-assoc₁ oner p = p
∙'-assoc₁ {inj₁ tt} rep p = onel
∙'-assoc₁ {inj₂ _} rep rep = rep

∙'-assoc₂ : {x y z : FreeRPMon'} (p : y ~' z) (q : x ~' ∙' p) → ∙' (∙'-assoc₁ p q) ~' z
∙'-assoc₂ oneb oneb = oneb
∙'-assoc₂ oneb oner = oner
∙'-assoc₂ onel onel = onel
∙'-assoc₂ onel rep = rep
∙'-assoc₂ oner onel = oner
∙'-assoc₂ oner rep = oner
∙'-assoc₂ rep onel = rep
∙'-assoc₂ rep rep = rep

ℕ⁺-eq : {m n : ℕ} {pm : NonZero m} {pn : NonZero n} → m ≡ n → (m , pm) ≡ (n , pn)
ℕ⁺-eq {suc m} {pm = record { nonZero = tt }} {record { nonZero = tt }} refl = refl

∙'-assoc-eq : {x y z  : FreeRPMon'} (p : y ~' z) (q : x ~' ∙' p) → ∙' q ≡ ∙' (∙'-assoc₂ p q)
∙'-assoc-eq oneb oneb = refl
∙'-assoc-eq oneb oner = refl
∙'-assoc-eq onel onel = refl
∙'-assoc-eq onel rep = refl
∙'-assoc-eq oner onel = refl
∙'-assoc-eq oner rep = refl
∙'-assoc-eq rep onel = refl
∙'-assoc-eq {inj₂ (x , m)} {inj₂ (.x , n)} {inj₂ (.x , o)} rep rep = cong (λ z → inj₂ (x , z)) (ℕ⁺-eq (sym $ +-assoc (proj₁ m) (proj₁ n) (proj₁ o)))

∙'-identityˡ : ∀ {x} → ∙' {[]} {x} ~'-compatˡ-[] ≡ x
∙'-identityˡ {a} = ?

∙'-identityʳ : ∀ {x} → ∙' {x} {[]} ~'-compatʳ-[] ≡ x
∙'-identityʳ {a} = ?

∙'-assoc : ?
∙'-assoc = ?

isPartialMonoid' : IsPartialMonoid {A = FreeRPMon'} _≡_ _~'_ ∙' []
IsPartialMonoid.isEquivalence isPartialMonoid' = isEquivalence
IsPartialMonoid.ε-compatˡ isPartialMonoid' = ~'-compatˡ-[]
IsPartialMonoid.ε-compatʳ isPartialMonoid' = ~'-compatʳ-[]
IsPartialMonoid.identityˡ isPartialMonoid' = ∙'-identityˡ
IsPartialMonoid.identityʳ isPartialMonoid' = ∙'-identityʳ
IsPartialMonoid.assoc isPartialMonoid' = ∙'-assoc

isReflexivePartialMonoid' : IsReflexivePartialMonoid {A = FreeRPMon'} _≡_ _~'_ ∙' []
IsReflexivePartialMonoid.isPMon isReflexivePartialMonoid' = isPartialMonoid'
IsReflexivePartialMonoid.refl isReflexivePartialMonoid' = ~'-reflexive

{-

-- Because we may only concatenate lists which contain copies of the same element,
-- we define the domain of concatenation to be a compatibility relation which encodes
-- this invarient.

-- Compatibility: two lists are compatible if they contain
-- (potentially different numbers of copies of) the same element
data _~_ : FreeRPMon → FreeRPMon → Set where
  nilb : [] ~ [] -- note: the first 3 constructors are mutually exclusive so that we don't have multiple representations of []~[]
  nill : ∀ {x xs x#xs} → [] ~ cons x xs x#xs
  nilr : ∀ {x xs x#xs} → cons x xs x#xs ~ []
  cons : ∀ {x y xs ys} {p : x # xs} {q : y # ys} → x ≡ y → cons x xs p ~ cons y ys q


~-weakenʳ : ∀ {y xs ys} {y#ys : y # ys} → xs ~ cons y ys y#ys → xs ~ ys
~-weakenʳ {y#ys = []} nill = nilb
~-weakenʳ {y#ys = []} (cons _) = nilr
~-weakenʳ {y#ys = p ∷ ps} nill = nill
~-weakenʳ {y#ys = p ∷ ps} (cons q) = cons (trans q p)

~-weakenˡ : ∀ {x xs ys} {x#xs : x # xs} → cons x xs x#xs ~ ys → xs ~ ys
~-weakenˡ {x#xs = []} nilr = nilb
~-weakenˡ {x#xs = []} (cons _) = nill
~-weakenˡ {x#xs = p ∷ ps} nilr = nilr
~-weakenˡ {x#xs = p ∷ ps} (cons q) = cons (trans (sym p) q)

~-weaken : ∀ {x y xs ys x#xs y#ys} → cons x xs x#xs ~ cons y ys y#ys → xs ~ ys
~-weaken {x#xs = []} {[]} (cons _) = nilb
~-weaken {x#xs = []} {_ ∷ _} (cons _) = nill
~-weaken {x#xs = _ ∷ _} {[]} (cons _) = nilr
~-weaken {x#xs = p ∷ _} {q ∷ _} (cons r) = cons (trans (sym p) (trans r q))

~-repeat : ∀ x n m → repeat x n ~ repeat x m
~-repeat x zero zero = nilb
~-repeat x zero (suc m) = nill
~-repeat x (suc n) zero = nilr
~-repeat x (suc n) (suc m) = cons refl

~fromAll : ∀ {a xs ys} → All (a ≡_) xs → All (a ≡_) ys → xs ~ ys
~fromAll [] [] = nilb
~fromAll [] (q ∷ qs) = nill
~fromAll (p ∷ ps) [] = nilr
~fromAll (p ∷ ps) (q ∷ qs) = cons (trans (sym p) q)

ne-toAll : {x : A} {xs : FreeRPMon} (x#xs : x # xs) → All (x ≡_) (cons x xs x#xs)
ne-toAll [] = refl ∷ []
ne-toAll {xs = cons _ _ p} (refl ∷ _) = refl ∷ (ne-toAll _)

-- Note that ~ is only transitive when the middle list is nonempty;
-- a~[]~b does not imply a~b.
~-trans-ne : ∀ {xs y ys} {y#ys : y # ys} {zs}
           → xs ~ cons y ys y#ys → cons y ys y#ys ~ zs → xs ~ zs
~-trans-ne nill nilr = nilb
~-trans-ne nill (cons _) = nill
~-trans-ne (cons _) nilr = nilr
~-trans-ne (cons p) (cons q) = cons (trans p q)

-----------------------------
-- Alternate Compatibility --
-----------------------------

-- We can also define compatibility for the alternate form.
data _~'_ : FreeRPMon' → FreeRPMon' → Set where
  oneb : inj₁ tt ~' inj₁ tt
  onel : ∀ {p} → inj₁ tt ~' inj₂ p
  oner : ∀ {p} → inj₂ p ~' inj₁ tt
  rep : ∀ {n m x} → inj₂ (x , n) ~' inj₂ (x , m) -- we insist on definitional equality here to hopefully make life easier

from-alt~ : ∀ {xs ys} → xs ~' ys → (from-alt xs) ~ (from-alt ys)
from-alt~ oneb = nilb
from-alt~ {ys = inj₂ (x , suc n , pn)} onel = nill
from-alt~ {xs = inj₂ (x , suc n , pn)} oner = nilr
from-alt~ rep = ~-repeat _ _ _

to-alt~ : ∀ {xs ys} → xs ~ ys → (to-alt xs) ~' (to-alt ys)
to-alt~ nilb = oneb
to-alt~ nill = onel
to-alt~ nilr = oner
to-alt~ (cons refl) = rep

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

∙ nilb = []
∙ (nill {x} {xs} {x#xs}) = cons x xs x#xs
∙ (nilr {x} {xs} {x#xs}) = cons x xs x#xs
∙ u@(cons {x} {p = p} {q} refl) = cons x (cons x (∙ $ ~-weaken u) (∙-fresh (~-weaken u) p q)) (refl ∷ ∙-fresh (~-weaken u) p q)

∙-fresh nilb p q = []
∙-fresh nill p q = q
∙-fresh nilr p q = p
∙-fresh u@(cons refl) (p ∷ ps) (_ ∷ qs) = p ∷ (p ∷ ∙-fresh (~-weaken u) ps qs)



----------------------------------------------------
-- Properties of Compatibility and Multiplication --
----------------------------------------------------


-- The theorem is morally proved now, but we have to enter subst hell to actually finish it.
-- Turns out subst'ing in 2D is hard...

to-alt~∙ : {x y z : FreeRPMon} (p : y ~ z) → x ~ ∙ p → to-alt x ~' ∙' (to-alt~ p)
to-alt~∙ nilb nilb = oneb
to-alt~∙ nilb nilr = oner
to-alt~∙ nill nill = onel
to-alt~∙ nill (cons refl) = rep
to-alt~∙ nilr nill = onel
to-alt~∙ nilr (cons refl) = rep
to-alt~∙ (cons refl) nill = onel
to-alt~∙ (cons refl) (cons refl) = rep

silver-bullet : {P : FreeRPMon → FreeRPMon → Set} {x y : FreeRPMon}
              → (P x y → (to-alt x) ~' (to-alt y))
              → (P x y → x ~ y)
silver-bullet {P} {x} {y} f p = subst₂ _~_ (from-to-alt x) (from-to-alt y) (from-alt~ $ f p)

∙-assoc₁ : {x y z : FreeRPMon} (yz : y ~ z) (p : x ~ ∙ yz) → (x ~ y)
∙-assoc₁ {x} {y} {z} p q = {!!}

{-
subst-nilr : ∀ {x y xs ys x#xs y#ys} → (p : cons x xs x#xs ≡ cons y ys y#ys)  → subst₂ _~_ p refl (nilr {x} {xs} {x#xs}) ≡ nilr {y} {ys} {y#ys}
subst-nilr refl = refl

subst-nill : ∀ {x y xs ys x#xs y#ys} → (p : cons x xs x#xs ≡ cons y ys y#ys) → subst₂ _~_ refl p (nill {x} {xs} {x#xs}) ≡ nill {y} {ys} {y#ys}
subst-nill refl = refl

subst-cons : {a : A} {xs ys xs' ys' : FreeRPMon}
           → (a#xs : a # xs) (a#ys : a # ys) (a#xs' : a # xs') (a#ys' : a # ys')
           → (p : xs ≡ xs') (q : ys ≡ ys')
           → (r : xs ~ ys) (r' : xs' ~ ys')
           → subst₂ _~_ (cons-cong {x#xs = a#xs} {y#ys = a#xs'} refl p) (cons-cong {x#xs = a#ys} {y#ys = a#ys'} refl q) (cons refl) ≡ cons refl
subst-cons [] [] [] [] refl refl nilb nilb = refl
subst-cons [] (refl ∷ ps) [] (q ∷ qs) refl refl nill nill = {!!}
subst-cons (p ∷ ps) [] (q ∷ qs) [] refl refl nilr nilr = {!!}
subst-cons (p ∷ ps) (q ∷ qs) (r ∷ rs) (s ∷ ss) refl refl (cons u) (cons v) = {!!}
-}

∙-comm : ∀ {xs ys} → (p : xs ~ ys) → ∙ (~-sym p) ≡ ∙ p
∙-comm nilb = refl
∙-comm nill = refl
∙-comm nilr = refl
∙-comm u@(cons {x} {.x} {xs} {ys} {p} {q} refl) = cons-cong refl $ cons-cong refl (trans (cong ∙ (lem p q)) (∙-comm $ (~-weaken u))) where
  lem : ∀ {x xs ys} p q
      → (~-weaken {x} {x} {ys} {xs} {q} {p} (cons {x} {x} {ys} {xs} {q} {p} refl))
      ≡ (~-sym {xs} {ys} (~-weaken {x} {x} {xs} {ys} {p} {q} (cons {x} {x} {xs} {ys} {p} {q} refl)))
  lem [] [] = refl
  lem [] (_ ∷ _) = refl
  lem (_ ∷ _) [] = refl
  lem (refl ∷ _) (refl ∷ _) = refl

~-distrib-∙ˡ : ∀ {a x y} → (p : x ~ y) → a ~ (∙ p) → a ~ x
~-distrib-∙ˡ nilb q = q
~-distrib-∙ˡ {[]} nill q = nilb
~-distrib-∙ˡ {cons x a x#xs} nill q = nilr
~-distrib-∙ˡ nilr q = q
~-distrib-∙ˡ (cons refl) nill = nill
~-distrib-∙ˡ (cons refl) (cons p) = cons p

~-distrib-∙ʳ : ∀ {a x y} → (p : x ~ y) → a ~ (∙ p) → a ~ y
~-distrib-∙ʳ nilb q = q
~-distrib-∙ʳ nill q = q
~-distrib-∙ʳ {[]} nilr q = nilb
~-distrib-∙ʳ {cons x a x#xs} nilr q = nilr
~-distrib-∙ʳ (cons refl) nill = nill
~-distrib-∙ʳ (cons refl) (cons q) = cons q

rep-len' : ∀ {a xs ys} (a#xs : a # xs) (a#ys : a # ys) (p : xs ~ ys) (q : a # ∙ p) → repeat a (length xs + length ys) ≡ ∙ p
rep-len' [] q nilb _ = rep-len _ q
rep-len' [] (q ∷ qs) nill _ = cons-cong q (rep-len _ qs)
rep-len' {a} {cons x xs x#xs} (p ∷ ps) q nilr v = cons-cong p (trans (cong (repeat a) (+-identityʳ (length xs))) (rep-len _ ps))
rep-len' {x} {cons _ xs _} {cons _ ys _} (_ ∷ x#xs) (_ ∷ x#ys) u@(cons refl) (refl ∷ (_ ∷ q))
  = cons-cong refl (trans (cong (repeat x) (+-comm (length xs) (suc $ length ys))) (cons-cong refl (trans (rep-len' x#ys x#xs (~-sym $ ~-weaken u) (subst (x #_) (sym $ ∙-comm $ ~-weaken u) q)) (∙-comm $ ~-weaken u))))

rep-len₂ : ∀ {x xs ys} (x#xs : x # xs) (x#ys : x # ys) (p : xs ~ ys) (q : x # ∙ p) → repeat x (length xs + suc (length ys)) ≡ cons x (∙ p) q
rep-len₂ {x} {xs} {ys} x#xs x#ys p q
  = trans (cong (repeat x) (+-comm (length xs) (suc $ length ys))) (cons-cong refl (trans (rep-len' x#ys x#xs (~-sym p) (subst (x #_) (sym $ ∙-comm p) q)) (∙-comm p)))


-- todo: this might be easier to do directly now than with subst?
∙-assoc₂ : {x y z : FreeRPMon} (p : y ~ z) (q : x ~ ∙ p) → ∙ (∙-assoc₁ p q) ~ z
∙-assoc₂ {x} {y} {z} p q = {!!}

-- subst₂ _~_ (lem p q) (from-to-alt z) (from-alt~ (∙-assoc'₂ (to-alt~ p) (to-alt~∙ p q))) where
--   lem : {x y z : FreeRPMon} (p : y ~ z) (q : x ~ ∙ p)
--       → from-alt (∙' (∙-assoc'₁ (to-alt~ p) (to-alt~∙ p q))) ≡ ∙ (∙-assoc₁ p q)
--   lem nilb nilb = refl
--   lem {x} nilb nilr = trans (from-to-alt x) (cong ∙ (sym $ subst-nilr (from-to-alt x)))
--   lem nill nill = refl
--   lem {cons x xs x#xs} nill (cons refl) = trans (cons-cong refl (rep-len xs x#xs)) $ cong ∙ (sym $ subst-nilr (cons-cong refl (rep-len xs x#xs)))
--   lem {y = y} nilr nill = trans (from-to-alt y) (cong ∙ (sym $ subst-nill (from-to-alt y)))
--   lem {cons x xs x#xs} {cons .x ys x#ys} nilr u@(cons refl) =
--     begin
--       cons x (repeat x (length xs + suc (length ys))) (repeat-equal x (length xs + suc (length ys)))
--     ≡⟨ (cons-cong {y#ys = refl ∷ ∙-fresh (~-weaken u) x#xs x#ys} refl (rep-len₂ x#xs x#ys (~-weaken u) (∙-fresh (~-weaken u) x#xs x#ys))) ⟩
--       cons x (cons x (∙ (~-weaken (cons refl))) (∙-fresh (~-weaken (cons refl)) x#xs x#ys)) (refl ∷ ∙-fresh (~-weaken (cons refl)) x#xs x#ys)
--     ≡⟨ {!cong ∙ !} ⟩
--       ∙ (subst₂ _~_ (WithIrr.cons-cong _≡_ A-set refl (rep-len xs x#xs)) (WithIrr.cons-cong _≡_ A-set refl (rep-len ys x#ys)) (cons refl))
--     ∎ where open ≡-Reasoning
--   lem {[]} {cons y ys y#ys} {cons .y zs y#zs} (cons refl) nill = trans (cons-cong refl (rep-len ys y#ys)) (cong ∙ (sym $ subst-nill (cons-cong refl (rep-len ys y#ys))))
--   lem {cons x xs x#xs} {cons .x ys x#ys} {cons .x zs x#zs} (cons refl) (cons refl) = {!!}

  -- lem nill nill = refl
  -- lem {x} nill nilr = trans (from-to-alt x) (cong ∙ (sym $ subst-nilr (from-to-alt x)))
  -- lem {cons x xs x#xs} nill (cons refl q) = trans (cons-cong refl (rep-len xs x#xs)) $ cong ∙ (sym $ subst-nilr (cons-cong refl (rep-len xs x#xs)))
  -- lem {y = y} nilr nill = trans (from-to-alt y) (cong ∙ (sym $ subst-nill (from-to-alt y)))
  -- lem {x} nilr nilr = trans (from-to-alt x) (cong ∙ (sym $ subst-nilr (from-to-alt x)))
  -- lem {cons x xs x#xs} {cons .x ys x#ys} nilr (cons refl q) = trans (cons-cong {y#ys = refl ∷ ∙-fresh q x#xs x#ys} refl (rep-len₂ x#xs x#ys q (∙-fresh q x#xs x#ys))) {!!}
  -- lem {[]} {cons y ys y#ys} {cons .y zs y#zs} (cons refl p) nill = trans (cons-cong refl (rep-len ys y#ys)) (cong ∙ (sym $ subst-nill (cons-cong refl (rep-len ys y#ys))))
  -- lem {cons x xs x#xs} {cons .x ys x#ys} {cons .x zs x#zs} (cons refl p) (cons refl q)
  --   = trans {!!} (cong ∙ $ sym $ subst-cons {!!} {!!} x#xs x#ys (rep-len xs x#xs) (rep-len ys x#ys) (~-repeat x (length xs) (length ys)) (~-distrib-∙ˡ p (~-weakenʳ q)))

∙-assoc : {x y z : FreeRPMon} (yz : y ~ z) (p : x ~ ∙ yz)
             → Σ[ xy ∈ (x ~ y) ] Σ[ q ∈ (∙ xy ~ z) ] (∙ p ≡ ∙ q)
∙-assoc p q = ∙-assoc₁ p q , ∙-assoc₂ p q , {!!}


isPartialMonoid : IsPartialMonoid {A = FreeRPMon} _≡_ _~_ ∙ []
IsPartialMonoid.isEquivalence isPartialMonoid = isEquivalence
IsPartialMonoid.ε-compatˡ isPartialMonoid = ~-compatˡ-[]
IsPartialMonoid.ε-compatʳ isPartialMonoid = ~-compatʳ-[]
IsPartialMonoid.identityˡ isPartialMonoid = ∙-identityˡ
IsPartialMonoid.identityʳ isPartialMonoid = ∙-identityʳ
IsPartialMonoid.assoc isPartialMonoid = ∙-assoc

isReflexivePartialMonoid : IsReflexivePartialMonoid {A = FreeRPMon} _≡_ _~_ ∙ []
IsReflexivePartialMonoid.isPMon isReflexivePartialMonoid = isPartialMonoid
IsReflexivePartialMonoid.refl isReflexivePartialMonoid = ~-reflexive

-}
