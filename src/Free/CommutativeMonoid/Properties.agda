open import Algebra.Structure.OICM
open import Relation.Binary.PropositionalEquality

module Free.CommutativeMonoid.Properties
  {X : Set} {_≤_ : X → X → Set}
  (≤-PDTO : IsPropDecTotalOrder _≡_ _≤_)
  where

open import Data.Empty
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s) renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (1+n≢n; 1+n≢0; +-identityʳ; m≤m+n; +-suc; suc-injective; +-assoc; +-comm) renaming (≤-step to ≤ℕ-step; ≤-refl to ≤ℕ-refl; ≤-trans to ≤ℕ-trans; ≤-reflexive to ≤ℕ-reflexive)
open import Data.Nat.Induction
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Sum
open import Data.Product
open import Algebra
open import Function
open import Induction.WellFounded

open import Relation.Binary hiding (Irrelevant)
open import Relation.Binary.Isomorphism
open _≃_
open import Relation.Nullary
open import Axiom.UniquenessOfIdentityProofs

open import Data.FreshList.InductiveInductive
open import Free.CommutativeMonoid.Base ≤-PDTO


private
  ≤-prop = IsPropDecTotalOrder.≤-prop ≤-PDTO
  _≟_ = IsPropDecTotalOrder._≟_ ≤-PDTO
  total = IsPropDecTotalOrder.total ≤-PDTO
  ≤-refl = IsPropDecTotalOrder.refl ≤-PDTO
  ≤-trans = IsPropDecTotalOrder.trans ≤-PDTO
  ≤-antisym = IsPropDecTotalOrder.antisym ≤-PDTO
  ≤-resp-≡ = IsPropDecTotalOrder.≤-resp-≈ ≤-PDTO
  ≡-isEq = IsPropDecTotalOrder.isEquivalence ≤-PDTO
  ≈-refl = λ {x} → IsPropDecTotalOrder.Eq.reflexive ≤-PDTO {x = x} refl


open Data.FreshList.InductiveInductive.WithIrr _≤_ ≤-prop
open Data.FreshList.InductiveInductive.WithEq _≤_ ≡-isEq ≤-resp-≡

≡-prop : {x y : X} → Irrelevant (x ≡ y)
≡-prop = Axiom.UniquenessOfIdentityProofs.Decidable⇒UIP.≡-irrelevant _≟_

there-inj : {a x : X} {xs : SortedList} {x#xs : x # xs} {p q : a ∈ xs} → there {x = x} {xs} {x#xs} p ≡ there q → p ≡ q
there-inj refl = refl

peel-∈-iso-fun' : {b : X} {xs ys : SortedList} {b#xs : b # xs} {b#ys : b # ys}
               → (iso : ∀ a → (a ∈ cons b xs b#xs) ≃ (a ∈ cons b ys b#ys))
               → (a : X)
               → (p : a ∈ xs)
               → (to-there : a ∈ cons b ys b#ys)
               → to-there ≡ to (iso a) (there p)
               → a ∈ ys
peel-∈-iso-fun' {b} iso a p (here a=b) eq with to (iso a) (here a=b) | inspect (to $ iso a) (here a=b)
... | here a=b' | [ eq' ] = ⊥-elim (here≢there (sym $ to-inj (iso a) (trans (sym eq) (sym (trans eq' (cong here (≡-prop a=b' a=b)))))))
... | there u | _ = u
peel-∈-iso-fun' {b} iso a p (there a∈ys) eq = a∈ys

peel-∈-iso-fun : {b : X} {xs ys : SortedList} {b#xs : b # xs} {b#ys : b # ys}
               → (∀ a → (a ∈ cons b xs b#xs) ≃ (a ∈ cons b ys b#ys))
               → (∀ a → a ∈ xs → a ∈ ys)
peel-∈-iso-fun iso a p = peel-∈-iso-fun' iso a p (to (iso a) (there p)) refl

from-to-peel' : {b : X} {xs ys : SortedList} {b#xs : b # xs} {b#ys : b # ys}
              → (iso : ∀ a → (a ∈ cons b xs b#xs) ≃ (a ∈ cons b ys b#ys))
              → (a : X)
              → (p : a ∈ xs)
              → (to-there : a ∈ cons b ys b#ys)
              → (eq : to-there ≡ to (iso a) (there p))
              → (from-there : a ∈ cons b xs b#xs)
              → (eq' : from-there ≡ to (≃-sym (iso a)) (there (peel-∈-iso-fun' iso a p to-there eq)))
              → p ≡ peel-∈-iso-fun' (λ x → ≃-sym (iso x)) a (peel-∈-iso-fun' iso a p to-there eq) from-there eq'
from-to-peel' iso a p (here refl) eq from-there eq' with to (iso a) (here refl) | inspect (to (iso a)) (here refl)
... | here a=a | [ v ] = ⊥-elim (here≢there (sym (to-inj (iso a) (trans (sym eq) (sym (trans v (cong here (≡-prop a=a refl))))))))
from-to-peel' iso a p (here refl) eq (there q)   eq' | there u | [ v ] = ⊥-elim (here≢there (trans (from-to (iso a) (here refl)) (sym (subst (λ z → there q ≡ from (iso a) z) (sym v) eq'))))
from-to-peel' iso a p (here refl) eq (here a=a) eq' | there u | [ v ] with from (iso a) (here a=a) | inspect (from (iso a)) (here a=a)
... | here a=a' | [ w ] = ⊥-elim (here≢there (sym (to-inj (≃-sym (iso a)) (trans (sym eq') (sym (trans w (cong here (≡-prop a=a' a=a ))))))))
... | there f   | [ w ] = there-inj (trans (trans (from-to (iso a) (there p)) (sym $ cong (from $ iso a) eq)) (trans (cong (λ z → from (iso a) (here z)) (≡-prop refl a=a)) w))
from-to-peel' iso a p (there a∈ys) eq .(to (≃-sym (iso a)) (there (peel-∈-iso-fun' iso a p (there a∈ys) eq))) refl
  = subst (λ z → ∀ q → p ≡ peel-∈-iso-fun' (λ x → ≃-sym (iso x)) a a∈ys (from (iso a) z) q)
          (sym eq)
          (λ q → subst (λ z → ∀ q' → p ≡ peel-∈-iso-fun' (λ x → ≃-sym (iso x)) a a∈ys z q')
                       (from-to (iso a) (there p))
                       (λ _ → refl)
                       q)
          refl

from-to-peel : {b : X} {xs ys : SortedList} {b#xs : b # xs} {b#ys : b # ys}
             → (iso : ∀ a → (a ∈ cons b xs b#xs) ≃ (a ∈ cons b ys b#ys))
             → (a : X)
             → (p : a ∈ xs)
             → p ≡ peel-∈-iso-fun (λ x → ≃-sym (iso x)) a (peel-∈-iso-fun iso a p)
from-to-peel iso a p = from-to-peel' iso a p _ refl _ refl

peel-∈-iso : {b : X} {xs ys : SortedList} {b#xs : b # xs} {b#ys : b # ys}
             → (∀ a → (a ∈ cons b xs b#xs) ≃ (a ∈ cons b ys b#ys))
             → (∀ a → (a ∈ xs) ≃ (a ∈ ys))
to (peel-∈-iso {b} iso a) = peel-∈-iso-fun iso a
from (peel-∈-iso iso a) = peel-∈-iso-fun (≃-sym ∘ iso) a
from-to (peel-∈-iso iso a) a∈xs = from-to-peel iso a a∈xs
to-from (peel-∈-iso iso a) a∈xs = from-to-peel (≃-sym ∘ iso) a a∈xs

-- If two sorted lists have isomorphic membership relations, then they are the same list.
extensionality : (xs ys : SortedList)
               → (∀ a → (a ∈ xs) ≃ (a ∈ ys))
               → xs ≡ ys
extensionality [] [] iso = refl
extensionality [] (cons y ys y#ys) iso = ⊥-elim $ ¬any[] $ from (iso y) (here refl)
extensionality (cons x xs x#xs) [] iso = ⊥-elim $ ¬any[] $ to (iso x) (here refl)
extensionality (cons x xs x#xs) (cons y ys y#ys) iso = cons-cong x≡y xs≡ys where
  x≡y : x ≡ y
  x≡y with to (iso x) (here refl)
  ... | here x≡y = x≡y
  ... | there x∈ys with from (iso y) (here refl)
  ... | here y≡x = sym y≡x
  ... | there y∈xs = ≤-antisym (#-trans' x#xs y∈xs) (#-trans' y#ys x∈ys) -- x≤a for all a∈xs. y∈xs, so x≤y. y≤a for all a∈ys. x∈ys, so y≤x. so x≡y.
  -- Antisymmetry of R is used here to make the definition easier, but I think this should be possible for all fresh lists.

  xs≡ys : xs ≡ ys
  xs≡ys with x≡y
  ... | refl = extensionality xs ys (peel-∈-iso {x} iso)

cons-∈-iso : {b : X} {xs ys : SortedList} {b#xs : b # xs} {b#ys : b # ys}
           → (∀ a → (a ∈ xs) ≃ (a ∈ ys))
           → (∀ a → (a ∈ cons b xs b#xs) ≃ (a ∈ cons b ys b#ys))
to (cons-∈-iso iso a) (here p) = here p
to (cons-∈-iso iso a) (there a∈xs) = there (to (iso a) a∈xs)
from (cons-∈-iso iso a) (here p) = here p
from (cons-∈-iso iso a) (there a∈ys) = there (from (iso a) a∈ys)
from-to (cons-∈-iso iso a) (here x) = refl
from-to (cons-∈-iso iso a) (there p) = cong there (from-to (iso a) p)
to-from (cons-∈-iso iso a) (here x) = refl
to-from (cons-∈-iso iso a) (there p) = cong there (to-from (iso a) p)

-----------------------
-- Counting Elements --
-----------------------


count : SortedList → (X → ℕ)
count [] x = zero
count (cons y ys y#ys) x = if   (does $ x ≟ y)
                           then (suc $ count ys x)
                           else (count ys x)

count-lem1 : {x y : X} {ys : SortedList} → x ≤ y → x ≢ y → y # ys → x ∉ ys
count-lem1 {x} {y} {cons .x zs z#zs} x≤y x≢y (y≤x ∷ y#ys) (here refl)  = x≢y $ ≤-antisym x≤y y≤x
count-lem1 {x} {y} {cons  z zs z#zs} x≤y x≢y (y≤z ∷ y#ys) (there x∈ys) = count-lem1 {x} {y} {zs} x≤y x≢y y#ys x∈ys

count-lem2 : {a : X} {xs : SortedList} → a ∉ xs → count xs a ≡ zero
count-lem2 {a} {[]} a∉xs = refl
count-lem2 {a} {cons x xs x#xs} a∉xs with a ≟ x
... | yes refl = ⊥-elim (a∉xs (here refl))
... | no  _ = count-lem2 {a} {xs} (∉-weaken a∉xs)

count-lem : {x y : X} {ys : SortedList} → x ≤ y → x ≢ y → y # ys → count ys x ≡ zero
count-lem p q r = count-lem2 $ count-lem1 p q r

wc-≗-lt : {x y : X} {xs ys : SortedList} (x#xs : x # xs) (y#ys : y # ys)
        → x ≢ y → x ≤ y
        → count (cons x xs x#xs) ≗ count (cons y ys y#ys)
        → count xs ≗ count ys
wc-≗-lt {x} {y} {xs} {ys} x#xs y#ys x≢y x≤y eq a with a ≟ x | a ≟ y | eq a
... | yes refl | yes refl | p = ⊥-elim (x≢y refl)
... | no _     | no _     | p = p
... | yes refl | no a≠y   | p = ⊥-elim $ 1+n≢0 $ trans p (count-lem x≤y x≢y y#ys)
... | no _     | yes refl | p with x ≟ x | x ≟ y | eq x
... | no ¬refl | _        | _ = ⊥-elim (¬refl refl)
... | yes x=x | yes refl | _ = ⊥-elim (x≢y refl)
... | yes x=x | no _     | q = ⊥-elim $ 1+n≢0 $ trans q (count-lem x≤y x≢y y#ys)

wc-≗-eq : {a : X} {xs ys : SortedList} (a#xs : a # xs) (a#ys : a # ys)
        → count (cons a xs a#xs) ≗ count (cons a ys a#ys)
        → count xs ≗ count ys
wc-≗-eq {x} {xs} {ys} a#xs a#ys eq a with a ≟ x | a ≟ a | eq a
... | _ | no ¬refl | _ = ⊥-elim (¬refl refl)
... | yes refl | yes x=x | p = suc-injective p
... | no x≢a | yes a=a | p = p

weaken-count-≗ : {x y : X} {xs ys : SortedList} {x#xs : x # xs} {y#ys : y # ys}
               → count (cons x xs x#xs) ≗ count (cons y ys y#ys)
               → count xs ≗ count ys
weaken-count-≗ {x} {y} {xs} {ys} {x#xs} {y#ys} eq a with x ≟ y | total x y
... | yes refl | _ = wc-≗-eq x#xs y#ys eq a
... | no x≠y   | inj₁ x≤y = wc-≗-lt x#xs y#ys x≠y x≤y eq a
... | no x≠y   | inj₂ y≤x = sym $ wc-≗-lt y#ys x#xs (≢-sym x≠y) y≤x (λ s → sym $ eq s) a

eqCount→iso : (xs ys : SortedList)
            → count xs ≗ count ys
            → (∀ a → (a ∈ xs) ≃ (a ∈ ys))
eqCount→iso [] [] eq a = ≃-refl
eqCount→iso [] (cons y ys y#ys) eq a with y ≟ y | eq y
... | yes y=y | ()
... | no ¬refl | _ = ⊥-elim (¬refl refl)
eqCount→iso (cons x xs x#xs) [] eq a with x ≟ x | eq x
... | yes x=x | ()
... | no ¬refl | _ = ⊥-elim (¬refl refl)
eqCount→iso (cons x xs x#xs) (cons y ys y#ys) eq a with x ≟ y | x ≟ x | eq x
... | yes refl | _ | _ = cons-∈-iso {x} {xs} {ys} {x#xs} {y#ys} (eqCount→iso xs ys (weaken-count-≗ {x#xs = x#xs} {y#ys = y#ys} eq)) a
... | no x≠y | no ¬refl | _ = ⊥-elim (¬refl refl)
... | no x≠y | yes x=x | p = ⊥-elim $ 1+n≢n $ trans p (sym $ weaken-count-≗ {x#xs = x#xs} {y#ys = y#ys} eq x)

eqCount→eq : {xs ys : SortedList}
           → count xs ≗ count ys
           → xs ≡ ys
eqCount→eq {xs} {ys} eq = extensionality xs ys (eqCount→iso xs ys eq)



-------------------------------------------------------------------
-- Properties of Union / Towards the Commutative Monoid Instance --
-------------------------------------------------------------------

union-acc-irrelevant : ∀ xs ys (p q : Acc _<ℕ_ (length xs + length ys)) → union xs ys p ≡ union xs ys q
union-acc-irrelevant [] ys (acc rs) (acc rs₁) = refl
union-acc-irrelevant (cons x xs x#xs) [] (acc rs) (acc rs₁) = refl
union-acc-irrelevant (cons x xs x#xs) (cons y ys y#ys) (acc rs) (acc rs₁) with total x y | total y x
... | inj₁ _ | inj₁ _ = cons-cong refl (union-acc-irrelevant xs (cons y ys y#ys) _ _)
... | inj₁ _ | inj₂ _ = cons-cong refl (union-acc-irrelevant xs (cons y ys y#ys) _ _)
... | inj₂ _ | inj₁ _ = cons-cong refl (union-acc-irrelevant (cons x xs x#xs) ys _ _)
... | inj₂ _ | inj₂ _ = cons-cong refl (union-acc-irrelevant (cons x xs x#xs) ys _ _)

ifL : ∀ {A : Set} {p : Bool} {x y : A}
      → p ≡ true → (if p then x else y) ≡ x
ifL refl = refl

ifR : ∀ {A : Set} {p : Bool} {x y : A}
      → p ≡ false → (if p then x else y) ≡ y
ifR refl = refl

does-not : ∀ {x y} → x ≢ y → does (x ≟ y) ≡ false
does-not {x} {y} x≢y with x ≟ y
... | yes x≡y = ⊥-elim (x≢y x≡y)
... | no _ = refl

does-too : ∀ {x y} → x ≡ y → does (x ≟ y) ≡ true
does-too {x} {y} x≡y with x ≟ y
... | yes _ = refl
... | no x≢y = ⊥-elim (x≢y x≡y)

union-idˡ : ∀ xs p → union [] xs p ≡ xs
union-idˡ xs (acc _) = refl

∪-idˡ : ∀ xs → [] ∪ xs ≡ xs
∪-idˡ xs = refl

union-idʳ : ∀ xs p → union xs [] p ≡ xs
union-idʳ [] (acc p) = refl
union-idʳ (cons x xs x#xs) (acc p) = refl

∪-idʳ : ∀ xs → xs ∪ [] ≡ xs
∪-idʳ xs = union-idʳ xs _

∪-countlem : ∀ xs ys p a → count (union xs ys p) a ≡ (count xs a) + (count ys a)
∪-countlem [] ys (acc p) a = refl
∪-countlem (cons x xs x#xs) [] (acc p) a = sym $ +-identityʳ _
∪-countlem (cons x xs x#xs) (cons y ys y#ys) (acc p) a with total x y
∪-countlem (cons x xs x#xs) (cons y ys y#ys) (acc p) a | inj₁ x≤y with a ≟ x | a ≟ y
... | yes refl | yes refl = cong suc (trans (∪-countlem xs (cons y ys y#ys) _ a) (cong (count xs x +_) (ifL $ does-too refl)))
... | yes refl | no a≢y   = cong suc (trans (∪-countlem xs (cons y ys y#ys) _ a) (cong (count xs x +_) (ifR $ does-not a≢y)))
... | no a≢x   | yes refl = trans (∪-countlem xs (cons y ys y#ys) _ a) (cong (count xs y +_) (ifL $ does-too refl))
... | no a≢x   | no a≢y   = trans (∪-countlem xs (cons y ys y#ys) _ a) (cong (count xs a +_) (ifR $ does-not a≢y))
∪-countlem (cons x xs x#xs) (cons y ys y#ys) (acc p) a | inj₂ y≤x with a ≟ x | a ≟ y
... | yes refl | yes refl = cong suc (trans (∪-countlem (cons x xs x#xs) ys _ a) (trans (cong (_+ count ys x) (ifL $ does-too refl)) (sym $ +-suc _ _)))
... | yes refl | no a≢y   = trans (∪-countlem (cons x xs x#xs) ys _ a) (cong (_+ count ys x) (ifL $ does-too refl))
... | no a≢x   | yes refl = trans (cong suc (trans (∪-countlem (cons x xs x#xs) ys _ a) (cong (_+ count ys y) (ifR $ does-not a≢x)))) (sym $ +-suc _ _)
... | no a≢x   | no a≢y   = trans (∪-countlem (cons x xs x#xs) ys _ a) (cong (_+ count ys a) (ifR $ does-not a≢x))

union-assoc : ∀ xs ys zs p q r s → union xs (union ys zs p) q ≡ union (union xs ys r) zs s
union-assoc xs ys zs (acc p) (acc q) (acc r) (acc s) = eqCount→eq (lem xs ys zs _ _ _ _) where
  lem : ∀ xs ys zs (p : Acc _<ℕ_ (length ys + length zs)) (p' : Acc _<ℕ_ (length xs + length (union ys zs p))) (q : Acc _<ℕ_ (length xs + length ys)) (q' : Acc _<ℕ_ (length (union xs ys q) + length zs))
    → count (union xs (union ys zs p) p') ≗ count (union (union xs ys q) zs q')
  lem xs ys zs r r' s s' a =
    begin
      count (union xs (union ys zs r) r') a
    ≡⟨ ∪-countlem xs (union ys zs r) r' a ⟩
      count xs a + count (union ys zs r) a
    ≡⟨ cong (count xs a +_) (∪-countlem ys zs r a) ⟩
      count xs a + (count ys a + count zs a)
    ≡⟨ (sym $ +-assoc (count xs a) (count ys a) (count zs a)) ⟩
      (count xs a + count ys a) + count zs a
    ≡⟨ (sym $ (cong (_+ count zs a) (∪-countlem xs ys s a))) ⟩
      count (union xs ys s) a + count zs a
    ≡⟨ (sym $ ∪-countlem (union xs ys s) zs s' a ) ⟩
      count (union (union xs ys s) zs s') a
    ∎ where open ≡-Reasoning

∪-assoc : ∀ xs ys zs → xs ∪ (ys ∪ zs) ≡ (xs ∪ ys) ∪ zs
∪-assoc xs ys zs = union-assoc xs ys zs _ _ _ _

union-comm : ∀ xs ys p q → union xs ys p ≡ union ys xs q
union-comm xs ys (acc p) (acc q) = eqCount→eq (lem xs ys _ _) where
  lem : ∀ xs ys (p : Acc _<ℕ_ (length xs + length ys)) (q : Acc _<ℕ_ (length ys + length xs))
    → count (union xs ys p) ≗ count (union ys xs q)
  lem xs ys p q a =
    begin
      count (union xs ys p) a
    ≡⟨ ∪-countlem xs ys p a ⟩
      count xs a + count ys a
    ≡⟨ +-comm (count xs a) (count ys a) ⟩
      count ys a + count xs a
    ≡⟨ (sym $ ∪-countlem ys xs q a) ⟩
      count (union ys xs q) a
    ∎ where open ≡-Reasoning

∪-comm : ∀ xs ys → xs ∪ ys ≡ ys ∪ xs
∪-comm xs ys = union-comm xs ys _ _

SortedList-CommMon : IsCommutativeMonoid _≡_ _∪_ []
IsMagma.isEquivalence (IsSemigroup.isMagma (IsMonoid.isSemigroup (IsCommutativeMonoid.isMonoid SortedList-CommMon))) = isEquivalence
IsMagma.∙-cong (IsSemigroup.isMagma (IsMonoid.isSemigroup (IsCommutativeMonoid.isMonoid SortedList-CommMon))) = cong₂ _∪_
IsSemigroup.assoc (IsMonoid.isSemigroup (IsCommutativeMonoid.isMonoid SortedList-CommMon)) a b c = sym $ ∪-assoc a b c
IsMonoid.identity (IsCommutativeMonoid.isMonoid SortedList-CommMon) = ∪-idˡ , ∪-idʳ
IsCommutativeMonoid.comm SortedList-CommMon = ∪-comm

union-cong : ∀ {xs ys xs' ys'} p q
       → xs ≡ xs' → ys ≡ ys'
       → union xs ys p ≡ union xs' ys' q
union-cong {xs} {ys} p q refl refl = union-acc-irrelevant xs ys p q

------------------------------
-- Ordering on Sorted Lists --
------------------------------

_<_ : X → X → Set
a < b = (a ≤ b) × (a ≢ b)

<-tri : Trichotomous _≡_ _<_
<-tri x y with total x y | x ≟ y
... | _        | yes refl = tri≈ (λ p → proj₂ p refl) refl (λ p → proj₂ p refl)
... | inj₁ x≤y | no x≢y   = tri< (x≤y , x≢y) x≢y (λ p → x≢y $ ≤-antisym x≤y (proj₁ p))
... | inj₂ y≤x | no x≢y   = tri> (λ p → x≢y $ ≤-antisym (proj₁ p) y≤x) x≢y (y≤x , (≢-sym x≢y))

<-trans : ∀ {a b c} → a < b → b < c → a < c
<-trans {a} {b} {c} (a≤b , a≢b) (b≤c , b≢c) = a≤c , a≢c where
  a≤c : a ≤ c
  a≤c = ≤-trans a≤b b≤c

  a≢c : a ≢ c
  a≢c with a ≟ c
  ... | no ¬q = ¬q
  ... | yes refl = λ _ → a≢b (≤-antisym a≤b b≤c)

<-prop : ∀ {x y} → Irrelevant (x < y)
<-prop (p , q) (p' , q') = cong₂ _,_ (≤-prop p p') refl

data _≤L_ : SortedList → SortedList → Set where
  [] : ∀ {xs} → [] ≤L xs
  lt : ∀ {x y xs ys} {x#xs : x # xs} {y#ys : y # ys}
     → x < y → (cons x xs x#xs) ≤L (cons y ys y#ys)
  eq : ∀ {x y xs ys} {x#xs : x # xs} {y#ys : y # ys}
     → x ≡ y → xs ≤L ys → (cons x xs x#xs) ≤L (cons y ys y#ys)

≤L-refl : ∀ {xs} → xs ≤L xs
≤L-refl {[]} = []
≤L-refl {cons x xs x#xs} = eq refl ≤L-refl

≤L-trans : ∀ {xs ys zs} → xs ≤L ys → ys ≤L zs → xs ≤L zs
≤L-trans [] q = []
≤L-trans (lt x<y) (lt y<z) = lt (<-trans x<y y<z)
≤L-trans (lt x<y) (eq refl ys≤zs) = lt x<y
≤L-trans (eq refl xs≤ys) (lt y≤z) = lt y≤z
≤L-trans (eq refl xs≤ys) (eq refl ys≤zs) = eq refl (≤L-trans xs≤ys ys≤zs)

≤L-antisym : ∀ {xs ys} → xs ≤L ys → ys ≤L xs → xs ≡ ys
≤L-antisym [] [] = refl
≤L-antisym (lt (x≤y , x≢y)) (lt (y≤x , _)) = ⊥-elim $ x≢y (≤-antisym x≤y y≤x)
≤L-antisym (lt (_ , ¬refl)) (eq refl _) = ⊥-elim $ ¬refl refl
≤L-antisym (eq refl _) (lt (_ , ¬refl)) = ⊥-elim $ ¬refl refl
≤L-antisym (eq refl p) (eq x=x q) = cons-cong refl (≤L-antisym p q)

≤L-total : ∀ xs ys → (xs ≤L ys) ⊎ (ys ≤L xs)
≤L-total [] ys = inj₁ []
≤L-total (cons x xs x#xs) [] = inj₂ []
≤L-total (cons x xs x#xs) (cons y ys y#ys) with x ≟ y | total x y | ≤L-total xs ys
... | yes refl | _ | inj₁ xs≤ys = inj₁ $ eq refl xs≤ys
... | yes refl | _ | inj₂ ys≤xs = inj₂ $ eq refl ys≤xs
... | no x≢y | inj₁ x≤y | _ = inj₁ $ lt $ x≤y , x≢y
... | no x≢y | inj₂ y≤x | _ = inj₂ $ lt $ y≤x , (≢-sym x≢y)

≤L-prop : ∀ {xs ys} → Irrelevant (xs ≤L ys)
≤L-prop [] [] = refl
≤L-prop (lt p) (lt q) = cong lt (<-prop p q )
≤L-prop (lt (_ , ¬refl)) (eq refl q) = ⊥-elim $ ¬refl refl
≤L-prop (eq refl p) (lt (_ , ¬refl)) = ⊥-elim $ ¬refl refl
≤L-prop (eq refl p) (eq x=x q) = cong₂ eq (≡-prop refl x=x) (≤L-prop p q)

_=L?_ : (xs ys : SortedList) → Dec (xs ≡ ys)
[] =L? [] = yes refl
[] =L? cons x ys x#xs = no λ {()}
cons x xs x#xs =L? [] = no λ {()}
cons x xs x#xs =L? cons y ys y#ys with x ≟ y | xs =L? ys
... | yes refl | yes refl = yes $ cons-cong refl refl
... | yes refl | no xs≢ys = no (λ p → xs≢ys (cons-injective-tail p))
... | no x≢y   | _        = no (λ p → x≢y (cons-injective-head p))

_≤L?_ : (xs ys : SortedList) → Dec (xs ≤L ys)
[] ≤L? _ = yes []
cons x xs x#xs ≤L? [] = no λ {()}
cons x xs x#xs ≤L? cons y ys y#ys with <-tri x y | xs ≤L? ys
... | tri< x<y x≠y  x≯y | _ = yes $ lt x<y
... | tri> x≮y x≠y  x>y | _ = no lem where
  lem : ¬ (cons x xs x#xs ≤L cons y ys y#ys)
  lem (lt x<y) = ⊥-elim (x≮y x<y)
  lem (eq refl xs≤ys) = ⊥-elim (x≠y refl)
... | tri≈ x≮y refl x≯y | yes xs≤ys = yes $ eq refl xs≤ys
... | tri≈ x≮y refl x≯y | no xs≰ys  = no lem where
  lem : ¬ (cons x xs x#xs ≤L cons x ys y#ys)
  lem (lt x<y) = ⊥-elim (x≮y x<y)
  lem (eq x=x xs≤ys) = ⊥-elim (xs≰ys xs≤ys)


SortedList-Order : IsPropDecTotalOrder _≡_ _≤L_
IsPreorder.isEquivalence (IsPartialOrder.isPreorder (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO SortedList-Order)))) = isEquivalence
IsPreorder.reflexive (IsPartialOrder.isPreorder (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO SortedList-Order)))) refl = ≤L-refl
IsPreorder.trans (IsPartialOrder.isPreorder (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO SortedList-Order)))) = ≤L-trans
IsPartialOrder.antisym (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO SortedList-Order))) = ≤L-antisym
IsTotalOrder.total (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO SortedList-Order)) = ≤L-total
IsDecTotalOrder._≟_ (IsPropDecTotalOrder.isDTO SortedList-Order) = _=L?_
IsDecTotalOrder._≤?_ (IsPropDecTotalOrder.isDTO SortedList-Order) = _≤L?_
IsPropDecTotalOrder.≤-prop SortedList-Order = ≤L-prop


SortedList-isOCM : IsOrderedCommutativeMonoid _≡_ _≤L_ _∪_ []
IsOrderedCommutativeMonoid.isICM SortedList-isOCM = SortedList-CommMon
IsOrderedCommutativeMonoid.isPDTO SortedList-isOCM = SortedList-Order

-----------------------------------
-- Properties of Insertion
-----------------------------------

insert-countlem-yes : ∀ x xs a p
                    → a ≡ x
                    → (count (insert' x xs p) a)
                    ≡ suc (count xs a)
insert-countlem-yes x [] .x (acc p) refl = ifL $ does-too refl
insert-countlem-yes x (cons y ys y#ys) .x (acc p) refl with total x y
insert-countlem-yes x (cons y ys y#ys) .x (acc p) refl | inj₁ u with x ≟ y
... | yes refl = trans (ifL $ does-too refl) (cong suc (trans (cong (λ z → count z x) (union-idˡ (cons y ys y#ys) (p ≤ℕ-refl))) (ifL $ does-too refl)))
... | no x≢y   = trans (ifL $ does-too refl) (cong suc (trans (cong (λ z → count z x) (union-idˡ (cons y ys y#ys) (p ≤ℕ-refl))) (ifR $ does-not x≢y)))
insert-countlem-yes x (cons y ys y#ys) .x (acc p) refl | inj₂ u with x ≟ y
... | yes refl = cong suc (insert-countlem-yes x ys x _ refl)
... | no x≢y   = insert-countlem-yes x ys x _ refl


insert-countlem-no : ∀ x xs a p
                   → a ≢ x
                   → (count (insert' x xs p) a)
                   ≡ (count xs a)
insert-countlem-no x [] a (acc p) a≢x = ifR $ does-not a≢x
insert-countlem-no x (cons y ys y#ys) a (acc p) a≢x with total x y
insert-countlem-no x (cons y ys y#ys) a (acc p) a≢x | inj₁ _ with a ≟ y
... | yes refl = trans (ifR $ does-not a≢x) (trans (cong (λ z → count z a) (union-idˡ (cons y ys y#ys) (p ≤ℕ-refl))) (ifL $ does-too refl))
... | no a≢y   = trans (ifR $ does-not a≢x) (trans (cong (λ z → count z a) (union-idˡ (cons y ys y#ys) (p ≤ℕ-refl))) (ifR $ does-not a≢y))
insert-countlem-no x (cons y ys y#ys) a (acc p) a≢x | inj₂ _ with a ≟ y
... | yes refl = cong suc (insert-countlem-no x ys a (p ≤ℕ-refl) a≢x)
... | no a≢y   = insert-countlem-no x ys a (p ≤ℕ-refl) a≢x


insert-countlem : ∀ x xs a p
                → (count (insert' x xs p) a)
                ≡ (if (does $ a ≟ x) then suc (count xs a) else (count xs a))
insert-countlem x xs a p with a ≟ x
... | yes a≡x = insert-countlem-yes x xs a p a≡x
... | no  a≢x = insert-countlem-no x xs a p a≢x

insert-length : ∀ x xs p
              → length (insert' x xs p) ≡ suc (length xs)
insert-length x [] (acc p) = refl
insert-length x (cons y ys y#ys) (acc p) with total x y
... | inj₁ _ = cong (suc ∘ length) (union-idˡ (cons y ys y#ys) (p ≤ℕ-refl))
... | inj₂ _ = cong suc (insert-length x ys _)

insert≡cons : ∀ {x xs} (x#xs : x # xs) p
            → insert' x xs p ≡ cons x xs x#xs
insert≡cons {x} {[]} [] (acc p) = refl
insert≡cons {x} {cons y ys y#ys} (x≤y ∷ x#ys) (acc p) with total x y
... | inj₁ _ = cons-cong refl (union-idˡ (cons y ys y#ys) (p ≤ℕ-refl))
... | inj₂ y≤x = cons-cong (≤-antisym y≤x x≤y) (trans (insert≡cons {x} {ys} x#ys (p ≤ℕ-refl)) (cons-cong (≤-antisym x≤y y≤x) refl))
