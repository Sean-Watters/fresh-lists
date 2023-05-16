{-# OPTIONS --safe --without-K #-}

open import Algebra.Structure.OICM
open import Data.FreshList.InductiveInductive
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Function
open import Relation.Binary hiding (Irrelevant)
open import Relation.Binary.PropositionalEquality renaming (isEquivalence to ≡-isEq)
open import Relation.Nullary

module Data.FreshList.FreeCommMonoid.Ordering
  {X : Set} {_≈_ : X → X → Set} {_≤_ : X → X → Set}
  (≤-PDTO : IsPropDecTotalOrder _≈_ _≤_)
  where

open import Data.FreshList.FreeCommMonoid ≤-PDTO

private
  ≤-prop = IsPropDecTotalOrder.≤-prop ≤-PDTO
  ≤-total = IsPropDecTotalOrder.total ≤-PDTO
  ≤-refl = IsPropDecTotalOrder.refl ≤-PDTO
  ≤-trans = IsPropDecTotalOrder.trans ≤-PDTO
  ≤-antisym = IsPropDecTotalOrder.antisym ≤-PDTO
  ≤-resp-≈ = IsPropDecTotalOrder.≤-resp-≈ ≤-PDTO
  _≈?_ = IsPropDecTotalOrder._≟_ ≤-PDTO
  ≈-sym = IsEquivalence.sym (IsPropDecTotalOrder.isEquivalence ≤-PDTO)
  ≈-trans = IsEquivalence.trans (IsPropDecTotalOrder.isEquivalence ≤-PDTO)
  ≈-refl = IsEquivalence.refl (IsPropDecTotalOrder.isEquivalence ≤-PDTO)


open Data.FreshList.InductiveInductive.WithIrr _≤_ ≤-prop

----------------------------------------------
-- Strictification of the order on elements --
----------------------------------------------

_≉_ : X → X → Set
a ≉ b = (a ≈ b) → ⊥

≉-sym : Symmetric _≉_
≉-sym = {!!}

≉-prop : ∀ {x y} → Irrelevant (x ≉ y)
≉-prop = {!!}

_<_ : X → X → Set
a < b = (a ≤ b) × (a ≉ b)

<-tri : Trichotomous _≈_ _<_
<-tri x y with ≤-total x y | x ≈? y
... | _        | yes x≈y = tri≈ (λ p → proj₂ p x≈y) x≈y (λ p → proj₂ p (≈-sym x≈y))
... | inj₁ x≤y | no x≉y   = tri< (x≤y , x≉y) x≉y (λ p → x≉y $ ≤-antisym x≤y (proj₁ p))
... | inj₂ y≤x | no x≉y   = tri> (λ p → x≉y $ ≤-antisym (proj₁ p) y≤x) x≉y (y≤x , ≉-sym x≉y)

<-trans : ∀ {a b c} → a < b → b < c → a < c
<-trans {a} {b} {c} (a≤b , a≉b) (b≤c , b≉c) = a≤c , a≉c where
  a≤c : a ≤ c
  a≤c = ≤-trans a≤b b≤c

  a≉c : a ≉ c
  a≉c with a ≈? c
  ... | no ¬q = ¬q
  ... | yes a≈c = λ _ → a≉b (≤-antisym a≤b (proj₁ ≤-resp-≈ (≈-sym a≈c) b≤c))

<-prop : ∀ {x y} → Irrelevant (x < y)
<-prop (p , q) (p' , q') = cong₂ _,_ (≤-prop p p') {!!}

<-resp-≈R : _<_ Respectsʳ _≈_
<-resp-≈R b≈c (a≤b , a≉b) = (proj₁ ≤-resp-≈ b≈c a≤b) , (λ a≈c → a≉b (≈-trans a≈c (≈-sym b≈c)))

<-resp-≈L : _<_ Respectsˡ _≈_
<-resp-≈L {a} {b} {c} b≈c (b≤a , b≉a) = (proj₂ ≤-resp-≈ b≈c b≤a) , (λ c≈a → b≉a (≈-trans b≈c c≈a))

------------------------------
-- Ordering on sorted lists --
------------------------------

data _≤L_ : SortedList → SortedList → Set where
  [] : ∀ {xs} → [] ≤L xs
  lt : ∀ {x y xs ys} {x#xs : x # xs} {y#ys : y # ys}
     → x < y → (cons x xs x#xs) ≤L (cons y ys y#ys)
  eq : ∀ {x y xs ys} {x#xs : x # xs} {y#ys : y # ys}
     → x ≈ y → xs ≤L ys → (cons x xs x#xs) ≤L (cons y ys y#ys)

≤L-refl : ∀ {xs} → xs ≤L xs
≤L-refl {[]} = []
≤L-refl {cons x xs x#xs} = eq ≈-refl ≤L-refl

≤L-trans : ∀ {xs ys zs} → xs ≤L ys → ys ≤L zs → xs ≤L zs
≤L-trans [] q = []
≤L-trans (lt x<y) (lt y<z) = lt (<-trans x<y y<z)
≤L-trans (lt x<y) (eq y≈z ys≤zs) = lt (<-resp-≈R y≈z x<y)
≤L-trans (eq x≈y xs≤ys) (lt y<z) = lt (<-resp-≈L (≈-sym x≈y) y<z)
≤L-trans (eq x≈y xs≤ys) (eq y≈z ys≤zs) = eq (≈-trans x≈y y≈z) (≤L-trans xs≤ys ys≤zs)

{-
≤L-antisym : ∀ {xs ys} → xs ≤L ys → ys ≤L xs → xs ≈ ys
≤L-antisym [] [] = refl
≤L-antisym (lt (x≤y , x≉y)) (lt (y≤x , _)) = ⊥-elim $ x≉y (≤-antisym x≤y y≤x)
≤L-antisym (lt (_ , ¬refl)) (eq refl _) = ⊥-elim $ ¬refl refl
≤L-antisym (eq refl _) (lt (_ , ¬refl)) = ⊥-elim $ ¬refl refl
≤L-antisym (eq refl p) (eq refl q) = cons-cong refl (≤L-antisym p q)

≤L-total : ∀ xs ys → (xs ≤L ys) ⊎ (ys ≤L xs)
≤L-total [] ys = inj₁ []
≤L-total (cons x xs x#xs) [] = inj₂ []
≤L-total (cons x xs x#xs) (cons y ys y#ys) with x ≟ y | total x y | ≤L-total xs ys
... | yes refl | _ | inj₁ xs≤ys = inj₁ $ eq refl xs≤ys
... | yes refl | _ | inj₂ ys≤xs = inj₂ $ eq refl ys≤xs
... | no x≉y | inj₁ x≤y | _ = inj₁ $ lt $ x≤y , x≉y
... | no x≉y | inj₂ y≤x | _ = inj₂ $ lt $ y≤x , (≉-sym x≉y)

≤L-prop : ∀ {xs ys} → Irrelevant (xs ≤L ys)
≤L-prop [] [] = refl
≤L-prop (lt p) (lt q) = cong lt (<-prop p q )
≤L-prop (lt (_ , ¬refl)) (eq refl q) = ⊥-elim $ ¬refl refl
≤L-prop (eq refl p) (lt (_ , ¬refl)) = ⊥-elim $ ¬refl refl
≤L-prop (eq refl p) (eq refl q) = cong (eq refl) (≤L-prop p q)

_=L?_ : (xs ys : SortedList) → Dec (xs ≈ ys)
[] =L? [] = yes refl
[] =L? cons x ys x#xs = no λ {()}
cons x xs x#xs =L? [] = no λ {()}
cons x xs x#xs =L? cons y ys y#ys with x ≟ y | xs =L? ys
... | yes refl | yes refl = yes $ cons-cong refl refl
... | yes refl | no xs≉ys = no λ {refl → xs≉ys refl}
... | no x≉y   | _        = no λ {refl → x≉y refl}

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
  lem (eq refl xs≤ys) = ⊥-elim (xs≰ys xs≤ys)


SortedList-Order : IsPropDecTotalOrder _≈_ _≤L_
IsPreorder.isEquivalence (IsPartialOrder.isPreorder (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO SortedList-Order)))) = ≈-isEq
IsPreorder.reflexive (IsPartialOrder.isPreorder (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO SortedList-Order)))) refl = ≤L-refl
IsPreorder.trans (IsPartialOrder.isPreorder (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO SortedList-Order)))) = ≤L-trans
IsPartialOrder.antisym (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO SortedList-Order))) = ≤L-antisym
IsTotalOrder.total (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO SortedList-Order)) = ≤L-total
IsDecTotalOrder._≟_ (IsPropDecTotalOrder.isDTO SortedList-Order) = _=L?_
IsDecTotalOrder._≤?_ (IsPropDecTotalOrder.isDTO SortedList-Order) = _≤L?_
IsPropDecTotalOrder.≤-prop SortedList-Order = ≤L-prop

-}
