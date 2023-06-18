{-# OPTIONS --safe --without-K #-}

open import Level

open import Algebra.Structure.OICM
open import Algebra.Structures

open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty

open import Function hiding (_↔_)

open import Relation.Nullary
open import Relation.Binary hiding (Irrelevant)
open import Relation.Binary.PropositionalEquality

open import Axiom.Extensionality.Propositional

module Index where

_↔_ : ∀ {a b} → (A : Set a) → (B : Set b) → Set _
A ↔ B = (A → B) × (B → A)


open import Category.Base

open import Data.FreshList.InductiveInductive

open import Free.Monoid.Adjunction as Mon
open import Free.PointedSet.Adjunction as Pointed
open import Free.LeftRegularMonoid.Adjunction as LRMon
open import Free.MysteryStructure.Base

---------------
-- Section 3 --
---------------

Definition-1 = List#

Proposition-2 : {n m : Level} {X : Set n}
              → (R : X → X → Set m)
              → (∀ {x y} → Irrelevant (R x y))
              ↔ (∀ {x : X} {xs : List# R} → Irrelevant (x # xs))
Proposition-2 R = WithIrr.#-irrelevant R , λ x p₁ p₂ → #-irrelevant-iff R (λ _ _ → x) _ _ p₁ p₂

Corollary-3 : {n m : Level} {X : Set n}
            → (R : X → X → Set m) → (R-irr : ∀ {x y} → Irrelevant (R x y))
            → {x y : X} {xs ys : List# R} {x#xs : x # xs} {y#ys : y # ys}
            → (x ≡ y × xs ≡ ys)
            ↔ (cons x xs x#xs ≡ cons y ys y#ys)
Corollary-3 R R-irr = (λ { (p , q) → WithIrr.cons-cong R R-irr p q}) , λ {refl → refl , refl}

Lemma-4 : {n m : Level} {X : Set n} {R : X → X → Set m}
        → Transitive R → (a x : X) (xs : List# R) → R a x → x # xs → a # xs
Lemma-4 = #-trans

Definition-5 = Any

Definition-6 : {n m : Level} {X : Set n} (R : X → X → Set m)
             → {_≈_ : X → X → Set m} (≈-isEq : IsEquivalence _≈_) (R-resp-≈ : R Respects₂ _≈_)
             → X → List# R → Set (n ⊔ m)
Definition-6 = WithEq._∈_

-- Maybe ought to show both directions of iff separately; types seem to get messy otherwise
Lemma-7 : {A : Set} {R : A → A → Set}
        → (a : A) (xs : List# R) →
        let _∈A_ = WithEq._∈_ R isEquivalence ((λ {refl p → p}) , λ {refl p → p})
        in (a # xs) ↔ (∀ {b : A} → (b ∈A xs) → R a b)
Lemma-7 {R = R} a xs = {!WithEq.#-trans' R isEquivalence ((λ {refl p → p}) , λ {refl p → p})!} , {!!}

Proposition-8a : {X Y : Set} → {R : X → X → Set}
               → (X → Y → Y) → Y → List# R → Y
Proposition-8a = foldr


Proposition-8b : {X Y : Set} → {R : X → X → Set}
               → (h : List# R → Y)
               → (f : X → Y → Y) (e : Y)
               → (h [] ≡ e)
               → (∀ x xs (fx : x # xs) → h (cons x xs fx) ≡ f x (h xs))
               → foldr f e ≗ h
Proposition-8b = foldr-universal


---------------
-- Section 4 --
---------------

module Sec4
  {X : Set} {_<_ : X → X → Set}
  (<-STO : IsPropStrictTotalOrder _≡_ _<_) -- fix a propositional strict total order <
  where

  open import Free.IdempotentCommutativeMonoid.Base <-STO
  open import Free.IdempotentCommutativeMonoid.Properties <-STO
  open import Free.IdempotentCommutativeMonoid.Adjunction

  Definition-9 = SortedList

  Proposition-10 : (xs ys : SortedList) → SortedList
  Proposition-10 = _∪_

  Lemma-11a : {a x : X} {xs : SortedList} {fx : x # xs} -> a < x -> a ∉ (cons x xs fx)
  Lemma-11a = ext-lem

  --seems to not be used in theorem 12? am I blind?
  Lemma-11b : {!!}
  Lemma-11b = {!!}

  Theorem-12 : (xs ys : SortedList)
             -> (∀ x -> ((x ∈ xs) -> (x ∈ ys)) × ((x ∈ ys) -> (x ∈ xs)))
             -> xs ≡ ys
  Theorem-12 xs ys p = ≈L→≡ <-STO (extensionality xs ys p)

  Proposition-13 : IsIdempotentCommutativeMonoid _≡_ _∪_ []
  Proposition-13 = SL-isICM <-STO

  Definition-14 : Category
  Definition-14 = STO

  Definition-15 : Extensionality _ _ → Category
  Definition-15 = OICM

  open OicmMorphism
  Lemma-16 : Extensionality _ _
           → ∀ {A B} → {f g : OicmMorphism A B}
           → (fun f ≡ fun g) ↔ (f ≡ g)
  Lemma-16 ext = (eqOicmMorphism ext) , λ {refl → refl}

  Proposition-17 : IsPropStrictTotalOrder _≈L_ _<-lex_
  Proposition-17 = <-lex-STO

module _ where
  open import Free.IdempotentCommutativeMonoid.Base
  open import Free.IdempotentCommutativeMonoid.Properties
  open import Free.IdempotentCommutativeMonoid.Adjunction
  open PropStrictTotalOrder

  Definition-18 : {X Y : PropStrictTotalOrder}
                → (Carrier X → Carrier Y)
                → SortedList (proof X)
                → SortedList (proof Y)
  Definition-18 = SL-map

  Lemma-19 : {X Y : PropStrictTotalOrder} →
           let _∪X_ = _∪_ (proof X)
               _∪Y_ = _∪_ (proof Y) in
           {f : Carrier X → Carrier Y} →
           (xs ys : SortedList (proof X)) →
           SL-map {X} {Y} f (xs ∪X  ys) ≡ (SL-map {X} {Y} f xs) ∪Y (SL-map {X} {Y} f ys)
  Lemma-19 = SL-map-preserves-∪

  Theorem-20 : (ext : Extensionality _ _) → Functor STO (OICM ext)
  Theorem-20 = SORTEDLIST

-------- The line

---------------
-- Section 6 --
---------------

Proposition-32 : (ext : Extensionality _ _) → FREEMONOID ext ⊣ (Mon.FORGET ext)
Proposition-32 = MonoidAdjunction

Proposition-33 : (ext : Extensionality _ _) → (MAYBE ext) ⊣ Pointed.FORGET
Proposition-33 = PSetAdjunction

Definition-34 : Set₁
Definition-34 = LeftRegularMonoidWithPropDecApartness

Proposition-35 : (ext : Extensionality _ _) →
                 (UNIQUELIST ext) ⊣ (LRMon.FORGET ext)
Proposition-35 = UL-Adjunction

Proposition-36 : (ext : Extensionality _ _) →
                 (A : Set) → (A-is-set : {x y : A} → Irrelevant (x ≡ y)) →
                 Iso TYPE (List# {A = A} _≡_)
                          (⊤ ⊎ (A × (Σ[ n ∈ ℕ ] (NonZero n))))
Proposition-36 ext A A-is-set =
  record { to = FL-≡.to A A-is-set
         ; from = FL-≡.from A A-is-set
         ; to-from = ext (FL-≡.to-from A A-is-set)
         ; from-to = ext (FL-≡.from-to A A-is-set)
         }
