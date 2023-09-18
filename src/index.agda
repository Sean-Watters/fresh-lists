{-# OPTIONS --safe --without-K #-}
----------------------------------------------------------------------------------------------------
-- Index of the Formalized Proofs in the paper
--
--     A Fresh Look at Commutativity: Free Algebraic Structures via Fresh Lists
--     by Clemens Kupke, Fredrik Nordvall Forsberg, and Sean Watters
--
--     APLAS'23.
----------------------------------------------------------------------------------------------------
--
-- Source files can be found at
--
--   https://github.com/Sean-Watters/fresh-lists
--
-- See `README.md` for versions of Agda and the standard library that these
-- files are tested with.

module index where

open import Level
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Function hiding (_↔_)
open import Algebra.Structures

open import Relation.Nullary
open import Relation.Binary hiding (Irrelevant)
open import Relation.Binary.PropositionalEquality
open import Axiom.Extensionality.Propositional

open import Relation.Binary.Isomorphism
open import Algebra.Structure.OICM
open import Category.Base

open import Data.FreshList.InductiveInductive
open import Data.FreshList.Sigma

open import Free.IdempotentCommutativeMonoid.Adjunction as IdCMon
open import Free.CommutativeMonoid.Adjunction as CMon
open import Free.Monoid.Adjunction as Mon
open import Free.PointedSet.Adjunction as Pointed
open import Free.LeftRegularMonoid.Adjunction as LRMon

open import Algebra.Structure.PartialMonoid
open import Free.ReflexivePartialMonoid.Properties as RPMon
open import Free.ReflexivePartialMonoid.Adjunction as RPMon

_↔_ : ∀ {a b} → (A : Set a) → (B : Set b) → Set _
A ↔ B = (A → B) × (B → A)

-- The following file gives an overview of the development
open import Everything

----------------------
-- Sections 1 and 2 --
----------------------

-- No formalisable content

---------------
-- Section 3 --
---------------

Definition-1 = List#

Proposition-2 : {n m : Level} {X : Set n}
              → (R : X → X → Set m)
              → List# R ≃ List#-ext
Proposition-2 R = List#-ext-iso {R = R}

Proposition-3 : {n m : Level} {X : Set n}
              → (R : X → X → Set m)
              → (∀ {x y} → Irrelevant (R x y))
              ↔ (∀ {x : X} {xs : List# R} → Irrelevant (x # xs))
Proposition-3 R = WithIrr.#-irrelevant R , λ x p₁ p₂ → #-irrelevant-iff R (λ _ _ → x) _ _ p₁ p₂

Corollary-4 : {n m : Level} {X : Set n}
            → (R : X → X → Set m) → (R-irr : ∀ {x y} → Irrelevant (R x y))
            → {x y : X} {xs ys : List# R} {x#xs : x # xs} {y#ys : y # ys}
            → (x ≡ y × xs ≡ ys)
            ↔ (cons x xs x#xs ≡ cons y ys y#ys)
Corollary-4 R R-irr = (λ { (p , q) → WithIrr.cons-cong R R-irr p q}) , λ {refl → refl , refl}

Lemma-5 : {n m : Level} {X : Set n} {R : X → X → Set m}
        → Transitive R → (a x : X) (xs : List# R) → R a x → x # xs → a # xs
Lemma-5 = #-trans

Definition-6 = Any

Definition-7 : {n m : Level} {X : Set n} (R : X → X → Set m)
             → X → List# R → Set (n ⊔ m)
Definition-7 R = WithEq._∈_ R isEquivalence ((λ {refl p → p}) , λ {refl p → p})

Lemma-8 : {A : Set} {R : A → A → Set}
        → (a : A) (xs : List# R) →
        let open WithEq R isEquivalence ((λ {refl p → p}) , λ {refl p → p})
        in (a # xs) ↔ (∀ {b : A} → (b ∈ xs) → R a b)
Lemma-8 {R = R} a xs = (λ a#xs {b} → #-trans' {a} {b} {xs} a#xs)
                     , #-trans'-iff
  where open WithEq R isEquivalence ((λ {refl p → p}) , λ {refl p → p})

Proposition-9 : {X Y : Set} → {R : X → X → Set}
              → Σ[ foldr ∈ ((X → Y → Y) → Y → List# R → Y) ]
                 ((h : List# R → Y) →
                 (f : X → Y → Y) (e : Y) →
                 (h [] ≡ e) →
                 (∀ x xs (fx : x # xs) → h (cons x xs fx) ≡ f x (h xs)) →
                 foldr f e ≗ h)
Proposition-9 = (foldr , foldr-universal)


---------------
-- Section 4 --
---------------

module Sec4
  {X : Set} {_<_ : X → X → Set}
  (<-STO : IsPropStrictTotalOrder _≡_ _<_)
  where

  open import Free.IdempotentCommutativeMonoid.Base <-STO
  open import Free.IdempotentCommutativeMonoid.Properties <-STO
  open import Free.IdempotentCommutativeMonoid.Adjunction

  Definition-10 = SortedList

  Proposition-11 : (xs ys : SortedList) → SortedList
  Proposition-11 = _∪_

  Lemma-12 : {a x : X} {xs : SortedList} {p : x # xs} ->
             (a < x -> a ∉ (cons x xs p))
           × (a # xs → a ∉ xs)
  Lemma-12 = (ext-lem , λ a#xs a∈xs → all<-irrefl a∈xs (fresh→all a#xs))

  Theorem-13 : (xs ys : SortedList)
             -> (∀ x -> ((x ∈ xs) -> (x ∈ ys)) × ((x ∈ ys) -> (x ∈ xs)))
             -> xs ≡ ys
  Theorem-13 xs ys p = ≈L→≡ <-STO (extensionality xs ys p)

  Proposition-14 : IsIdempotentCommutativeMonoid _≡_ _∪_ []
  Proposition-14 = SL-isICM <-STO

  Definition-15 : Category
  Definition-15 = STO

  Definition-16 : Extensionality _ _ → Category
  Definition-16 = OICM

  open OicmMorphism
  Lemma-17 : Extensionality _ _
           → ∀ {A B} → {f g : OicmMorphism A B}
           → (fun f ≡ fun g) ↔ (f ≡ g)
  Lemma-17 ext = (eqOicmMorphism ext) , λ {refl → refl}

  Proposition-18 : IsPropStrictTotalOrder _≈L_ _<-lex_
  Proposition-18 = <-lex-STO

module _ where
  open import Free.IdempotentCommutativeMonoid.Base
  open import Free.IdempotentCommutativeMonoid.Properties
  open import OrderingPrinciple.Base

  open IdCMon.PropStrictTotalOrder

  Definition-19 : {X Y : PropStrictTotalOrder}
                → (Carrier X → Carrier Y)
                → SortedList (proof X)
                → SortedList (proof Y)
  Definition-19 {X} {Y} = IdCMon.SL-map {X} {Y}

  Lemma-20 : {X Y : PropStrictTotalOrder} →
           let _∪X_ = _∪_ (proof X)
               _∪Y_ = _∪_ (proof Y) in
           {f : Carrier X → Carrier Y} →
           (xs ys : SortedList (proof X)) →
           IdCMon.SL-map {X} {Y} f (xs ∪X  ys) ≡ (IdCMon.SL-map {X} {Y} f xs) ∪Y (IdCMon.SL-map {X} {Y} f ys)
  Lemma-20 = IdCMon.SL-map-preserves-∪

  Theorem-21 : (ext : Extensionality _ _) → IdCMon.SORTEDLIST ext ⊣ IdCMon.FORGET ext
  Theorem-21 = IdCMon.SL-Adjunction

  Proposition-22a : (ext : Extensionality _ _)
                  → OrderingPrinciple → IsEquiv FORGETSTO × IsEquiv (FORGETOICM ext)
  Proposition-22a ext OP = (OP-gives-STO≃Set OP) , (OP-gives-OICM≃ICM ext OP)

  Proposition-22b : IsEquiv FORGETSTO → OrderingPrinciple
  Proposition-22b = STO≃Set-gives-OP


---------------
-- Section 5 --
---------------

module Sec5
  {X : Set} {_≤_ : X → X → Set}
  (≤-PDTO : IsPropDecTotalOrder _≡_ _≤_)
  where

  open import Free.CommutativeMonoid.Base ≤-PDTO
  open import Free.CommutativeMonoid.Properties ≤-PDTO
  open Data.FreshList.InductiveInductive.WithEq
         _≤_ isEquivalence ((λ { refl x → x }) , (λ { refl x → x }))

  Definition-23 : Set
  Definition-23 = SortedList

  Proposition-24 : SortedList → SortedList → SortedList
  Proposition-24 = _∪_

  Definition-25 : SortedList → X → ℕ
  Definition-25 = count

  Lemma-26 : ((x : X) → (ys : SortedList) → x ∉ ys → count ys x ≡ 0)
           × ({x y : X}{xs ys : SortedList}{p : x # xs}{q : y # ys} →
              ((a : X) → count (cons x xs p) a ≡ count (cons y ys q) a) →
              ((a : X) → count xs a ≡ count ys a))
  Lemma-26 = (λ x ys → count-lem2 {x} {ys})
           , (λ {x} {y} {xs} {ys} {p} {q} →
                 weaken-count-≗ {x} {y} {xs} {ys} {p} {q})

  Proposition-27 : (xs ys : SortedList) →
                   ((a : X) → count xs a ≡ count ys a) →
                   ((a : X) → (a ∈ xs) ≃ (a ∈ ys))
  Proposition-27 = eqCount→iso


  Lemma-28 : {b : X}{xs ys : SortedList}{p : b # xs}{q : b # ys} →
             ((a : X) → (a ∈ cons b xs p) ≃ (a ∈ cons b ys q)) →
             ((a : X) → (a ∈ xs) ≃ (a ∈ ys))
  Lemma-28 = peel-∈-iso

  Proposition-29 : (xs ys : SortedList) →
                   ((a : X) → (a ∈ xs) ≃ (a ∈ ys)) → xs ≡ ys
  Proposition-29 = extensionality

  Theorem-30 : (xs ys : SortedList) →
               ((a : X) → count xs a ≡ count ys a) → xs ≡ ys
  Theorem-30 xs ys = eqCount→eq {xs} {ys}

  Proposition-31 : IsOrderedCommutativeMonoid _≡_ _≤L_ _∪_ []
  Proposition-31 = SortedList-isOCM

Proposition-32 : (ext : Extensionality _ _) →
                 (CMon.SORTEDLIST ext) ⊣ (CMon.FORGET ext)
Proposition-32 = CMon.SL-Adjunction


---------------
-- Section 6 --
---------------

Proposition-33 : (ext : Extensionality _ _) → FREEMONOID ext ⊣ (Mon.FORGET ext)
Proposition-33 = MonoidAdjunction

Proposition-34 : (ext : Extensionality _ _) → (MAYBE ext) ⊣ Pointed.FORGET
Proposition-34 = PSetAdjunction

Definition-35 : Set₁
Definition-35 = LeftRegularMonoidWithPropDecApartness

Proposition-36 : (ext : Extensionality _ _) →
                 (UNIQUELIST ext) ⊣ (LRMon.FORGET ext)
Proposition-36 = UL-Adjunction

Lemma-37 : (A : Set) → (A-is-set : {x y : A} → Irrelevant (x ≡ y)) →
           (List# {A = A} _≡_) ≃ (⊤ ⊎ (A × (Σ[ n ∈ ℕ ] (NonZero n))))
Lemma-37 A A-is-set = RPMon.iso A A-is-set

Definition-38 : Set₁
Definition-38 = Σ[ X ∈ Set ]
                Σ[ _∙_↓ ∈ (X → X → Set) ]
                Σ[ op ∈ ((x y : X) → (x ∙ y ↓) → X) ]
                Σ[ ε ∈ X ]
                (IsReflexivePartialMonoid _≡_ _∙_↓ op ε)


Proposition-39 : (ext : Extensionality _ _) → (RPMon.FREE ext) ⊣ (RPMon.FORGET ext)
Proposition-39 = RPMon-Adjunction

---------------
-- Section 7 --
---------------

-- No formalisable content
