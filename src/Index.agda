{-# OPTIONS --safe --without-K #-}

open import Level

open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty

open import Relation.Nullary
open import Relation.Binary hiding (Irrelevant)
open import Relation.Binary.PropositionalEquality

open import Axiom.Extensionality.Propositional

module Index where

_↔_ : ∀ {a b} → (A : Set a) → (B : Set b) → Set _
A ↔ B = (A → B) × (B → A)


open import Category.Base

open import Data.FreshList.InductiveInductive

open import Free.MysteryStructure.Base


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


-------- The line

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
