{-# OPTIONS --without-K --safe #-}
open import Level hiding (zero; suc)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
open import Data.Empty

open import Relation.Nullary
open import Relation.Unary using (Decidable)
open import Relation.Binary hiding (Decidable; Irrelevant)
open import Relation.Binary.PropositionalEquality hiding (sym)

module Data.FreshList.InductiveInductive where

data List# {n m} {A : Set n} (R : A → A → Set m) : Set (n ⊔ m)
data _#_   {n m} {A : Set n} {R : A → A → Set m} : (x : A) → (xs : List# R) → Set (n ⊔ m)

data List# {A = A} R where
  []   : List# R
  cons : (x : A) (xs : List# R) (x#xs : x # xs) → List# R

data _#_ {A = A} {R = R} where
  []  : {a : A} → _#_ {R = R} a []
  _∷_ : {a x : A} {xs : List# R} {x#xs : x # xs} → R a x → a # xs → a # (cons x xs x#xs)
pattern _∷#_ a as = cons a as _

-- The Any and All predicates for fresh lists
data All {n m o} {A : Set n} {R : A → A → Set m} (P : A → Set o) : (xs : List# R) → Set (n ⊔ m ⊔ o) where
  [] : All P []
  _∷_ : {x : A} {xs : List# R} {x#xs : x # xs} → P x → All P xs → All P (cons x xs x#xs)

data Any {n m o} {A : Set n} {R : A → A → Set m} (P : A → Set o) : (xs : List# R) → Set (n ⊔ m ⊔ o) where
  here  : {x : A} {xs : List# R} {x#xs : x # xs} → P x      → Any P (cons x xs x#xs)
  there : {x : A} {xs : List# R} {x#xs : x # xs} → Any P xs → Any P (cons x xs x#xs)

-- Fix an implicit R so we don't need to keep writing it.
-- Only put definitions in here if the R really can be inferred
-- (usually satisfied by a (List# R) as an explicit argument)
module _
    {n m : Level}
    {X : Set n}
    {R : X → X → Set m}
    where

    all? : ∀ {o} {P : X → Set o} → Decidable P → (xs : List# R) → Dec (All P xs)
    all? p? [] = yes []
    all? p? (cons x xs x#xs) with p? x | all? p? xs
    ... | _      | no ¬pxs = no λ {(px ∷ pxs) → ¬pxs pxs}
    ... | no ¬px | _       = no λ {(px ∷ pxs) → ¬px px}
    ... | yes px | yes pxs = yes (px ∷ pxs)

    any? : ∀ {o} {P : X → Set o} → Decidable P → (xs : List# R) → Dec (Any P xs)
    any? p? [] = no λ {()}
    any? p? (cons x xs x#xs) with p? x | any? p? xs
    ... | yes px | _ = yes (here px)
    ... | no ¬px | yes pxs = yes (there pxs)
    ... | no ¬px | no ¬pxs = no λ {(here px) → ¬px px; (there pxs) → ¬pxs pxs}


    ¬any[] : ∀ {o} {P : X → Set o} → ¬ (Any {R = R} P [])
    ¬any[] ()

    here≢there : ∀ {o} {P : X → Set o} {x : X} {xs : List# R} {x#xs : x # xs}
               → {px : P x} {q : Any P xs}
               → here {x#xs = x#xs} px ≢ there q
    here≢there ()

{-
    -- Concatenation of fresh lists.
    -- Requires a "gluability" condition proving that the two lists may actually be concatenated
    -- Specific choices of R might admit more ergonomic or efficient logically
    -- equivalent notions of gluability.
    concat : (xs ys : List# R) → All (_# ys) xs → List# R
    concat [] ys [] = ys
    concat (cons x xs x#xs) ys (x#ys ∷ g) = cons x (concat xs ys g) (concat-fresh g x#xs x#ys) where
      concat-fresh : {a : X} {xs ys : List# R} (g : All (_# ys) xs) (a#xs : a # xs) → a # ys → a # concat xs ys g
      concat-fresh [] a#xs a#ys = a#ys
      concat-fresh (x#ys ∷ g) (Rax ∷ a#xs) a#ys = Rax ∷ concat-fresh g a#xs a#ys

    syntax concat xs ys g = xs ++[ g ] ys

    snoc : (xs : List# R) (x : X) → All (λ a → R a x) xs → List# R
    snoc xs x p = xs ++[ snoc-fresh p ] (cons x [] []) where
      snoc-fresh : ∀ {x : X} {xs : List# R} → All (λ a → R a x) xs → All (λ a → _#_ {A = X} {R} a (cons x [] [])) xs
      snoc-fresh [] = []
      snoc-fresh (px ∷ pxs) = (px ∷ []) ∷ (snoc-fresh pxs)
-}

    length : List# R → ℕ
    length [] = zero
    length (cons _ xs _) = suc (length xs)

    #-trans : Transitive R → (a x : X) (xs : List# R) → R a x → x # xs → a # xs
    #-trans R-trans a x [] Rax x#xs = []
    #-trans R-trans a x (cons y ys y#ys) Rax (Rxy ∷ x#ys) = R-trans Rax Rxy ∷ #-trans R-trans a x ys Rax x#ys

    #-tail : {a x : X} {xs : List# R} {x#xs : x # xs} → a # (cons x xs x#xs) → a # xs
    #-tail (px ∷ pxs) = pxs


    cons-injective-head : {x y : X} {xs ys : List# R} {x#xs : x # xs} {y#ys : y # ys}
                        → cons x xs x#xs ≡ cons y ys y#ys → x ≡ y
    cons-injective-head refl = refl

    cons-injective-tail : {x y : X} {xs ys : List# R} {x#xs : x # xs} {y#ys : y # ys}
                        → cons x xs x#xs ≡ cons y ys y#ys → xs ≡ ys
    cons-injective-tail refl = refl

-- Fix a proof-irrelevant R
module WithIrr
    {n m : Level}
    {X : Set n}
    (R : X → X → Set m)
    (R-irr : ∀ {x y} → Irrelevant (R x y))
    where

    #-irrelevant : {x : X} {xs : List# R} → Irrelevant (x # xs)
    #-irrelevant [] [] = refl
    #-irrelevant (x ∷ p) (y ∷ q) = cong₂ _∷_ (R-irr x y) (#-irrelevant p q)

    cons-cong : {x y : X} {xs ys : List# R} {x#xs : x # xs} {y#ys : y # ys}
              → x ≡ y → xs ≡ ys
              → cons x xs x#xs ≡ cons y ys y#ys
    cons-cong refl refl = cong (cons _ _) (#-irrelevant _ _)


-- Fix an R and some notion of equality.
module WithEq
    {n m : Level}
    {X : Set n}
    (R : X → X → Set m)
    {_≈_ : X → X → Set m}
    (≈-isEq : IsEquivalence _≈_)
    (R-resp-≈ : R Respects₂ _≈_)
    where

    _∈_ : X → List# R → Set (n ⊔ m)
    x ∈ xs = Any (x ≈_) xs

    _∉_ : X → List# R → Set (n ⊔ m)
    x ∉ xs = ¬ (x ∈ xs)

    _⊆_ : (xs ys : List# R) -> Set (n ⊔ m)
    xs ⊆ ys = ∀ {a} -> a ∈ xs -> a ∈ ys

    _⊈_ : (xs ys : List# R) -> Set (n ⊔ m)
    xs ⊈ ys = ¬ (xs ⊆ ys)

    open IsEquivalence

    #-trans' : Transitive R → {a b : X} {xs : List# R} → a # xs → b ∈ xs → R a b
    #-trans' R-trans {a} {b} {cons x xs x#xs} (Rax ∷ a#xs) (here b≈x) = proj₁ R-resp-≈ (sym ≈-isEq b≈x) Rax 
    #-trans' R-trans {a} {b} {cons x xs x#xs} (Rax ∷ a#xs) (there p∈xs) = #-trans' R-trans a#xs p∈xs

    ∉-weaken : {a x : X} {xs : List# R} {x#xs : x # xs} → a ∉ (cons x xs x#xs) → a ∉ xs
    ∉-weaken ¬p q = ⊥-elim (¬p (there q))
