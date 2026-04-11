module Data.FreshList.InductiveInductive where

open import Axiom.UniquenessOfIdentityProofs
open import Axiom.UniquenessOfIdentityProofs.Properties
open import Level hiding (zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
open import Data.Empty
open import Function
open import Relation.Nullary
open import Relation.Unary using (Decidable)
open import Relation.Binary hiding (Decidable; Irrelevant)
open import Relation.Binary.PropositionalEquality renaming (sym to ≡-sym)
open import Relation.Binary.Isomorphism

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

    all-map : ∀ {a b} {P : X → Set a}{Q : X → Set b} → ∀ {xs : List# R} → (∀ {x} → P x → Q x) → All P xs → All Q xs
    all-map p⇒q []       = []
    all-map p⇒q (p ∷ ps) = p⇒q p ∷ all-map p⇒q ps

    fresh→all : {x : X} {xs : List# R} -> x # xs -> All (R x) xs
    fresh→all [] = []
    fresh→all (rx ∷ x#xs) = rx ∷ fresh→all x#xs

    all→fresh : {x : X} {xs : List# R} -> All (R x) xs -> x # xs
    all→fresh [] = []
    all→fresh (rx ∷ as) = rx ∷ all→fresh as

    here≢there : ∀ {o} {P : X → Set o} {x : X} {xs : List# R} {x#xs : x # xs}
               → {px : P x} {q : Any P xs}
               → here {x#xs = x#xs} px ≢ there q
    here≢there ()

    foldr : {Y : Set} → (X → Y → Y) → Y → List# R → Y
    foldr f e [] = e
    foldr f e (cons x xs x#xs) = f x (foldr f e xs)

    foldr-universal : {Y : Set}
                    → (h : List# R → Y)
                    → (f : X → Y → Y) (e : Y)
                    → (h [] ≡ e)
                    → (∀ x xs (fx : x # xs) → h (cons x xs fx) ≡ f x (h xs))
                    → foldr f e ≗ h
    foldr-universal h f e base step [] = ≡-sym base
    foldr-universal h f e base step (cons x xs x#xs) =
      begin
        foldr f e (cons x xs x#xs)
      ≡⟨ cong (f x) (foldr-universal h f e base step xs) ⟩
        f x (h xs)
      ≡⟨ (≡-sym $ step x xs x#xs) ⟩
        h (cons x xs x#xs)
      ∎ where open ≡-Reasoning

{-
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

    ∷-injective-head : ∀ {x y : X}{xs : List# R}{y#xs : y # xs} →
                       {p q : R x y} → {ps qs : x # xs} →
                       _#_._∷_ {x#xs = y#xs} p ps ≡ q ∷ qs → p ≡ q
    ∷-injective-head refl = refl

    open import Data.List
    open import Data.List.Relation.Unary.All as L using ()

    -- We can erase the proofs to recover the underlying list
    toList : List# R → List X
    toList [] = []
    toList (cons x xs _) = x ∷ (toList xs)

    toListAll : ∀ {k} → {P : X → Set k} → {xs : List# R} → All P xs → L.All P (toList xs)
    toListAll [] = L.[]
    toListAll (p ∷ ps) = p L.∷ toListAll ps

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

    R-irr-unique : ∀ {x y} → (p : R x y) → R-irr p p ≡ refl
    R-irr-unique p = UIP-prop R-irr (R-irr p p) refl

    #-irrelevant-unique : ∀ {x : X} {xs : List# R} (p : x # xs) → #-irrelevant p p ≡ refl
    #-irrelevant-unique [] = refl
    #-irrelevant-unique (x ∷ p) rewrite R-irr-unique x rewrite #-irrelevant-unique p = refl

    -- Depenedent cong₂ doesn't exist in general, so here's the version specialised to cons.
    -- There will also exist a ternery version which takes a proof that the freshness proofs
    -- are equal without assuming R to be propositional, but we never use that.
    cons-cong : {x y : X} {xs ys : List# R} {x#xs : x # xs} {y#ys : y # ys}
              → x ≡ y → xs ≡ ys
              → cons x xs x#xs ≡ cons y ys y#ys
    cons-cong refl refl = cong (cons _ _) (#-irrelevant _ _)

    -- Pulling a proof apart then putting it back together is identity,
    -- as long as X is a set.
    cons-cong-inverse : ∀ {x y xs ys x#xs y#ys}
                      → UIP X
                      → (p : cons x xs x#xs ≡ cons y ys y#ys)
                      → p ≡ cons-cong (cons-injective-head p) (cons-injective-tail p)
    cons-cong-inverse {x#xs = []} uipX refl = refl
    cons-cong-inverse {x} {.x} {cons y ys y#ys} {cons .y .ys .y#ys} {Rxy ∷ x#ys} {.Rxy ∷ .x#ys} uipX refl
      rewrite #-irrelevant-unique x#ys rewrite R-irr-unique Rxy = refl

    -- If X is a Set, then so are the types of fresh lists over X.
    UIP-List# : UIP X → UIP (List# R)
    UIP-List# uipX {[]} {[]} refl refl = refl
    UIP-List# uipX {cons x xs x#xs} {cons y ys y#ys} p q =
      begin
        p
      ≡⟨ cons-cong-inverse uipX p ⟩
        cons-cong (cons-injective-head p) (cons-injective-tail p)
      ≡⟨ cong₂ cons-cong (uipX (cons-injective-head p) (cons-injective-head q)) (UIP-List# uipX {xs} {ys} (cons-injective-tail p) (cons-injective-tail q)) ⟩
        cons-cong (cons-injective-head q) (cons-injective-tail q)
      ≡⟨ ≡-sym $ cons-cong-inverse uipX q ⟩
        q
      ∎ where open ≡-Reasoning

    lift-decEq : ((x y : X) → Dec (x ≡ y)) → ((xs ys : List# R) → Dec (xs ≡ ys))
    lift-decEq dec [] [] = yes refl
    lift-decEq dec [] (cons x ys x#xs) = no λ ()
    lift-decEq dec (cons x xs x#xs) [] = no λ ()
    lift-decEq dec (cons x xs x#xs) (cons y ys y#ys) with dec x y
    lift-decEq dec (cons x xs x#xs) (cons y ys y#ys) | yes x≡y with lift-decEq dec xs ys
    lift-decEq dec (cons x xs x#xs) (cons y ys y#ys) | yes x≡y | yes xs≡ys = yes (cons-cong x≡y xs≡ys)
    lift-decEq dec (cons x xs x#xs) (cons y ys y#ys) | yes x≡y | no ¬xs≡ys
      = no λ x∷xs≡y∷ys → ⊥-elim (¬xs≡ys (cons-injective-tail x∷xs≡y∷ys))
    lift-decEq dec (cons x xs x#xs) (cons y ys y#ys) | no ¬x≡y
      = no λ x∷xs≡y∷ys → ⊥-elim (¬x≡y (cons-injective-head x∷xs≡y∷ys))

#-irrelevant-iff : {n m : Level}{X : Set n}(R : X → X → Set m) →
                   ((x : X)(xs : List# R) → Irrelevant (x # xs)) →
                   (x y : X) → Irrelevant (R x y)
#-irrelevant-iff R prop-# x y p q = ∷-injective-head (prop-# x (cons y [] []) (p ∷ []) (q ∷ []))

-- Fix an R and some notion of equality.
module WithEq
    {n m k : Level}
    {X : Set n}
    (R : X → X → Set m)
    {_≈_ : X → X → Set k}
    (≈-isEq : IsEquivalence _≈_)
    (R-resp-≈ : R Respects₂ _≈_)
    where

    _∈_ : X → List# R → Set (n ⊔ m ⊔ k)
    x ∈ xs = Any (x ≈_) xs

    _∉_ : X → List# R → Set (n ⊔ m ⊔ k)
    x ∉ xs = ¬ (x ∈ xs)

    _⊆_ : (xs ys : List# R) -> Set (n ⊔ m ⊔ k)
    xs ⊆ ys = ∀ {a} -> a ∈ xs -> a ∈ ys

    _⊈_ : (xs ys : List# R) -> Set (n ⊔ m ⊔ k)
    xs ⊈ ys = ¬ (xs ⊆ ys)

    open IsEquivalence renaming (refl to ≈-refl)

    #-trans' : {a b : X} {xs : List# R} → a # xs → b ∈ xs → R a b
    #-trans' {a} {b} {cons x xs x#xs} (Rax ∷ a#xs) (here b≈x) = proj₁ R-resp-≈ (sym ≈-isEq b≈x) Rax
    #-trans' {a} {b} {cons x xs x#xs} (Rax ∷ a#xs) (there p∈xs) = #-trans' a#xs p∈xs

    #-trans'-iff : {a : X} {xs : List# R} → (∀ {b} → b ∈ xs → R a b) → a # xs
    #-trans'-iff {xs = []} Rab = []
    #-trans'-iff {xs = cons x xs x#xs} Rab = Rab (here (≈-refl ≈-isEq)) ∷ #-trans'-iff {xs = xs} (λ z → Rab (there z))

    ∉-weaken : {a x : X} {xs : List# R} {x#xs : x # xs} → a ∉ (cons x xs x#xs) → a ∉ xs
    ∉-weaken ¬p q = ⊥-elim (¬p (there q))

    #-resp-≈ : {x y : X} {xs : List# R} → x # xs → x ≈ y → y # xs
    #-resp-≈ [] x≈y = []
    #-resp-≈ (px ∷ pxs) x≈y = proj₂ R-resp-≈ x≈y px ∷ #-resp-≈ pxs x≈y
