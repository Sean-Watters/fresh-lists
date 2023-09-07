{-# OPTIONS --safe --without-K #-}

open import Algebra.Structure.PartialMonoid

module Free.ReflexivePartialMonoid.PowerCute
  {X : Set}
  {_≈_ : X → X → Set} {_R_ : X → X → Set}
  {op : (x y : X) → x R y → X}
  {ε : X}
  (X-RPMon : IsReflexivePartialMonoid _≈_ _R_ op ε)
  where

-- Theorem : Exponentiation is defined for any reflexive partial monoid.
--
-- Proof Sketch :
---- (1) By reflexivity, x^(2^n) is trivially defined for all (x : X) and (n : ℕ).
---- (2) To produce x^k, we:
-------- (a) Choose n such that (2^n)>k.
-------- (b) Re-write x^(2^n) to be right-bracketed using associativity.
-------- (c) Chop off outer x's until we have k many x's in term. This is now x^k.
--
-- We can make this easier by talking about "cute lists", thanks to conor. More at 6

open import Data.Unit
open import Data.Empty
open import Data.List as List
open import Data.List.Properties
open import Data.List.NonEmpty
open import Data.Nat
open import Data.Nat.Properties
open import Data.PosNat
open import Data.Product hiding (assocˡ; assocʳ)
open import Function
open import Relation.Binary.PropositionalEquality

open IsReflexivePartialMonoid X-RPMon

-- Warmup: the sort of induction principle we need for lists.
data Chop (xs : List⁺ X) : Set where
  chop : ((ys zs : List⁺ X) → xs ≡ ys ⁺++⁺ zs → (Chop ys) × (Chop zs))
       → Chop xs

chop-singleton : ∀ x → Chop (x ∷ [])
chop-singleton x = chop f where
  f : (ys zs : List⁺ X) → x ∷ [] ≡ ys ⁺++⁺ zs → Chop ys × Chop zs
  f (y ∷ []) zs ()
  f (y ∷ y' ∷ ys) zs ()

chop-cons : ∀ x xs → Chop xs → Chop (x ∷⁺ xs)
chop-cons x xs (chop f) = chop g where
  g : (ys zs : List⁺ X) → x ∷⁺ xs ≡ ys ⁺++⁺ zs → Chop ys × Chop zs
  g (.x ∷ []) .xs refl = chop-singleton x , (chop f)
  g (.x ∷ y ∷ ys) zs refl = let (cyys , czs) = f (y ∷ ys) zs refl
                            in chop-cons x (y ∷ ys) cyys , czs

-- The key insight from Conor -- we represent monomials in the monoid as
-- nonempty lists which satisfy a predicate which encodes the partiality.
-- That is, elements of the list can be multiplied according to any choice
-- of bracketing. Thus, such lists support a "crush" operation which multiplies
-- everything together.
mutual
  -- The predicate - a list is "cute" if it can be CUT Everywhere such that the
  -- pieces are compatible.
  data Cute (xs : List⁺ X) : Set where
    cute : ((ys zs : List⁺ X) → xs ≡ ys ⁺++⁺ zs    -- If all ways of cutting up xs into two non-empty partitions ys and zs
           → Σ[ cys ∈ Cute ys ] Σ[ czs ∈ Cute zs ] -- ...result in ys and zs being cute
             ⟦ cys ⟧ R ⟦ czs ⟧)                    -- ...and their crushes being compatible,
         → Cute xs                                 -- then xs is cute.

  -- Pronounced "crush" due to Conor McBride; that is, this
  -- tells us how to crush on cute things. Always with the puns.
  ⟦_⟧ : ∀ {xs} → Cute xs → X
  ⟦_⟧ {x ∷ []} (cute f) = x
  ⟦_⟧ {x ∷ (y ∷ ys)} (cute f) = let (c , d , cRd) = f (x ∷ []) (y ∷ ys) refl
                                in op ⟦ c ⟧ ⟦ d ⟧ cRd


cute-singleton : ∀ x → Cute (x ∷ [])
cute-singleton x = cute f where
  f : (ys zs : List⁺ X) → x ∷ [] ≡ ys ⁺++⁺ zs
    → Σ[ cys ∈ (Cute ys) ] Σ[ czs ∈ (Cute zs) ] (⟦ cys ⟧ R ⟦ czs ⟧)
  f (_ ∷ []) _ ()
  f (_ ∷ _ ∷ _) _ ()

-- Crushing cute lists gives the same result if the underlying lists were equal
crush-cute-unique : ∀ {x y} → (p : Cute x) (q : Cute y) → x ≡ y → ⟦ p ⟧ ≡ ⟦ q ⟧
crush-cute-unique {x ∷ []} (cute p) (cute q) refl = refl
crush-cute-unique {x ∷ (y ∷ ys)} (cute p) (cute q) refl = {!!}

-- Concatenating then crushing is the same as crushing then muliplying.
cute-unique : ∀ {x y} (cx : Cute x) (cy : Cute y) (cxy : Cute (x ⁺++⁺ y)) → (p : ⟦ cx ⟧ R ⟦ cy ⟧) → ⟦ cxy ⟧ ≡ op ⟦ cx ⟧ ⟦ cy ⟧ p
cute-unique {x ∷ []} {y ∷ ys} cx cy cxy p = {!!}
cute-unique {x ∷ x' ∷ xs} {y ∷ ys} cx cy cxy p = {!!}

cute-cons : ∀ x xs → (cxs : Cute xs) → x R ⟦ cxs ⟧ → Cute (x ∷⁺ xs)
cute-cons x xs (cute f) xRxs = cute g where
  cute-cons-lem :  ∀ x xs → (cxs : Cute xs) → (p : x R ⟦ cxs ⟧) → op x ⟦ cxs ⟧ p ≡ ⟦ cute-cons x xs cxs p ⟧
  cute-cons-lem x xs cxs p = {!!}

  g : (ys zs : List⁺ X) → x ∷⁺ xs ≡ ys ⁺++⁺ zs
    → Σ[ cys ∈ (Cute ys) ] Σ[ czs ∈ (Cute zs) ] (⟦ cys ⟧ R ⟦ czs ⟧)
  g (.x ∷ []) .xs refl = cute-singleton x , cute f , xRxs
  g (.x ∷ y ∷ ys) zs refl = let (cyys , czs , yysRzs) = f (y ∷ ys) zs refl
                                (xRyys , xyysRzs) = assocL1 {x} {⟦ cyys ⟧} {⟦ czs ⟧} yysRzs (subst (x R_) (cute-unique cyys czs (cute f) yysRzs) xRxs)
                            in cute-cons x (y ∷ ys) cyys xRyys , czs , subst (_R ⟦ czs ⟧ ) (cute-cons-lem x (y ∷ ys) cyys xRyys) xyysRzs


cute-++ : ∀ {xs ys} → (cxs : Cute xs) → (cys : Cute ys) → ⟦ cxs ⟧ R ⟦ cys ⟧ → Cute (xs ⁺++⁺ ys)
cute-++ {x ∷ []} {y ∷ ys} cxs cys xsRys = cute-cons x (y ∷ ys) cys {!!}
cute-++ {x' ∷ x ∷ xs} {y ∷ ys} cxs cys xsRys = {!!}

-- In particular, thanks to reflexivity of R, doubling is a primitive thing we can do
-- to cute lists.
cute-double : {xs : List⁺ X} → Cute xs → Cute (xs ⁺++⁺ xs)
cute-double cxs = cute-++ cxs cxs reflexive

-- Repeat gives us monomial representing xⁿ.
-- If we can show that repeat is cute, then exponentiation will be its
-- crush.
-- EXCEPT: that's probably very hard. So let's go another way;
repeat⁺ : X → ℕ⁺ → List⁺ X
repeat⁺ x (suc zero , _) = x ∷ []
repeat⁺ x (suc (suc n) , _) = x ∷⁺ (repeat⁺ x (suc n , record {nonZero = tt}))

repeat-cute : ∀ x n → Cute (repeat⁺ x n)
repeat-cute x (suc zero , _) = cute-singleton x
repeat-cute x (suc (suc n) , _) = cute-cons x (repeat⁺ x (suc n , record { nonZero = tt }))
                                    (repeat-cute x (suc n , record { nonZero = tt })) {!!} -- this goal will likely be too hard to fill.
