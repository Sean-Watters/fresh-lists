{-# OPTIONS --safe --without-K #-}

open import Algebra.Structure.OICM

module Free.IdempotentCommutativeMonoid.Properties
  {X : Set} {_≈_ : X -> X -> Set} {_<_ : X -> X -> Set}
  (<-STO : IsPropStrictTotalOrder _≈_ _<_)
  where

open import Level renaming (suc to lsuc)
open import Algebra
open import Data.Product hiding (map)
open import Data.Sum hiding (map )
open import Data.Unit
open import Data.Empty
open import Data.Nat hiding (_<?_; compare) renaming (_<_ to _<ℕ_)
open import Data.Nat.Properties hiding (<-trans; <-asym; <-irrefl; _<?_)
open import Data.Nat.Induction
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

open import Function
open import Induction.WellFounded

open import Relation.Binary hiding (NonEmpty; StrictTotalOrder)
open import Relation.Binary.Isomorphism
open import Relation.Binary.PropositionalEquality hiding (isEquivalence)
open import Relation.Nullary hiding (Irrelevant)
open import Relation.Nullary.Decidable hiding (map)

open import Data.FreshList.InductiveInductive
open import Free.IdempotentCommutativeMonoid.Base <-STO



private
  -- Some more convenient names for the fields and subfields of the STO proof
  <-SPO    = IsPropStrictTotalOrder.isStrictPartialOrder <-STO
  ≈-Eq     = IsPropStrictTotalOrder.isEquivalence <-STO
  <-trans  = IsPropStrictTotalOrder.trans <-STO
  <-irrefl = IsStrictPartialOrder.irrefl <-SPO
  <-asym   = IsStrictPartialOrder.asym <-SPO
  <-resp-≈ = IsStrictPartialOrder.<-resp-≈ <-SPO
  ≈-refl   = IsEquivalence.refl ≈-Eq
  ≈-sym    = IsEquivalence.sym ≈-Eq
  ≈-trans  = IsEquivalence.trans ≈-Eq
  _<?_     = IsPropStrictTotalOrder._<?_ <-STO
  _≈?_     = IsPropStrictTotalOrder._≟_ <-STO
  compare  = IsPropStrictTotalOrder.compare <-STO
  open import Relation.Unary.Finiteness (record {Carrier = X; _≈_ = _≈_; isEquivalence = ≈-Eq})

-- Since < is transitive, it suffices to know that z < head to cons z,
cons-head-< : ∀ {x y} {xs : SortedList} {fx : x # xs} -> y < x -> All (y <_) (cons x xs fx)
cons-head-< {fx = fx} y<x = y<x ∷ all-map (<-trans y<x) (fresh→all fx)

-- Overload for membership to work with  ≈
_∈_ : X -> SortedList -> Set
x ∈ xs = Any (x ≈_) xs

infix 10 _∈_

_∉_ : X -> SortedList -> Set
x ∉ xs = ¬ (Any (x ≈_) xs)

_⊆_ : (xs ys : SortedList) -> Set
xs ⊆ ys = ∀ {a} -> a ∈ xs -> a ∈ ys

_⊈_ : (xs ys : SortedList) -> Set
xs ⊈ ys = ¬ (xs ⊆ ys)

_∈?_ : Decidable _∈_
x ∈? xs = any? (x ≈?_) xs

⊆-refl : { xs : SortedList } -> xs ⊆ xs
⊆-refl a∈xs = a∈xs

⊆-[]-initial : ∀ {xs} -> [] ⊆ xs
⊆-[]-initial ()

⊆-weaken : ∀ {x xs ys} {fx : x # xs} → (cons x xs fx) ⊆ ys → xs ⊆ ys
⊆-weaken sub a∈xs = sub (there a∈xs)

cons⊈[] : ∀ {x xs} {fx : x # xs} -> cons x xs fx ⊈ []
cons⊈[] {x} {xs} {fx} p with p (here ≈-refl)
... | ()

#→∉ : ∀ {x} {xs : SortedList} -> x # xs -> x ∉ xs
#→∉ {x} {cons y ys fy} x#xs x∈xs with fresh→all {xs = cons y ys fy} x#xs
#→∉ {x} {cons y ys fy} x#xs (here x≈y) | x<y ∷ pxs = <-irrefl x≈y x<y
#→∉ {x} {cons y ys fy} x#xs (there x∈xs) | x<y ∷ pxs = #→∉ (all→fresh pxs) x∈xs


-- Equivalence preserves freshness
≈-preserves-# : ∀ {x y} {xs : SortedList} -> x # xs -> x ≈ y -> y # xs
≈-preserves-# = WithEq.#-resp-≈ _<_ ≈-Eq (IsPropStrictTotalOrder.<-resp-≈ <-STO)

-- Equivalence preserves membership
≈-preserves-∈ : ∀ {a b} {xs : SortedList} -> a ∈ xs -> a ≈ b -> b ∈ xs
≈-preserves-∈ (here a≈x) a≈b = here (≈-trans (≈-sym a≈b) a≈x)
≈-preserves-∈ (there a∈xs) a≈b = there (≈-preserves-∈ a∈xs a≈b)

-- If ≈ preserves ∈, then it also preserves ∉
≈-preserves-∉ : ∀ {x y} {xs : SortedList} -> x ∉ xs -> x ≈ y -> y ∉ xs
≈-preserves-∉ a∉xs a≈b (here b≈x) = a∉xs (here (≈-trans a≈b b≈x))
≈-preserves-∉ a∉xs a≈b (there b∈xs) = a∉xs (there (≈-preserves-∈ b∈xs (≈-sym a≈b)))

-- If the equivalence relation is propositional, then membership for sorted lists is propositional,
-- because an element can only appear once.
∈-irrelevant : ∀ {a} {xs : SortedList} -> (∀ {x y} -> (u v : x ≈ y) -> u ≡ v) -> (p q : a ∈ xs) -> p ≡ q
∈-irrelevant {a} {cons x xs fx} ≈-irrelevant (here p) (here q) = cong here (≈-irrelevant p q)
∈-irrelevant {a} {cons x xs fx} ≈-irrelevant (here p) (there q) = ⊥-elim (#→∉ fx (≈-preserves-∈ q p))
∈-irrelevant {a} {cons x xs fx} ≈-irrelevant (there p) (here q) = ⊥-elim (#→∉ fx (≈-preserves-∈ p q))
∈-irrelevant {a} {cons x xs fx} ≈-irrelevant (there p) (there q) = cong there (∈-irrelevant ≈-irrelevant p q)

all<-irrefl : ∀ {x} {xs : SortedList} -> x ∈ xs -> All (x <_) xs -> ⊥
all<-irrefl (here px)  (qx ∷ qxs) = <-irrefl px qx
all<-irrefl (there pxs) (qx ∷ qxs) = all<-irrefl pxs qxs

all>-irrefl : ∀ {x} {xs : SortedList} -> x ∈ xs -> All (_< x) xs -> ⊥
all>-irrefl (here px)  (qx ∷ qxs) = <-irrefl (≈-sym px) qx
all>-irrefl (there pxs) (qx ∷ qxs) = all>-irrefl pxs qxs

all<-resp-≈ : ∀ {x y} {xs : SortedList} -> x ≈ y -> All (x <_) xs -> All (y <_) xs
all<-resp-≈ x≈y [] = []
all<-resp-≈ x≈y (px ∷ pxs) = proj₂ <-resp-≈ x≈y px ∷ (all<-resp-≈ x≈y pxs)

all>-resp-≈ : ∀ {x y} {xs : SortedList} -> x ≈ y -> All (_< x) xs -> All (_< y) xs
all>-resp-≈ x≈y [] = []
all>-resp-≈ x≈y (px ∷ pxs) = proj₁ <-resp-≈ x≈y px ∷ (all>-resp-≈ x≈y pxs)



all>-trans : ∀ {x y} {xs : SortedList} -> All (_< x) xs -> x < y -> All (_< y) xs
all>-trans [] x<y = []
all>-trans (x<a ∷ pas) a<y = <-trans x<a a<y ∷ all>-trans pas a<y

all<-trans : ∀ {x y} {xs : SortedList} -> x < y -> All (y <_) xs -> All (x <_) xs
all<-trans x<y [] = []
all<-trans x<y (y<a ∷ pas) = <-trans x<y y<a ∷ all<-trans x<y pas

---------------------------------
-- Equivalence of Sorted Lists --
---------------------------------

-- We lift ≈ pointwise
data _≈L_ : SortedList -> SortedList -> Set where
  [] : [] ≈L []
  cons : {x y : X} {xs ys : SortedList} {fx : x # xs} {fy : y # ys}
       -> x ≈ y -> xs ≈L ys -> (cons x xs fx) ≈L (cons y ys fy)

≈L-refl : { xs : SortedList } -> xs ≈L xs
≈L-refl {[]} = []
≈L-refl {cons x xs fx} = cons ≈-refl ≈L-refl

≈L-sym : {xs ys : SortedList} -> xs ≈L ys -> ys ≈L xs
≈L-sym [] = []
≈L-sym (cons x p) = cons (≈-sym x) (≈L-sym p)

≈L-trans : {xs ys zs : SortedList} -> xs ≈L ys -> ys ≈L zs -> xs ≈L zs
≈L-trans [] q = q
≈L-trans (cons x p) (cons y q) = cons (≈-trans x y) (≈L-trans p q)

≈L-prop : Irrelevant (_≈L_)
≈L-prop [] [] = refl
≈L-prop (cons x=y xs=ys) (cons x=y' xs=ys') = cong₂ cons (IsPropStrictTotalOrder.≈-prop <-STO x=y x=y') (≈L-prop xs=ys xs=ys')

isEquivalence : IsEquivalence _≈L_
IsEquivalence.refl isEquivalence = ≈L-refl
IsEquivalence.sym isEquivalence = ≈L-sym
IsEquivalence.trans isEquivalence = ≈L-trans

_≈?L_ : Decidable _≈L_
[] ≈?L [] = yes []
[] ≈?L cons y ys fy = no λ ()
cons x xs fx ≈?L [] = no λ ()
cons x xs fx ≈?L cons y ys fy with x ≈? y | xs ≈?L ys
... | yes p | yes q = yes (cons p q)
... | no ¬p | _ = no λ { (cons p q) → ¬p p}
... | _ | no ¬q = no λ { (cons p q) → ¬q q}

≡→≈L : {xs ys : SortedList} -> xs ≡ ys -> xs ≈L ys
≡→≈L refl = ≈L-refl

module ≈L-Reasoning where
  infix  3 _∎
  infixr 2 _≈⟨⟩_ step-≈ step-≈˘
  infix  1 begin_

  begin_ : {x y : SortedList} → x ≈L y → x ≈L y
  begin_ x≈y = x≈y

  _≈⟨⟩_ : ∀ (x {y} : SortedList) → x ≈L y → x ≈L y
  _ ≈⟨⟩ x≈y = x≈y

  step-≈ : ∀ (x {y z} : SortedList) → y ≈L z → x ≈L y → x ≈L z
  step-≈ _ y≈z x≈y = ≈L-trans x≈y y≈z

  step-≈˘ : ∀ (x {y z} : SortedList) → y ≈L z → y ≈L x → x ≈L z
  step-≈˘ _ y≈z y≈x = ≈L-trans (≈L-sym y≈x) y≈z

  _∎ : ∀ (x : SortedList) → x ≈L x
  _∎ _ = ≈L-refl

  syntax step-≈  x y≈z x≈y = x ≈⟨  x≈y ⟩ y≈z
  syntax step-≈˘ x y≈z y≈x = x ≈˘⟨ y≈x ⟩ y≈z

nil≉cons : {x : X} {xs : SortedList} {x#xs : x # xs} → ¬ ([] ≈L cons x xs x#xs)
nil≉cons ()


------------------------
-- Preservation of ≈L --
------------------------

≈L-preserves-∈ : ∀ {a} {xs ys : SortedList} -> a ∈ xs -> xs ≈L ys -> a ∈ ys
≈L-preserves-∈ (here a≈x) (cons x≈y xs≈ys) = here (≈-trans a≈x x≈y)
≈L-preserves-∈ (there a∈xs) (cons x≈y xs≈ys) = there (≈L-preserves-∈ a∈xs xs≈ys)

≈L-preserves-∉ : ∀ {a} {xs ys : SortedList} -> a ∉ xs -> xs ≈L ys -> a ∉ ys
≈L-preserves-∉ a∉xs xs≈ys a∈ys = a∉xs (≈L-preserves-∈ a∈ys (≈L-sym xs≈ys))

≈L-preserves-length : {xs ys : SortedList} -> xs ≈L ys -> length xs ≡ length ys
≈L-preserves-length [] = refl
≈L-preserves-length (cons x≈y xs≈ys) = cong suc (≈L-preserves-length xs≈ys)

------------------------------
-- Properties of All and ≈L --
------------------------------

-- If P respects ≈, then All P respects ≈ and ≈L
all-resp-≈L : ∀ {xs ys : SortedList} {P : X -> Set}
            → (∀ {a b} → a ≈ b → P a → P b) --todo: this almost definitely has a name
            → xs ≈L ys
            → All P xs → All P ys
all-resp-≈L f [] pxs = pxs
all-resp-≈L f (cons x≈y xs≈ys) (px ∷ pxs) = f x≈y px ∷ all-resp-≈L f xs≈ys pxs

-- ----------------------------
-- -- SortedList Extensionality --
-- ----------------------------

-- Something which is smaller than the head cannot appear elsewhere in the list.
ext-lem : {a x : X} {xs : SortedList} {fx : x # xs} -> a < x -> a ∉ (cons x xs fx)
ext-lem a<x (here a≈x) = <-irrefl a≈x a<x
ext-lem {a} {x} {xs} {fx} a<x (there a∈xs) with fresh→all fx
... | px ∷ pxs = ext-lem (<-trans a<x px) a∈xs

-- Two sorted lists with the same elements are the same list.
extensionality : (xs ys : SortedList)
                       -> (∀ x -> ((x ∈ xs) -> (x ∈ ys)) × ((x ∈ ys) -> (x ∈ xs)))
                       -> xs ≈L ys
extensionality [] [] p = []
extensionality [] (cons x xs fx) p with (proj₂ (p x)) (here ≈-refl)
... | ()
extensionality (cons x xs fx) [] p with (proj₁ (p x)) (here ≈-refl)
... | ()
extensionality (cons x xs fx) (cons y ys fy) p with compare x y
... | tri≈ ¬lt x≈y ¬gt = cons x≈y (extensionality xs ys (λ z → f z , g z)) where

  f : ∀ z -> z ∈ xs -> z ∈ ys
  f z z∈xs with proj₁ (p z) (there z∈xs)
  ... | here z≈y = ⊥-elim (all<-irrefl z∈xs (fresh→all (≈-preserves-# fx (≈-trans x≈y (≈-sym z≈y)))))
  ... | there z∈ys = z∈ys

  g : ∀ z -> z ∈ ys -> z ∈ xs
  g z z∈ys with proj₂ (p z) (there z∈ys)
  ... | here z≈x = ⊥-elim (all<-irrefl z∈ys (fresh→all (≈-preserves-# fy (≈-trans (≈-sym x≈y) (≈-sym z≈x)))))
  ... | there z∈xs = z∈xs
... | tri< lt ¬eq ¬gt = ⊥-elim (ext-lem (lt) (proj₁ (p x) (here ≈-refl)))
... | tri> ¬lt ¬eq gt = ⊥-elim (ext-lem (gt) (proj₂ (p y) (here ≈-refl)))


-----------------------
-- Length Properties --
-----------------------

weaken-∉ : ∀ {x a} {as : SortedList} {fa : a # as} -> x ∉ (cons a as fa) -> x ∉ as
weaken-∉ x (here x₁) = x (there (here x₁))
weaken-∉ x (there x₁) = x (there (there x₁))

strengthen-∉ : ∀ {x a} {as : SortedList} {fa : a # as} -> ¬ (x ≈ a) -> x ∉ as -> x ∉ (cons a as fa)
strengthen-∉ x≉a x∉as (here x≈a) = x≉a x≈a
strengthen-∉ x≉a x∉as (there x∈as) = x∉as x∈as

----------------------
-- Union Properties --
----------------------

union∈ : ∀ {a} {xs ys : SortedList} -> (p : Acc _<ℕ_ (length xs + length ys)) → a ∈ (union xs ys p) -> a ∈ xs ⊎ a ∈ ys
union∈ {a} {[]} {ys} p a∈ys = inj₂ a∈ys
union∈ {a} {cons x xs x#xs} {[]} p a∈xs = inj₁ a∈xs
union∈ {a} {cons x xs x#xs} {cons y ys y#ys} (acc rs) a∈xs∪ys with compare x y
union∈ {a} {cons x xs x#xs} {cons y ys y#ys} (acc rs) (here a≈x) | tri< x<y ¬x≈y ¬y<x = inj₁ (here a≈x)
union∈ {a} {cons x xs x#xs} {cons y ys y#ys} (acc rs) (there a∈xs∪yys) | tri< x<y ¬x≈y ¬y<x with union∈ {a} {xs} {cons y ys y#ys} _ a∈xs∪yys
... | inj₁ a∈xs = inj₁ (there a∈xs)
... | inj₂ a∈yys = inj₂ a∈yys
union∈ {a} {cons x xs x#xs} {cons y ys y#ys} (acc rs) (here a≈x) | tri≈ ¬x<y x≈y ¬y<x = inj₁ (here a≈x)
union∈ {a} {cons x xs x#xs} {cons y ys y#ys} (acc rs) (there a∈xs∪ys) | tri≈ ¬x<y x≈y ¬y<x with union∈ {a} {xs} {ys} _ a∈xs∪ys
... | inj₁ a∈xs = inj₁ (there a∈xs)
... | inj₂ a∈ys = inj₂ (there a∈ys)
union∈ {a} {cons x xs x#xs} {cons y ys y#ys} (acc rs) (here a≈y) | tri> ¬x<y ¬x≈y y<x = inj₂ (here a≈y)
union∈ {a} {cons x xs x#xs} {cons y ys y#ys} (acc rs) (there a∈xxs∪ys) | tri> ¬x<y ¬x≈y y<x with union∈ {a} {cons x xs x#xs} {ys} _ a∈xxs∪ys
... | inj₁ a∈xxs = inj₁ a∈xxs
... | inj₂ a∈ys = inj₂ (there a∈ys)

∪∈ : ∀ {a} {xs ys : SortedList} -> a ∈ (xs ∪ ys) -> a ∈ xs ⊎ a ∈ ys
∪∈ {a} {xs} {ys} = union∈ (<-wellFounded (length xs + length ys))

∉∪ : ∀ {a} {xs ys : SortedList} -> a ∉ xs -> a ∉ ys -> a ∉ (xs ∪ ys)
∉∪ {a} {[]} {ys} a∉xs a∉ys = a∉ys
∉∪ {a} {cons x xs fx} {ys} a∉xs a∉ys a∈∪ with ∪∈ a∈∪
... | inj₁ a∈xs = a∉xs a∈xs
... | inj₂ a∈ys = a∉ys a∈ys


∈unionˡ : ∀ {a} {xs : SortedList} -> a ∈ xs -> (ys : SortedList) -> (p : Acc _<ℕ_ (length xs + length ys)) -> a ∈ (union xs ys p)
∈unionˡ {a} {cons x xs x#xs} (here a≈x) [] p = here a≈x
∈unionˡ {a} {cons x xs x#xs} (here a≈x) (cons y ys y#ys) (acc rs) with compare x y
... | tri< _ _ _ = here a≈x
... | tri≈ _ _ _ = here a≈x
... | tri> _ _ _ = there (∈unionˡ {a} {cons x xs x#xs} (here a≈x) ys _)
∈unionˡ {a} {cons x xs x#xs} (there a∈xs) [] p = there a∈xs
∈unionˡ {a} {cons x xs x#xs} (there a∈xs) (cons y ys y#ys) (acc rs) with compare x y
... | tri< _ _ _ = there (∈unionˡ {a} {xs} a∈xs (cons y ys y#ys) _)
... | tri≈ _ _ _ = there (∈unionˡ {a} {xs} a∈xs ys _)
... | tri> _ _ _ = there (∈unionˡ {a} {cons x xs x#xs} (there a∈xs) ys _)

∈unionʳ : ∀ {a} {ys : SortedList} -> (xs : SortedList) → a ∈ ys -> (p : Acc _<ℕ_ (length xs + length ys)) -> a ∈ (union xs ys p)
∈unionʳ {a} {ys} [] a∈ys p = a∈ys
∈unionʳ {a} {cons y ys y#ys} (cons x xs x#xs) a∈yys (acc rs) with compare x y
... | tri< _ _ _ = there (∈unionʳ {a} {cons y ys y#ys} xs a∈yys _)
∈unionʳ {a} {cons y ys y#ys} (cons x xs x#xs) (here a≈y) (acc rs) | tri≈ _ x≈y _ = here (≈-trans a≈y (≈-sym x≈y))
∈unionʳ {a} {cons y ys y#ys} (cons x xs x#xs) (there a∈ys) (acc rs) | tri≈ _ _ _ = there (∈unionʳ {a} {ys} xs a∈ys _)
∈unionʳ {a} {cons y ys y#ys} (cons x xs x#xs) (here a≈y) (acc rs) | tri> _ _ _ = here a≈y
∈unionʳ {a} {cons y ys y#ys} (cons x xs x#xs) (there a∈ys) (acc rs) | tri> _ _ _ = there (∈unionʳ {a} {ys} (cons x xs x#xs) a∈ys _)

∈∪ˡ : ∀ {a} {xs : SortedList} -> a ∈ xs -> (ys : SortedList) -> a ∈ (xs ∪ ys)
∈∪ˡ {a} {xs} a∈xs ys = ∈unionˡ a∈xs ys (<-wellFounded (length xs + length ys))

∈∪ʳ : ∀ {x} {ys : SortedList} -> (xs : SortedList) -> x ∈ ys -> x ∈ (xs ∪ ys)
∈∪ʳ {a} {ys} xs a∈ys = ∈unionʳ {a} {ys} xs a∈ys (<-wellFounded (length xs + length ys))

∈∪ : ∀ {a} {xs ys : SortedList} -> (a ∈ xs) ⊎ (a ∈ ys) → a ∈ (xs ∪ ys)
∈∪ {xs = xs} {ys} (inj₁ a∈xs) = ∈∪ˡ a∈xs ys
∈∪ {xs = xs} {ys} (inj₂ a∈ys) = ∈∪ʳ xs a∈ys

∉∪ˡ : ∀ {a} {xs ys : SortedList} -> a ∉ (xs ∪ ys) -> a ∉ xs
∉∪ˡ {ys = ys} ¬p a∈xs = ¬p (∈∪ˡ a∈xs ys)

∉∪ʳ : ∀ {a} {xs ys : SortedList} -> a ∉ (xs ∪ ys) -> a ∉ ys
∉∪ʳ {xs = xs} ¬p a∈ys = ¬p (∈∪ʳ xs a∈ys)

∪-idʳ : (xs : SortedList) -> (xs ∪ []) ≡ xs
∪-idʳ [] = refl
∪-idʳ (cons x xs fx) rewrite ∪-idʳ xs = refl

∪-id : Identity _≈L_ [] _∪_
proj₁ ∪-id = λ x → ≈L-refl
proj₂ ∪-id = λ x → ≡→≈L (∪-idʳ x)

∪-comm : ( xs ys : SortedList ) -> (xs ∪ ys) ≈L (ys ∪ xs)
∪-comm xs ys = extensionality (xs ∪ ys) (ys ∪ xs) (λ x → f xs ys x , f ys xs x)
  where
    f : (xs ys : SortedList) → (x : X) → x ∈ (xs ∪ ys) → x ∈ (ys ∪ xs)
    f xs ys x x∈xs∪ys with ∪∈ x∈xs∪ys
    ... | inj₁ x∈xs = ∈∪ʳ ys x∈xs
    ... | inj₂ x∈ys = ∈∪ˡ x∈ys xs

∪-idempotent : Idempotent _≈L_ _∪_
∪-idempotent xs = extensionality (xs ∪ xs) xs (λ x → (λ x∈xs∪xs → [ id , id ]′ (∪∈ x∈xs∪xs) ) , ∈∪ʳ xs)

∪-preserves-≈L : {xs xs' ys ys' : SortedList} -> xs ≈L xs' -> ys ≈L ys' -> (xs ∪ ys) ≈L (xs' ∪ ys')
∪-preserves-≈L {xs} {xs'} {ys} {ys'} xs=xs' ys=ys' = extensionality _ _ λ x → f x xs=xs' ys=ys' , f x (≈L-sym xs=xs') (≈L-sym ys=ys')
  where
    f : (x : X) → {xs xs' ys ys' : SortedList} -> xs ≈L xs' -> ys ≈L ys' → x ∈ (xs ∪ ys) → x ∈ (xs' ∪ ys')
    f x {xs} {xs'} {ys} {ys'} xs=xs' ys=ys' x∈xs∪xs = [ (λ x∈xs → ∈∪ˡ (≈L-preserves-∈ x∈xs xs=xs') ys') , (λ x∈ys → ∈∪ʳ xs' (≈L-preserves-∈ x∈ys ys=ys')) ]′ (∪∈ x∈xs∪xs)

∪-cancelˡ : {xs ys : SortedList} -> xs ≈L ys -> (xs ∪ ys) ≈L xs
∪-cancelˡ {xs} {ys} xs=ys = begin
  xs ∪ ys
    ≈⟨ ∪-preserves-≈L (≈L-refl {xs}) (≈L-sym xs=ys) ⟩
  xs ∪ xs
    ≈⟨ ∪-idempotent xs ⟩
  xs
    ∎ where open ≈L-Reasoning

∪-assoc : (xs ys zs : SortedList) -> ((xs ∪ ys) ∪ zs) ≈L (xs ∪ (ys ∪ zs))
∪-assoc xs ys zs = extensionality ((xs ∪ ys) ∪ zs) (xs ∪ (ys ∪ zs)) (λ x → f x , g x)
  where
    f : (x : X) → (x ∈ ((xs ∪ ys) ∪ zs) → x ∈ (xs ∪ (ys ∪ zs)))
    f x x∈xs∪ys∪zs with ∪∈ {xs = xs ∪ ys} x∈xs∪ys∪zs
    f x x∈xs∪ys∪zs | inj₁ x∈xs∪ys with ∪∈ {xs = xs} x∈xs∪ys
    ... | inj₁ x∈xs = ∈∪ˡ x∈xs (ys ∪ zs)
    ... | inj₂ x∈ys = ∈∪ʳ xs (∈∪ˡ x∈ys zs)
    f x x∈xs∪ys∪zs | inj₂ x∈zs = ∈∪ʳ xs (∈∪ʳ ys x∈zs)

    g : (x : X) → (x ∈ (xs ∪ (ys ∪ zs)) → x ∈ ((xs ∪ ys) ∪ zs))
    g x x∈xs∪ys∪zs with ∪∈ {xs = xs} x∈xs∪ys∪zs
    g x x∈xs∪ys∪zs | inj₁ x∈xs = ∈∪ˡ (∈∪ˡ x∈xs ys) zs
    g x x∈xs∪ys∪zs | inj₂ x∈ys∪zs with ∪∈ {xs = ys} x∈ys∪zs
    ... | inj₁ x∈ys = ∈∪ˡ (∈∪ʳ xs x∈ys) zs
    ... | inj₂ x∈zs = ∈∪ʳ (xs ∪ ys) x∈zs

-----------------------
-- Insert Properties --
-----------------------

insert-consview : ∀ {x} {xs : SortedList} -> (fx : x # xs) -> insert x xs ≡ cons x xs fx
insert-consview {xs = []} [] = refl
insert-consview {x} {xs = cons y ys y#ys} x#xs with compare x y
... | tri< _ _ _ = WithIrr.cons-cong _<_ (IsPropStrictTotalOrder.<-prop <-STO) refl refl
insert-consview {x} {cons y ys y#ys} (x<y ∷ x#xs) | tri≈ _ x≈y _ = ⊥-elim (<-irrefl x≈y x<y)
insert-consview {x} {cons y ys y#ys} (x<y ∷ x#ys) | tri> _ _ y<x = ⊥-elim (<-irrefl (≈-refl {x}) (<-trans x<y y<x))

∈insertˡ' : {a x : X} {xs : SortedList} → a ≈ x → a ∈ (insert x xs)
∈insertˡ' {xs = xs} p = ∈∪ˡ (here p) xs

∈insertˡ : (x : X) (xs : SortedList) → x ∈ (insert x xs)
∈insertˡ x xs = ∈∪ˡ (here ≈-refl) xs

∈insertʳ : {a x : X} {xs : SortedList} → a ∈ xs → a ∈ (insert x xs)
∈insertʳ {x = x} = ∈∪ʳ (cons x [] [])

insert∈ : {a x : X} {xs : SortedList} → a ∈ (insert x xs) → a ≈ x ⊎ a ∈ xs
insert∈ {a} {x} {xs} p with ∪∈ {a} {cons x [] []} {xs} p
... | inj₁ (here p) = inj₁ p
... | inj₂ p = inj₂ p

----------------------------
-- Lexicographic Ordering --
----------------------------

-- lexicographic strict less-than relation on lists
data _<-lex_ : SortedList → SortedList → Set where
  [] : ∀ {x xs fx} → [] <-lex (cons x xs fx)
  here : ∀ {x xs fx y ys fy} → x < y → (cons x xs fx) <-lex (cons y ys fy)
  there : ∀ {x xs fx y ys fy} → x ≈ y → xs <-lex ys → (cons x xs fx) <-lex (cons y ys fy)

<-lex-trans : ∀ {xs ys zs} → xs <-lex ys → ys <-lex zs → xs <-lex zs
<-lex-trans [] (here y<z) = []
<-lex-trans [] (there y≈z ys<zs) = []
<-lex-trans (here x<y) (here y<z) = here (<-trans x<y y<z)
<-lex-trans (here x<y) (there y≈z ys<zs) = here (proj₁ <-resp-≈ y≈z x<y)
<-lex-trans (there x≈y xs<ys) (here y<z) = here (proj₂ <-resp-≈ (≈-sym x≈y) y<z  )
<-lex-trans (there x≈y xs<ys) (there y≈z ys<zs) = there (≈-trans x≈y y≈z) (<-lex-trans xs<ys ys<zs)

compareL : Trichotomous _≈L_ _<-lex_
compareL [] [] = tri≈ (λ {()}) [] (λ {()})
compareL [] (cons y ys fy) = tri< [] (λ {()}) λ {()}
compareL (cons x xs fx) [] = tri> (λ {()}) (λ {()}) []
compareL (cons x xs fx) (cons y ys fy) with compare x y
... | tri< x<y x≉y x≯y = tri< (here x<y) (λ {(cons x≈y _) → x≉y x≈y }) λ { (here x>y) → x≯y x>y ; (there y≈x _) → x≉y (≈-sym y≈x)}
... | tri> x≮y x≉y x>y = tri> (λ { (here x<y) → x≮y x<y ; (there x≈y _) → x≉y x≈y}) (λ { (cons x≈y _) → x≉y x≈y}) (here x>y)
... | tri≈ x≮y x≈y x≯y with compareL xs ys
... | tri< xs<ys xs≉ys xs≯ys = tri< (there x≈y xs<ys) (λ { (cons _ xs≈ys) → xs≉ys xs≈ys}) λ { (here y<x) → x≯y y<x ; (there _ ys<xs) → xs≯ys ys<xs}
... | tri≈ xs≮ys xs≈ys xs≯ys = tri≈ (λ { (here x<y) → x≮y x<y ; (there _ xs<ys) → xs≮ys xs<ys}) (cons x≈y xs≈ys) λ { (here y<x) → x≯y y<x ; (there _ ys<xs) → xs≯ys ys<xs}
... | tri> xs≮ys xs≉ys xs>ys = tri> (λ { (here x<y) → x≮y x<y ; (there _ xs<ys) → xs≮ys xs<ys}) (λ { (cons _ xs≈ys) → xs≉ys xs≈ys}) (there (≈-sym x≈y) xs>ys)

<L-prop : Irrelevant _<-lex_
<L-prop [] [] = refl
<L-prop (here x<y) (here x<y') = cong here (IsPropStrictTotalOrder.<-prop <-STO x<y x<y')
<L-prop (here x<y) (there x=y xs<ys) = ⊥-elim (<-irrefl x=y x<y)
<L-prop (there x=y xs<ys) (here x<y) = ⊥-elim (<-irrefl x=y x<y)
<L-prop (there x=y xs<ys) (there x=y' xs<ys') = cong₂ there (IsPropStrictTotalOrder.≈-prop <-STO x=y x=y') (<L-prop xs<ys xs<ys')

<-lex-STO : IsPropStrictTotalOrder _≈L_ _<-lex_
IsStrictTotalOrder.isEquivalence (IsPropStrictTotalOrder.isSTO <-lex-STO) = isEquivalence
IsStrictTotalOrder.trans (IsPropStrictTotalOrder.isSTO <-lex-STO) = <-lex-trans
IsStrictTotalOrder.compare (IsPropStrictTotalOrder.isSTO <-lex-STO) = compareL
IsPropStrictTotalOrder.≈-prop <-lex-STO = ≈L-prop
IsPropStrictTotalOrder.<-prop <-lex-STO = <L-prop

<L-trans = <-lex-trans
_<L_ = _<-lex_
<L-STO = <-lex-STO

-----------------------------------
-- Idempotent Commutative Monoid --
-----------------------------------

isSemigroup : IsSemigroup _≈L_ _∪_
IsMagma.isEquivalence (IsSemigroup.isMagma isSemigroup) = isEquivalence
IsMagma.∙-cong (IsSemigroup.isMagma isSemigroup) = ∪-preserves-≈L
IsSemigroup.assoc isSemigroup = ∪-assoc

isMonoid : IsMonoid _≈L_ _∪_ []
IsMonoid.isSemigroup isMonoid = isSemigroup
IsMonoid.identity isMonoid = ∪-id

isCommMonoid : IsCommutativeMonoid _≈L_ _∪_ []
IsCommutativeMonoid.isMonoid isCommMonoid = isMonoid
IsCommutativeMonoid.comm isCommMonoid = ∪-comm

isIdemCommMonoid : IsIdempotentCommutativeMonoid _≈L_ _∪_ []
IsIdempotentCommutativeMonoid.isCommutativeMonoid isIdemCommMonoid = isCommMonoid
IsIdempotentCommutativeMonoid.idem isIdemCommMonoid = ∪-idempotent

isOICM : IsOrderedIdempotentCommutativeMonoid _≈L_ _<-lex_ _∪_ []
IsOrderedIdempotentCommutativeMonoid.isICM isOICM = isIdemCommMonoid
IsOrderedIdempotentCommutativeMonoid.isSTO isOICM = <-lex-STO


-----------------------
-- Properties of _∩_ --
-----------------------

-- Left elimination principle for membership in an intersection
∈∩ˡ : {a : X} {xs ys : SortedList} → a ∈ (xs ∩ ys) → a ∈ xs
∈∩ˡ {a} {cons x xs x#xs} {ys} p with any? (x ≈?_) ys
... | no ¬q = there $ ∈∩ˡ {a} {xs} {ys} p
... | yes q with insert∈ {a} {x} {xs ∩ ys} p
... | inj₁ r = here r
... | inj₂ r = there $ ∈∩ˡ {a} {xs} {ys} r

-- Right elimination principle for membership in an intersection
∈∩ʳ : {a : X} {xs ys : SortedList} → a ∈ (xs ∩ ys) → a ∈ ys
∈∩ʳ {a} {cons x xs x#xs} {ys} p with any? (x ≈?_) ys
... | no ¬q = ∈∩ʳ {a} {xs} {ys} p
... | yes q with insert∈ {a} {x} {xs ∩ ys} p
... | inj₁ r = ≈-preserves-∈ q (≈-sym r)
... | inj₂ r = ∈∩ʳ {a} {xs} {ys} r

-- Introduction principle for membership in an intersection
∩∈ : {a : X} {xs ys : SortedList} → a ∈ xs → a ∈ ys → a ∈ (xs ∩ ys)
∩∈ {a} {cons x xs x#xs} {ys} p q with any? (x ≈?_) ys
∩∈ {a} {cons x xs x#xs} {ys} (here a≈x) q | yes u = ∈insertˡ' {xs = xs ∩ ys} a≈x
∩∈ {a} {cons x xs x#xs} {ys} (there p) q | yes u = ∈insertʳ (∩∈ p q)
∩∈ {a} {cons x xs x#xs} {ys} (here a≈x) q | no ¬u = ⊥-elim (¬u (≈-preserves-∈ q a≈x))
∩∈ {a} {cons x xs x#xs} {ys} (there p) q | no ¬u = ∩∈ p q

∩-assoc : Associative _≈L_ _∩_
∩-assoc xs ys zs = extensionality _ _ λ x → f x , g x where
  f : (a : X) → a ∈ ((xs ∩ ys) ∩ zs) → a ∈ (xs ∩ (ys ∩ zs))
  f a p = ∩∈ {a} {xs} {ys ∩ zs} (∈∩ˡ (∈∩ˡ p)) (∩∈ {a} {ys} {zs} (∈∩ʳ {a} {xs} {ys} (∈∩ˡ p)) (∈∩ʳ {xs = xs ∩ ys} p))

  g : (a : X) → a ∈ (xs ∩ (ys ∩ zs)) → a ∈ ((xs ∩ ys) ∩ zs)
  g a p = ∩∈ {a} {xs ∩ ys} {zs} (∩∈ {a} {xs} {ys} (∈∩ˡ p) (∈∩ˡ (∈∩ʳ {a} {xs} {ys ∩ zs} p))) (∈∩ʳ {a} {ys} {zs} (∈∩ʳ {a} {xs} {ys ∩ zs} p))

∩-comm : Commutative _≈L_ _∩_
∩-comm xs ys = extensionality _ _ λ a → f a xs ys , f a ys xs where
  f : (a : X) (xs ys : SortedList) → a ∈ (xs ∩ ys) → a ∈ (ys ∩ xs)
  f a xs ys p = ∩∈ {a} {ys} {xs} (∈∩ʳ {a} {xs} p) (∈∩ˡ p)

∩-preserves-≈L : ∀ {x y u v} → x ≈L y → u ≈L v → (x ∩ u) ≈L (y ∩ v)
∩-preserves-≈L {xs} {ys} {us} {vs} p q = extensionality (xs ∩ us) (ys ∩ vs) λ x → f {x} p q , f {x} (≈L-sym p) (≈L-sym q) where
  f : ∀ {a xs us ys vs} → xs ≈L ys → us ≈L vs → a ∈ (xs ∩ us) → a ∈ (ys ∩ vs)
  f {a} {xs} {us} {ys} {vs} p q r = ∩∈ {a} {ys} {vs} (≈L-preserves-∈ (∈∩ˡ r) p) (≈L-preserves-∈ (∈∩ʳ {xs = xs} r) q)

∩-annihilatesˡ : LeftZero _≈L_ [] _∩_
∩-annihilatesˡ _ = []

∩-annihilatesʳ : RightZero _≈L_ [] _∩_
∩-annihilatesʳ [] = []
∩-annihilatesʳ (cons x xs x#xs) = ∩-annihilatesʳ xs

∩-isSemigroup : IsSemigroup _≈L_ _∩_
IsMagma.isEquivalence (IsSemigroup.isMagma ∩-isSemigroup) = isEquivalence
IsMagma.∙-cong (IsSemigroup.isMagma ∩-isSemigroup) = ∩-preserves-≈L
IsSemigroup.assoc ∩-isSemigroup = ∩-assoc

-- if there exists an element which is not in xs, then xs cannot be the unit of ∩
∩-id-lem : (xs : SortedList) → (∃[ x ] x ∉ xs) → ¬ (LeftIdentity _≈L_ xs _∩_)
∩-id-lem xs (x , x∉xs) id = x∉xs (∈∩ˡ (≈L-preserves-∈ (∈insertˡ x xs) (≈L-sym (id (insert x xs)))))

-- _∩_ has a unit iff the carrier set is finite (ie, enumerable)
module _ where
  open import Data.List as L
  open import Data.List.Membership.Setoid as L using ()
  open import Data.List.Relation.Unary.Any
  _∈'_ = L._∈_ (record { Carrier = X ; _≈_ = _≈_ ; isEquivalence = ≈-Eq })

  ∩-idˡ→X-fin : (ε : List X) → LeftIdentity _≈L_ (insertion-sort ε) _∩_ → is-enumeration ε
  ∩-idˡ→X-fin xs id = {!!}

  ∩-idʳ→X-fin : (ε : List X) → RightIdentity _≈L_(insertion-sort ε) _∩_ → is-enumeration ε
  ∩-idʳ→X-fin xs id = {!!}

  X-fin→∩-idˡ : (ε : List X) → is-enumeration ε → LeftIdentity _≈L_ (insertion-sort ε) _∩_
  X-fin→∩-idˡ xs isEnum = {!!}

  X-fin→∩-idʳ : (ε : List X) → is-enumeration ε → RightIdentity _≈L_ (insertion-sort ε) _∩_
  X-fin→∩-idʳ xs isEnum = {!!}


----------------------------------------
-- Properties of _∩_ and _∪_ together --
----------------------------------------

∩-distrib-∪ˡ : _DistributesOverˡ_ _≈L_ _∩_ _∪_
∩-distrib-∪ˡ xs ys zs = extensionality _ _ λ x → f x , g x where
  f : (a : X) → a ∈ (xs ∩ (ys ∪ zs)) → a ∈ ((xs ∩ ys) ∪ (xs ∩ zs))
  f a p with ∪∈ {a} {ys} {zs} (∈∩ʳ {a} {xs} {ys ∪ zs} p)
  ... | inj₁ a∈ys = ∈∪ˡ {a} {xs ∩ ys} (∩∈ {a} {xs} {ys} (∈∩ˡ p) a∈ys) (xs ∩ zs)
  ... | inj₂ a∈zs = ∈∪ʳ {a} {xs ∩ zs} (xs ∩ ys) (∩∈ {a} {xs} {zs} (∈∩ˡ p) a∈zs)

  g : (a : X) → a ∈ ((xs ∩ ys) ∪ (xs ∩ zs)) → a ∈ (xs ∩ (ys ∪ zs))
  g a p with ∪∈ {a} {xs ∩ ys} {xs ∩ zs} p
  ... | inj₁ q = ∩∈ {a} {xs} {ys ∪ zs} (∈∩ˡ q) (∈∪ˡ (∈∩ʳ {a} {xs} {ys} q) zs)
  ... | inj₂ q = ∩∈ {a} {xs} {ys ∪ zs} (∈∩ˡ q) (∈∪ʳ ys (∈∩ʳ {a} {xs} {zs} q))

∩-distrib-∪ʳ : _DistributesOverʳ_ _≈L_ _∩_ _∪_
∩-distrib-∪ʳ xs ys zs = extensionality _ _ λ x → f x , g x where
  f : (x : X) → x ∈ ((ys ∪ zs) ∩ xs) → x ∈ ((ys ∩ xs) ∪ (zs ∩ xs))
  f = {!!}

  g : (x : X) → x ∈ ((ys ∩ xs) ∪ (zs ∩ xs)) → x ∈ ((ys ∪ zs) ∩ xs)
  g = {!!}

isPreSemiring : IsSemiringWithoutOne _≈L_ _∪_ _∩_ []
IsSemiringWithoutOne.+-isCommutativeMonoid isPreSemiring = isCommMonoid
IsSemiringWithoutOne.*-cong isPreSemiring = ∩-preserves-≈L
IsSemiringWithoutOne.*-assoc isPreSemiring = ∩-assoc
IsSemiringWithoutOne.distrib isPreSemiring = ∩-distrib-∪ˡ , ∩-distrib-∪ʳ
IsSemiringWithoutOne.zero isPreSemiring = ∩-annihilatesˡ , ∩-annihilatesʳ

-- TODO: isCommutativePreSemiring

-------------------------------------------------
-- Properties of _∩_ with a Finite Carrier Set --
-------------------------------------------------

module WithFinCarrier (isEnum : Enumerated) where
  ∩-Unit : SortedList
  ∩-Unit = insertion-sort (proj₁ isEnum)

  ∩-idˡ : LeftIdentity _≈L_ ∩-Unit _∩_
  ∩-idˡ = X-fin→∩-idˡ (proj₁ isEnum) (proj₂ isEnum)

  ∩-idʳ : RightIdentity _≈L_ ∩-Unit _∩_
  ∩-idʳ = X-fin→∩-idʳ (proj₁ isEnum) (proj₂ isEnum)

  isSemiring : IsSemiring _≈L_ _∪_ _∩_ [] ∩-Unit
  IsSemiringWithoutAnnihilatingZero.+-isCommutativeMonoid (IsSemiring.isSemiringWithoutAnnihilatingZero isSemiring) = isCommMonoid
  IsSemiringWithoutAnnihilatingZero.*-cong (IsSemiring.isSemiringWithoutAnnihilatingZero isSemiring) = ∩-preserves-≈L
  IsSemiringWithoutAnnihilatingZero.*-assoc (IsSemiring.isSemiringWithoutAnnihilatingZero isSemiring) = ∩-assoc
  IsSemiringWithoutAnnihilatingZero.*-identity (IsSemiring.isSemiringWithoutAnnihilatingZero isSemiring) = ∩-idˡ , ∩-idʳ
  IsSemiringWithoutAnnihilatingZero.distrib (IsSemiring.isSemiringWithoutAnnihilatingZero isSemiring) = ∩-distrib-∪ˡ , ∩-distrib-∪ʳ
  IsSemiring.zero isSemiring = ∩-annihilatesˡ , ∩-annihilatesʳ

  isCommSemiring : IsCommutativeSemiring _≈L_ _∪_ _∩_ [] ∩-Unit
  IsCommutativeSemiring.isSemiring isCommSemiring = isSemiring
  IsCommutativeSemiring.*-comm isCommSemiring = ∩-comm

---------------------
-- Properties of ⊆ --
---------------------

⊆-isDTO : {!!}
⊆-isDTO = {!!}

⊆-isLattice : {!!}
⊆-isLattice = {!!}
