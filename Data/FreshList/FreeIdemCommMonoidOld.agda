{-# OPTIONS --safe --without-K #-}


open import Level renaming (suc to lsuc)
open import Algebra
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit
open import Data.Empty
open import Data.Nat hiding (_<_; _<?_; compare)
open import Data.Nat.Properties hiding (<-trans; <-asym; <-irrefl; _<?_)

open import Function

open import Relation.Binary hiding (NonEmpty; StrictTotalOrder)
open import Relation.Binary.PropositionalEquality hiding (isEquivalence)
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)

open import Data.FreshList hiding (map)
open import Algebra.Structure.OICM

-- Given a set X, and a decidable strict total order _<_ on X, we can form the type of
-- lists of X's which are sorted according to _<_
module Data.FreshList.FreeIdemCommMonoidOld
  {X : Set} {_≈_ : X -> X -> Set} {_<_ : X -> X -> Set}
  (<-STO : IsStrictTotalOrder _≈_ _<_)
  where

-- Some more convenient names for the fields and subfields of the STO proof
<-SPO    = IsStrictTotalOrder.isStrictPartialOrder <-STO
≈-Eq     = IsStrictTotalOrder.isEquivalence <-STO
<-trans  = IsStrictTotalOrder.trans <-STO
<-irrefl = IsStrictPartialOrder.irrefl <-SPO
<-asym   = IsStrictPartialOrder.asym <-SPO
<-resp-≈ = IsStrictPartialOrder.<-resp-≈ <-SPO
≈-refl   = IsEquivalence.refl ≈-Eq
≈-sym    = IsEquivalence.sym ≈-Eq
≈-trans  = IsEquivalence.trans ≈-Eq
_<?_     = IsStrictTotalOrder._<?_ <-STO
_≈?_     = IsStrictTotalOrder._≟_ <-STO
compare  = IsStrictTotalOrder.compare <-STO


SortedList :  Set
SortedList = List# _<?_


-- The head of the list is the smallest, so to cons z, it suffices to know
-- that z < head.
cons-lem : ∀ {x y} {xs : SortedList} {fx : x # xs} -> y < x -> All (y <_) (cons x xs fx)
cons-lem {fx = fx} y<x = y<x ∷ all-map (<-trans y<x) (fresh→all fx)


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
≈-preserves-# fx eq with fresh→all fx
... | z = all→fresh (all-map (IsStrictTotalOrder.<-respˡ-≈ <-STO eq) z)

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

-------------------
-- Concatenation --
-------------------

-- The prerequisite for concatenating contexts is that the largest (aka, rightmost)
-- thing in the left context must be smaller than the smallest (aka, leftmost; aka, the head)
-- thing in the right context.
Gluable : SortedList -> SortedList -> Set
Gluable xs [] = ⊤
Gluable xs (y ∷# ys) = All (_< y) xs

gluable-singleton : ∀ x ys → All (x <_) ys → Gluable (x ∷# []) ys
gluable-singleton x [] [] = tt
gluable-singleton x (cons y ys fy) (x<y ∷ ps) = x<y ∷ []

-- It's also very easy to glue with the empty list in the other direction.
[]gluable-l : ∀ xs -> Gluable [] xs
[]gluable-l [] = tt
[]gluable-l (cons x xs fx) = []

-- Removing elements from the front of the left list preserves gluability.
-- (both this and the following strengthing lemms have duals for the end of
-- the right list, but we don't need those yet)
Gluable-weaken : {x : X} {xs ys : SortedList} {fx : x # xs} -> Gluable (cons x xs fx) ys -> Gluable xs ys
Gluable-weaken {ys = []} g = tt
Gluable-weaken {ys = cons y ys fy} (_ ∷ g) = g

-- as long as there was already something at the front, we can add more
-- (constraint is important: anything is both smaller + larger than every element of the empty list)
Gluable-strengthenL : {x : X} {xs ys : SortedList} (fx : fresh _ _ x xs)
                   -> NonEmpty xs
                   -> Gluable xs ys
                   -> Gluable (cons x xs fx) ys
Gluable-strengthenL {ys = []} _ _ _ = tt
Gluable-strengthenL {ys = cons y ys fy} fx pxs g = all-trans pxs (fresh→all fx) g ∷ g where
  all-trans : ∀ {a b} {as : SortedList} -> NonEmpty as -> All (a <_) as -> All (_< b) as -> a < b
  all-trans (cons x xs fx) (a<x ∷ l) (x<b ∷ r) = <-trans a<x x<b

-- Concatenation is defined mutually because we have to build proofs as we go
concat : (xs ys : SortedList) -> Gluable xs ys -> SortedList
concat-fresh : ∀ x xs ys ( fx : x # xs ) (ps : Gluable (cons x xs fx) ys) -> All (x <_) (concat xs ys (Gluable-weaken ps))

concat [] ys _ = ys
concat (cons x xs fx) ys ps = cons x (concat xs ys (Gluable-weaken ps)) (all→fresh (concat-fresh x xs ys fx ps))

concat-fresh z [] [] fz ps = []
concat-fresh z [] (cons y ys fy) (lift tt) (x ∷ []) = cons-lem x
concat-fresh z (cons x xs fx) ys (lift z<x , fz) q = toWitness z<x ∷ all-map (<-trans (toWitness z<x)) (concat-fresh x xs ys fx (Gluable-weaken q))

syntax concat xs ys g = xs ++[ g ] ys

-- Concatenation for All
_++A_ : {xs ys : SortedList} {g : Gluable xs ys} {P : X -> Set}
           -> All P xs -> All P ys -> All P (xs ++[ g ] ys)
_++A_ [] pys = pys
_++A_ (px ∷ pxs) pys = px ∷ (pxs ++A pys)

-- Append to the end of a context
snoc : (xs : SortedList) (x : X) -> All (_< x) xs -> SortedList
snoc xs x p = xs ++[ p ] (x ∷# [])

-- If y is larger than the x that was snocced, then y is larger than the whole list.
snoc-all< : {x y : X} {xs : SortedList} {pxs : All (_< x) xs}
          -> x < y -> All (_< y) (snoc xs x pxs)
snoc-all< {x} {y} {xs} {pxs} x<y = (all-map (λ z → <-trans z x<y) pxs) ++A (x<y ∷ [])

-- If the thing that was snocced is smaller than the whole right list, then the two lists are still gluable.
snoc-gluable : {l r : SortedList} {x : X} {p : All (_< x) l} -> All (x <_) r -> Gluable (snoc l x p) r
snoc-gluable [] = tt
snoc-gluable (x<r ∷ prs ) = snoc-all< x<r

-- -- If we have an All P on a snoc, then we can traverse it to get the P x at the end
-- snoc-allP : ∀ {x} {xs : SortedList} {P : X → Set} {p : All (_< x) xs} -> All P (snoc xs x p) -> P x
-- snoc-allP = {!!}

---------------------------------
-- Properties of Concatenation --
---------------------------------

-- For the same left and right side, the gluable proof doesn't change the result of the concat
concat-gluable-irrelevant : { l l' r r' : SortedList } {p q : Gluable l r} -> l ≡ l' -> r ≡ r' -> l ++[ p ] r ≡ l ++[ q ] r
concat-gluable-irrelevant {[]} refl refl = refl
concat-gluable-irrelevant {cons l₀ l fl} refl refl = cons-cong l₀ (concat-gluable-irrelevant {l} refl refl)

concat-idʳ : ∀ xs -> xs ++[ tt ] [] ≡ xs
concat-idʳ [] = refl
concat-idʳ (cons x xs fx) = cons-cong x (concat-idʳ xs)

-- Concatenation is associative
concat-assoc : ∀ xs ys zs {p q p' q'} -> (xs ++[ p ] ys) ++[ q ] zs ≡ xs ++[ q' ] (ys ++[ p' ] zs)
concat-assoc [] [] zs = refl
concat-assoc [] (cons y ys fy) zs = cons-cong y (concat-gluable-irrelevant {l = ys} {r = zs} refl refl)
concat-assoc (cons x xs fx) ys zs = cons-cong x (concat-assoc xs ys zs)



-- -- We can push a snoc on the left of a concat to a cons on the right
-- concat-snoc-cons : ∀ l r x p fx g g' -> (snoc l x p) ++[ g ] r ≡ l ++[ g' ] (cons x r fx)
-- concat-snoc-cons l [] x p fx tt g' rewrite concat-idʳ (l ++[ p ] (x ∷# [])) tt = concat-gluable-irrelevant refl refl
-- concat-snoc-cons l (cons r₀ r fr) x p fx g g' with fresh-irrelevant (all→fresh {x = x} {xs = concat [] (cons r₀ r fr) (Gluable-weaken (snoc-allP g ∷ []))} (concat-fresh x [] (cons r₀ r fr) (lift tt) (snoc-allP g ∷ []))) fx
-- ... | z = {!concat-assoc l (x ∷# []) r!}
-- -- = concat-assoc l (x ∷# []) r
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

-----------------
-- Insertion
-----------------

-- General form of insertion that also produces some proof data;
-- namely, that the result can be seen as (l ++ [x] ++ r) for some l and r.
ins : (l : SortedList) (r : SortedList) (x : X)
    -> (g : Gluable l r)
    -> (p : All (_< x) l)
    -> SortedList
    × Σ[ l ∈ SortedList ] Σ[ r ∈ SortedList ] Σ[ p ∈ All (_< x) l ] (Gluable (snoc l x p) r)
ins l [] x g p = snoc l x p
                 , l , [] , p , g
ins l (cons r₀ r fr) x g p with compare x r₀
-- if x<r₀ then we've found its one true home. insert here.
... | tri< lt ¬eq ¬gt = (snoc l x p) ++[ snoc-all< (lt) ] (cons r₀ r fr)
                  , l , (cons r₀ r fr) , p , snoc-all< (lt)
-- if x=r₀ then we stop here and don't insert.
... | tri≈ ¬lt eq ¬gt = l ++[ g ] (cons r₀ r fr)
                  , l , r , p , snoc-gluable (fresh→all (≈-preserves-# fr (≈-sym eq)))
-- if x>r₀ then we need to keep looking.
... | tri> ¬lt ¬eq gt = ins (snoc l r₀ g) r x (snoc-gluable (fresh→all fr)) (snoc-all< (gt))

-- If x doesn't already appear in the list, then insert it in the
-- correct place. Otherwise, leave it alone.
insert : X -> SortedList -> SortedList
insert x xs = proj₁ (ins [] xs x ([]gluable-l xs) [])

----------------------------
-- Union and Intersection --
----------------------------

-- Union of sorted lists.
_∪_ : SortedList -> SortedList -> SortedList
[] ∪ ys = ys
cons x xs p ∪ ys = insert x (xs ∪ ys)

-- Intersection of sorted lists
_∩_ : SortedList -> SortedList -> SortedList
[] ∩ ys = []
_∩_ (cons x xs p) ys with any? (x <?_) ys
... | yes _ = insert x (xs ∩ ys)
... | no  _ = xs ∩ ys


----------------------
-- Deletion/Removal --
----------------------

remove' : ∀ {x} { acc xs : SortedList } -> Gluable acc xs -> x ∈ xs -> SortedList
remove' {a} {acc} { cons x [] fx } px (here a≈x) = acc
remove' {a} {acc} { cons x (cons y ys fy) fx } px (here a≈x) with fresh→all {xs = cons y ys fy} fx
... | x<y ∷ _ = let p = all>-trans px x<y
                in acc ++[ p ] (cons y ys fy)
remove' {a} {acc} { cons x (cons y ys fy) fx } px (there a∈xs) with fresh→all {xs = cons y ys fy} fx
... | x<y ∷ _ = remove' {a} {snoc acc x px} {cons y ys fy} (snoc-all< x<y) a∈xs

remove : ∀ {x} {xs : SortedList} -> x ∈ xs -> SortedList
remove {x} {xs} x∈xs = remove' ([]gluable-l xs) x∈xs

------------------------------
-- Non-Emptiness Properties --
------------------------------

-- Concatenating with a non-empty list produces a non-empty list.
concatcons-NonEmpty : ∀ {xs y ys g fy} -> NonEmpty (xs ++[ g ] (cons y ys fy))
concatcons-NonEmpty {[]} = cons _ _ _
concatcons-NonEmpty {(cons a xs x)} = cons _ _ _

-- a nicer version to use in with's
snoc-NonEmpty : ∀ xs x p -> NonEmpty (snoc xs x p)
snoc-NonEmpty xs x p = concatcons-NonEmpty

-- Insertion produces a non-empty list.
ins-NonEmpty : ∀ l r x (g : Gluable l r) (p : All (_< x) l) -> NonEmpty (proj₁ (ins l r x g p))
ins-NonEmpty l [] x g p = concatcons-NonEmpty
ins-NonEmpty l (cons r₀ r fr) x g p with compare x r₀
... | tri< lt ¬eq ¬gt = concatcons-NonEmpty
... | tri≈ ¬lt eq ¬gt = concatcons-NonEmpty
... | tri> ¬lt ¬eq gt = ins-NonEmpty (snoc l r₀ g) r x (snoc-gluable (fresh→all fr)) (snoc-all< (gt))

-- For convenience, specialise the above result to insert.
insert-NonEmpty : ∀ x xs -> NonEmpty (insert x xs)
insert-NonEmpty x xs = ins-NonEmpty [] xs x ([]gluable-l xs) []

----------------------------------------
-- Properties of Concatenation and ∈ --
----------------------------------------

concat∈l : ∀ l r x p -> x ∈ l -> x ∈ (l ++[ p ] r)
concat∈l (cons l₀ l fl) r x p (here eq) = here eq
concat∈l (cons l₀ l fl) r x p (there x∈l) = there (concat∈l l r x (Gluable-weaken p) x∈l)

concat∈r : ∀ l r x p -> x ∈ r -> x ∈ (l ++[ p ] r)
concat∈r [] r x p x∈r = x∈r
concat∈r (cons l₀ l fl) r x p x∈r = there (concat∈r l r x (Gluable-weaken p) x∈r)

snoc∈ : ∀ {a b} xs p -> a ≈ b -> a ∈ snoc xs b p
snoc∈ {a} {b} xs p a≈b = concat∈r xs (cons b [] _) a p (here a≈b)

∈-weaken : ∀ {a x} {xs : SortedList} {fx : x # xs} -> ¬ (a ≈ x) -> a ∈ (cons x xs fx) -> a ∈ xs
∈-weaken {a} {x} a≉x (here a≈x) = ⊥-elim (a≉x a≈x)
∈-weaken {a} {x} a≉x (there a∈xs) = a∈xs

view-concat∈ : ∀ l r x p -> x ∈ (l ++[ p ] r) -> x ∈ l ⊎ x ∈ r
view-concat∈ [] r x p x∈r = inj₂ x∈r
view-concat∈ (cons l₀ l fl) r x p x∈lr with x ≈? l₀
... | yes eq = inj₁ (here eq)
... | no  x≉l₀ = lem (view-concat∈ l r x (Gluable-weaken p) (∈-weaken x≉l₀ x∈lr) ) where
  lem : ∀ {x y} {ys zs : SortedList} {fy : y # ys} -> (x ∈ ys) ⊎ (x ∈ zs) -> (x ∈ (cons y ys fy)) ⊎ (x ∈ zs)
  lem (inj₁ p) = inj₁ (there p)
  lem (inj₂ q) = inj₂ q

--------------------------------
-- Properties of Insert and ∈ --
--------------------------------

-- If a≡x, then a ∈ (jnsert x xs), because a is exactly the thing that was inserted.
mk-ins∈-here : ∀ {a} (l r : SortedList) (x : X) (g : Gluable l r) (p : All (_< x) l)
        -> a ≈ x -> a ∈ proj₁ (ins l r x g p)
mk-ins∈-here l [] x g p a≈x = ≈-preserves-∈ (snoc∈ l p ≈-refl) (≈-sym a≈x)
mk-ins∈-here {a} l (cons r₀ r fr) x g p a≈x with compare x r₀
... | tri< lt ¬eq ¬gt = concat∈l (snoc l x p) (cons r₀ r fr) a
                    (snoc-all< (lt)) (≈-preserves-∈ (snoc∈ l p ≈-refl) (≈-sym a≈x))
... | tri≈ ¬lt eq ¬gt = ≈-preserves-∈ (concat∈r l (cons r₀ r fr) r₀ g (here ≈-refl)) (≈-sym (≈-trans a≈x eq))
... | tri> ¬lt ¬eq gt = mk-ins∈-here (snoc l r₀ g) r x (snoc-gluable (fresh→all fr))
                        (snoc-all< (gt)) a≈x

mk-ins∈-l : ∀ {a} (l r : SortedList) (x : X) (g : Gluable l r) (p : All (_< x) l)
        -> a ∈ l -> a ∈ proj₁ (ins l r x g p)
mk-ins∈-l {a} l [] x g p a∈l = concat∈l l (x ∷# []) a p a∈l
mk-ins∈-l {a} l (cons r₀ r fr) x g p a∈l with compare x r₀
... | tri< lt ¬eq ¬gt = concat∈l (snoc l x p) (cons r₀ r fr) a
                    (snoc-all< (lt)) (concat∈l l (x ∷# []) a p a∈l)
... | tri≈ ¬lt eq ¬gt = ≈-preserves-∈ (concat∈l l (cons r₀ r fr) a g a∈l) ≈-refl
... | tri> ¬lt ¬eq gt = mk-ins∈-l (snoc l r₀ g) r x (snoc-gluable (fresh→all fr)) (snoc-all< (gt)) (concat∈l l (r₀ ∷# []) a g a∈l)

mk-ins∈-r : ∀ {a} (l r : SortedList) (x : X) (g : Gluable l r) (p : All (_< x) l)
        -> a ∈ r -> a ∈ proj₁ (ins l r x g p)
mk-ins∈-r {a} l (cons r₀ r fr) x g p a∈r with a ≈? r₀
mk-ins∈-r {a} l (cons r₀ r fr) x g p a∈r | yes a≈r₀ with compare x r₀
... | tri< lt ¬eq ¬gt = concat∈r (snoc l x p) (cons r₀ r fr) a (snoc-all< lt) (here a≈r₀)
... | tri≈ ¬lt x≈r₀ ¬gt = ≈-preserves-∈ (concat∈r l (cons r₀ r fr) r₀ g (here ≈-refl)) (≈-sym a≈r₀ )
... | tri> ¬lt ¬eq gt = ≈-preserves-∈ (mk-ins∈-l (snoc l r₀ g) r x (snoc-gluable (fresh→all fr)) (snoc-all< gt) (snoc∈ l g ≈-refl)) (≈-sym a≈r₀)
mk-ins∈-r {a} l (cons r₀ r fr) x g p a∈r | no a≢r₀ with compare x r₀
... | tri< lt ¬eq ¬gt = concat∈r (snoc l x p) (cons r₀ r fr) a (snoc-all< (lt)) a∈r
... | tri≈ ¬lt eq ¬gt =  concat∈r l (cons r₀ r fr) a g a∈r
... | tri> ¬lt ¬eq gt =  mk-ins∈-r (snoc l r₀ g) r x (snoc-gluable (fresh→all fr))
                         (snoc-all< (gt)) (∈-weaken a≢r₀ a∈r)

-- To prove membership in an insertion, that element has to be either the
-- one being inserted, or it had to have been in the list already.
mk-insert∈ : {a x : X} ( xs : SortedList ) -> a ≈ x ⊎ a ∈ xs -> a ∈ insert x xs
mk-insert∈ {a} {x} xs (inj₁ a≡x) = mk-ins∈-here [] xs x ([]gluable-l xs) [] a≡x
mk-insert∈ {a} {x} xs (inj₂ a∈xs) = mk-ins∈-r [] xs x ([]gluable-l xs) [] a∈xs

-- If we already have a proof of membership in an ins, then we can decide whether it was on the left, right, or if it was the thing inserted.
cases-ins∈ : ∀ {a} (l r : SortedList) (x : X) (g : Gluable l r) (p : All (_< x) l)
           -> a ∈ proj₁ (ins l r x g p) -> a ∈ l ⊎ a ≈ x ⊎ a ∈ r
cases-ins∈ {a} l [] x g p a∈ins with view-concat∈ l (x ∷# []) a p a∈ins
... | inj₁ a∈l = inj₁ a∈l
... | inj₂ (here a≡x) = inj₂ (inj₁ a≡x)
cases-ins∈ {a} l (cons r₀ r fr) x g p a∈ins with compare x r₀
cases-ins∈ {a} l (cons r₀ r fr) x g p a∈ins | tri< lt ¬eq ¬gt with view-concat∈ (snoc l x p) (cons r₀ r fr) a (snoc-all< (lt)) a∈ins
... | inj₂ w = inj₂ (inj₂ w)
cases-ins∈ {a} l (cons r₀ r fr) x g p a∈ins | tri< lt ¬eq ¬gt | inj₁ v with view-concat∈ l (x ∷# []) a p v
... | inj₁ a∈l = inj₁ a∈l
... | inj₂ (here a≡x) = inj₂ (inj₁ a≡x)
cases-ins∈ {a} l (cons r₀ r fr) x g p a∈ins | tri≈ ¬lt eq ¬gt with view-concat∈ l (cons r₀ r fr) a g a∈ins
... | inj₁ v = inj₁ v
... | inj₂ w = inj₂ (inj₂ w)
cases-ins∈ {a} l (cons r₀ r fr) x g p a∈ins | tri> ¬lt ¬eq gt with cases-ins∈ (snoc l r₀ g) r x (snoc-gluable (fresh→all fr)) (snoc-all< (gt)) a∈ins
... | inj₂ (inj₁ a≡x) = inj₂ (inj₁ a≡x)
... | inj₂ (inj₂ a∈r) = inj₂ (inj₂ (there a∈r))
... | inj₁ v with view-concat∈ l (r₀ ∷# []) a g v
... | inj₁ a∈l = inj₁ a∈l
... | inj₂ (here a≡r₀) = inj₂ (inj₂ (here a≡r₀))

-- The inverse; if we know that "a" was in the insertion, then we can decide
-- whether it was the thing that was inserted or not (and if not, it must have
-- been in the list already, in which case we can prove that.)
cases-insert∈ : ∀ {a x} (xs : SortedList) -> a ∈ insert x xs -> a ≈ x ⊎ a ∈ xs
cases-insert∈ {a} {x} xs a∈ins with cases-ins∈ [] xs x ([]gluable-l xs) [] a∈ins
... | inj₂ z = z

insert∈tail : ∀ {a x} (xs : SortedList) -> a ∈ insert x xs -> ¬ (a ≈ x) -> a ∈ xs
insert∈tail xs a∈xxs a≉x with cases-insert∈ xs a∈xxs
... | inj₁ a≈x = ⊥-elim (a≉x a≈x)
... | inj₂ a∈xs = a∈xs

insert-weaken-∉ : ∀ {a x xs} -> a ∉ insert x xs -> a ∉ xs
insert-weaken-∉ {a} {x} {xs} a∉ins a∈xs = ⊥-elim (a∉ins (mk-insert∈ xs (inj₂ a∈xs)))

insert-strengthen-∉ : ∀ {a x xs} -> ¬ (x ≈ a) -> a ∉ xs -> a ∉ insert x xs
insert-strengthen-∉ {a} {x} {xs} x≢a a∉xs a∈ins with cases-insert∈ xs a∈ins
... | inj₁ a≈x = ⊥-elim (x≢a (≈-sym a≈x))
... | inj₂ a∈xs = ⊥-elim (a∉xs a∈xs)

----------------------------------------
-- The Important Properties of Insert --
----------------------------------------

-- Limitation: Using extensionality makes the proofs easy, but is weaker than actually proving equality.
-- For many of these, we should have equality, but currently don't. Though it's also not currently an issue.

-- Order of insertion doesn't matter, because it ends up sorted anyway.
insert-comm : ∀ x y xs
             -> insert x (insert y xs) ≈L insert y (insert x xs)
insert-comm x y xs = extensionality (insert x (insert y xs)) (insert y (insert x xs)) λ z → f xs , f xs where
  f : ∀ {x y z} ( xs : SortedList ) -> z ∈ (insert x (insert y xs)) -> z ∈ (insert y (insert x xs))
  f {x} {y} {z} xs p with z ≈? y
  ... | yes z≈y = mk-insert∈ (insert x xs) (inj₁ z≈y)
  ... | no z≉y with z ≈? x
  ... | yes z≈x = mk-insert∈ (insert x xs) (inj₂ (mk-insert∈ xs (inj₁ z≈x)))
  ... | no z≉x with cases-insert∈ (insert y xs) p
  ... | inj₁ z≈x = ⊥-elim (z≉x z≈x)
  ... | inj₂ q with cases-insert∈ xs q
  ... | inj₁ z≈y = ⊥-elim (z≉y z≈y)
  ... | inj₂ z∈xs = mk-insert∈ (insert x xs) (inj₂ (mk-insert∈ xs (inj₂ z∈xs)))

-- Trying to insert the same thing twice has the same effect as once.
insert-idempotent : ∀ {x y}
                   -> x ≈ y
                   -> (xs : SortedList)
                   -> insert x (insert y xs) ≈L insert x xs
insert-idempotent {x} {y} x≈y xs = extensionality (insert x (insert y xs)) (insert x xs) λ z → f x≈y xs , g x≈y xs where

  f : ∀ {x y z} -> x ≈ y -> ( xs : SortedList ) -> z ∈ (insert x (insert y xs)) -> z ∈ insert x xs
  f {x} {y} {z} x≈y xs p with cases-insert∈ (insert y xs) p
  ... | inj₁ z≈x = mk-insert∈ xs (inj₁ z≈x)
  ... | inj₂ q with cases-insert∈ xs q
  ... | inj₁ z≈y = mk-insert∈ xs (inj₁ (≈-trans z≈y (≈-sym x≈y)))
  ... | inj₂ z∈xs = mk-insert∈ xs (inj₂ z∈xs)

  g : ∀ {x y z} -> x ≈ y -> ( xs : SortedList ) -> z ∈ insert x xs -> z ∈ (insert x (insert y xs))
  g {x} {y} {z} x≈y xs p with cases-insert∈ xs p
  ... | inj₁ z≈x = mk-insert∈ (insert y xs) (inj₂ (mk-insert∈ xs (inj₁ (≈-trans z≈x x≈y))))
  ... | inj₂ z∈xs = mk-insert∈ (insert y xs) (inj₂ (mk-insert∈ xs (inj₂ z∈xs)))

-- Inserting something that is smaller than everything else is the same as directly doing a cons.
insert-consview : ∀ {x} {xs : SortedList} -> (fx : x # xs) -> insert x xs ≡ cons x xs fx
insert-consview {xs = []} _ = refl
insert-consview {a} {cons x xs fx} fa with fresh→all {xs = cons x xs fx} fa | compare a x
... | _       | tri< _   _ _ = cons-cong a refl
... | a<x ∷ _ | tri≈ a≮x _ _ = ⊥-elim (a≮x a<x)
... | a<x ∷ _ | tri> a≮x _ _ = ⊥-elim (a≮x a<x)

------------------------
-- Preservation of ≈L --
------------------------

concat-preserves-≈L : ∀ {xs ys xs' ys' p q} -> xs ≈L xs' -> ys ≈L ys' -> (xs ++[ p ] ys) ≈L (xs' ++[ q ] ys')
concat-preserves-≈L [] ys≈ys' = ys≈ys'
concat-preserves-≈L (cons x≈x' xs≈xs') ys≈ys' = cons x≈x' (concat-preserves-≈L xs≈xs' ys≈ys')

snoc-preserves-≈L : ∀ {x y xs ys p q} -> xs ≈L ys -> x ≈ y -> snoc xs x p ≈L snoc ys y q
snoc-preserves-≈L xs≈ys x≈y = concat-preserves-≈L xs≈ys (cons x≈y [])

ins-preserves-≈L : ∀ {l l' r r' x x' g g' p p'}
                 -> l ≈L l'
                 -> r ≈L r'
                 -> x ≈ x'
                 -> proj₁ (ins l r x g p) ≈L proj₁ (ins l' r' x' g' p')
ins-preserves-≈L l≈l' [] x≈x' = snoc-preserves-≈L l≈l' x≈x'
ins-preserves-≈L {l} {l'} {cons r₀ r fr} {cons r₀' r' fr'} {x} {x'} l≈l' (cons r₀≈r₀' r≈r') x≈x' with compare x r₀ | compare x' r₀'
... | tri< x<r₀ x≉r₀ x≯r₀ | tri< x'<r₀' x'≉r₀' x'≯r₀' = concat-preserves-≈L (snoc-preserves-≈L l≈l' x≈x') (cons r₀≈r₀' r≈r')
... | tri< x<r₀ x≉r₀ x≯r₀ | tri≈ x'≮r₀' x'≈r₀' x'≯r₀' = ⊥-elim (x≉r₀ (≈-trans x≈x' (≈-trans x'≈r₀' (≈-sym r₀≈r₀'))))
... | tri< x<r₀ x≉r₀ x≯r₀ | tri> x'≮r₀' x'≉r₀' x'>r₀' = ⊥-elim (<-asym x<r₀ (proj₂ <-resp-≈ (≈-sym r₀≈r₀') (proj₁ <-resp-≈ (≈-sym x≈x') x'>r₀')))
... | tri≈ x≮r₀ x≈r₀ x≯r₀ | tri< x'<r₀' x'≉r₀' x'≯r₀' = ⊥-elim (x'≉r₀' (≈-trans (≈-sym x≈x') (≈-trans x≈r₀ r₀≈r₀')))
... | tri≈ x≮r₀ x≈r₀ x≯r₀ | tri≈ x'≮r₀' x'≈r₀' x'≯r₀' = concat-preserves-≈L l≈l' (cons r₀≈r₀' r≈r')
... | tri≈ x≮r₀ x≈r₀ x≯r₀ | tri> x'≮r₀' x'≉r₀' x'>r₀' = ⊥-elim (x'≉r₀' (≈-trans (≈-sym x≈x') (≈-trans x≈r₀ r₀≈r₀')))
... | tri> x≮r₀ x≉r₀ x>r₀ | tri< x'<r₀' x'≉r₀' x'≯r₀' = ⊥-elim (<-asym x>r₀ (proj₂ <-resp-≈ (≈-sym x≈x') (proj₁ <-resp-≈ (≈-sym r₀≈r₀') x'<r₀')))
... | tri> x≮r₀ x≉r₀ x>r₀ | tri≈ x'≮r₀' x'≈r₀' x'≯r₀' = ⊥-elim (x≉r₀ (≈-trans x≈x' (≈-trans x'≈r₀' (≈-sym r₀≈r₀'))))
... | tri> x≮r₀ x≉r₀ x>r₀ | tri> x'≮r₀' x'≉r₀' x'>r₀' = ins-preserves-≈L (snoc-preserves-≈L l≈l' r₀≈r₀') r≈r' x≈x'

insert-preserves-≈L : ∀ {x y} {xs ys : SortedList} -> x ≈ y -> xs ≈L ys -> insert x xs ≈L insert y ys
insert-preserves-≈L x≈y xs≈ys = ins-preserves-≈L [] xs≈ys x≈y

≈L-preserves-∈ : ∀ {a} {xs ys : SortedList} -> a ∈ xs -> xs ≈L ys -> a ∈ ys
≈L-preserves-∈ (here a≈x) (cons x≈y xs≈ys) = here (≈-trans a≈x x≈y)
≈L-preserves-∈ (there a∈xs) (cons x≈y xs≈ys) = there (≈L-preserves-∈ a∈xs xs≈ys)

≈L-preserves-∉ : ∀ {a} {xs ys : SortedList} -> a ∉ xs -> xs ≈L ys -> a ∉ ys
≈L-preserves-∉ a∉xs xs≈ys a∈ys = a∉xs (≈L-preserves-∈ a∈ys (≈L-sym xs≈ys))

≈L-preserves-length : {xs ys : SortedList} -> xs ≈L ys -> length xs ≡ length ys
≈L-preserves-length [] = refl
≈L-preserves-length (cons x≈y xs≈ys) = cong suc (≈L-preserves-length xs≈ys)

-----------------------
-- Length Properties --
-----------------------

weaken-∉ : ∀ {x a} {as : SortedList} {fa : a # as} -> x ∉ (cons a as fa) -> x ∉ as
weaken-∉ x (here x₁) = x (there (here x₁))
weaken-∉ x (there x₁) = x (there (there x₁))

strengthen-∉ : ∀ {x a} {as : SortedList} {fa : a # as} -> ¬ (x ≈ a) -> x ∉ as -> x ∉ (cons a as fa)
strengthen-∉ x≉a x∉as (here x≈a) = x≉a x≈a
strengthen-∉ x≉a x∉as (there x∈as) = x∉as x∈as

length-concat : ∀ l r (g : Gluable l r) -> length (l ++[ g ] r) ≡ length l + length r
length-concat [] r g = refl
length-concat (cons l₀ l fl) r g = cong suc (length-concat l r (Gluable-weaken g))

length-snoc : ∀ xs x p -> length (snoc xs x p) ≡ suc (length xs)
length-snoc xs x p rewrite +-comm 1 (length xs) = length-concat xs (x ∷# []) p

module _ where
  open Relation.Binary.PropositionalEquality.≡-Reasoning

  ins-len∉ : ∀ l r x g p -> x ∉ r -> length (proj₁ (ins l r x g p)) ≡ suc (length l + length r)
  ins-len∉ l [] x g p x∉r rewrite +-identityʳ (length l) = length-snoc l x p
  ins-len∉ l (cons r₀ r fr) x g p x∉r with compare x r₀
  ... | tri< x<r₀ _ _ = trans (length-concat (snoc l x p) (cons r₀ r fr) (snoc-all< x<r₀)) (cong (_+ suc (length r)) (length-snoc l x p))
  ... | tri≈ _ x≈r₀ _ = ⊥-elim (x∉r (here x≈r₀))
  ... | tri> _ _ x>r₀
    = begin
      length (proj₁ (ins (snoc l r₀ g) r x _ _))
    ≡⟨ ins-len∉ (snoc l r₀ g) r x _ _ (weaken-∉ x∉r) ⟩
      suc (length (concat l (cons r₀ [] (lift tt)) g) + length r)
    ≡⟨ cong suc (trans (cong (_+ length r) (length-concat l (r₀ ∷# []) g)) (+-assoc (length l) 1 (length r))) ⟩
      suc (length l + suc (length r))
    ∎

  ins-len∈ : ∀ l r x g p -> x ∈ r -> length (proj₁ (ins l r x g p)) ≡ length l + length r
  ins-len∈ l (cons r₀ r fr) x g p (here x≈r₀) with compare x r₀
  ... | tri< x<r₀ _ _ = ⊥-elim (<-irrefl x≈r₀ x<r₀)
  ... | tri≈ _ x≈r₀ _ = length-concat l (cons r₀ r fr) g
  ... | tri> _ _ x>r₀ = ⊥-elim (<-irrefl (≈-sym x≈r₀) x>r₀)
  ins-len∈ l (cons r₀ r fr) x g p (there x∈r) with compare x r₀
  ... | tri< x<r₀ _ _ = ⊥-elim (lem x<r₀ (fresh→all fr) x∈r) where
    lem : ∀ {a x} {xs : SortedList} -> a < x -> All (x <_) xs -> Any (a ≈_) xs -> ⊥
    lem a<x (px ∷ pxs) (here a≈x) = <-irrefl a≈x (<-trans a<x px)
    lem a<x (px ∷ pxs) (there a∈xs) = lem a<x pxs a∈xs
  ... | tri≈ _ x≈r₀ _ = length-concat l (cons r₀ r fr) g
  ... | tri> _ _ x>r₀ =
    begin
      length (proj₁ (ins (snoc l r₀ g) r x (snoc-gluable (fresh→all fr)) (snoc-all< x>r₀)))
    ≡⟨ ins-len∈ (snoc l r₀ g) r x _ _ x∈r ⟩
      length (snoc l r₀ g) + length r
    ≡⟨ trans (cong (_+ length r) (length-snoc l r₀ g)) (sym (+-suc (length l) (length r))) ⟩
      length l + suc (length r)
    ∎


insert-length∉ : ∀ {x xs} -> x ∉ xs -> length (insert x xs) ≡ suc (length xs)
insert-length∉ {x} {xs} x∉xs = ins-len∉ [] xs x ([]gluable-l xs) [] x∉xs

-- ins∈r-id : ∀ l r x g p -> x ∈ r -> proj₁ (ins l r x g p) ≡ (l ++[ g ] r)
-- ins∈r-id l (cons r₀ r fr) x g p (here x≈r₀) with compare x r₀
-- ... | tri< x<r₀ _ _ = ⊥-elim (<-irrefl x≈r₀ x<r₀)
-- ... | tri≈ _ x≈r₀ _ = refl
-- ... | tri> _ _ x>r₀ = ⊥-elim (<-irrefl (≈-sym x≈r₀) x>r₀)
-- ins∈r-id l (cons r₀ r fr) x g p (there x∈r) with compare x r₀
-- ... | tri≈ _ x≈r₀ _ = refl
-- ... | tri< x<r₀ _ _ = ⊥-elim (<-asym x<r₀ (lem x∈r (fresh→all fr))) where
--   lem : ∀ {a x} {xs : SortedList} -> a ∈ xs -> All (x <_) xs -> x < a
--   lem {a} {x} {cons y ys fy} (here x≈r₀) (x<y ∷ pxs) = proj₁ <-resp-≈ (≈-sym x≈r₀) x<y
--   lem (there a∈xs) (x<y ∷ pxs) = lem a∈xs pxs
-- ... | tri> _ _ x>r₀ = trans (ins∈r-id (snoc l r₀ g) r x _ _ x∈r) (concat-snoc-cons l r r₀ g fr _ _)

-- insert∈-id : ∀ {x} {xs : SortedList} -> x ∈ xs -> insert x xs ≡ xs
-- insert∈-id {a} {xs} a∈xs = ins∈r-id [] xs a _ _ a∈xs

insert-length∈ : ∀ {x} {xs : SortedList} -> x ∈ xs -> length (insert x xs) ≡ length xs
insert-length∈ {x} {xs} x∈xs = ins-len∈ [] xs x ([]gluable-l xs) [] x∈xs

NonEmpty-length : {xs : SortedList} -> NonEmpty xs -> length xs > 0
NonEmpty-length (cons x xs fx) = s≤s z≤n

----------------------
-- Union Properties --
----------------------


∪∈ : ∀ {a} {xs ys : SortedList} -> a ∈ (xs ∪ ys) -> a ∈ xs ⊎ a ∈ ys
∪∈ {a} {[]} {ys} a∈ys = inj₂ a∈ys
∪∈ {a} {cons x xs fx} {ys} p with cases-insert∈ (xs ∪ ys) p
... | inj₁ a≈x = inj₁ (here a≈x)
... | inj₂ a∈∪ with ∪∈ a∈∪
... | inj₁ a∈xs = inj₁ (there a∈xs)
... | inj₂ a∈ys = inj₂ a∈ys

∉∪ : ∀ {a} {xs ys : SortedList} -> a ∉ xs -> a ∉ ys -> a ∉ (xs ∪ ys)
∉∪ {a} {[]} {ys} a∉xs a∉ys = a∉ys
∉∪ {a} {cons x xs fx} {ys} a∉xs a∉ys a∈∪ with ∪∈ a∈∪
... | inj₁ a∈xs = a∉xs a∈xs
... | inj₂ a∈ys = a∉ys a∈ys

-- This one definitely should be a _≡_, but the final case needs commutativity, which we haven't proved to _≡_ (yet?)
-- Not really a problem though. We lose rewritability, but can still prove ∈∪ʳ, which is its only current use.
module _ where
  open ≈L-Reasoning

  ∪-consʳ : ∀ {y} xs {ys : SortedList} ( fy : y # ys ) -> (xs ∪ cons y ys fy) ≈L (insert y (xs ∪ ys))
  ∪-consʳ {a} [] {[]} fa = ≈L-refl
  ∪-consʳ {a} [] {cons y ys fy} fa with fresh→all {xs = cons y ys fy} fa | compare a y
  ... | _       | tri< a<y a≉y a≯y = cons-refl-fresh-irrelevant where
    cons-refl-fresh-irrelevant : ∀ {x xs} {p q : x # xs} -> (cons x xs p) ≈L (cons x xs q)
    cons-refl-fresh-irrelevant {p = p} {q = q} rewrite fresh-irrelevant p q = ≈L-refl
  ... | a<y ∷ _ | tri≈ a≮y  _   _  = ⊥-elim (a≮y a<y)
  ... | a<y ∷ _ | tri> a≮y  _   _  = ⊥-elim (a≮y a<y)
  ∪-consʳ {a} ( cons x xs fx ) {ys} fa =
    begin
      (cons x xs fx ∪ cons a ys fa)
    ≈⟨ insert-preserves-≈L ≈-refl (∪-consʳ xs fa) ⟩
      insert x (insert a (xs ∪ ys))
    ≈⟨ insert-comm x a (xs ∪ ys) ⟩
      insert a (cons x xs fx ∪ ys)
    ∎

∈∪ˡ : ∀ {a} {xs : SortedList} -> a ∈ xs -> (ys : SortedList) -> a ∈ (xs ∪ ys)
∈∪ˡ {a} {cons x xs fx} (here a≈x) ys rewrite insert-consview fx = mk-insert∈ (xs ∪ ys) (inj₁ a≈x)
∈∪ˡ {a} {cons x xs fx} (there a∈xs) ys = mk-insert∈ (xs ∪ ys) (inj₂ (∈∪ˡ a∈xs ys))

∈∪ʳ : ∀ {x} {ys : SortedList} -> (xs : SortedList) -> x ∈ ys -> x ∈ (xs ∪ ys)
∈∪ʳ {a} {cons y ys fy} xs (here a≈y) rewrite insert-consview fy = ≈L-preserves-∈ (mk-insert∈ (xs ∪ ys) (inj₁ a≈y)) (≈L-sym (∪-consʳ xs fy))
∈∪ʳ {a} {cons y ys fy} xs (there a∈ys) = ≈L-preserves-∈ (mk-insert∈ (xs ∪ ys) (inj₂ (∈∪ʳ xs a∈ys))) (≈L-sym (∪-consʳ xs fy))

∉∪ˡ : ∀ {a} {xs ys : SortedList} -> a ∉ (xs ∪ ys) -> a ∉ xs
∉∪ˡ {ys = ys} ¬p a∈xs = ¬p (∈∪ˡ a∈xs ys)

∉∪ʳ : ∀ {a} {xs ys : SortedList} -> a ∉ (xs ∪ ys) -> a ∉ ys
∉∪ʳ {xs = xs} ¬p a∈ys = ¬p (∈∪ʳ xs a∈ys)

∪-idʳ : (xs : SortedList) -> (xs ∪ []) ≡ xs
∪-idʳ [] = refl
∪-idʳ (cons x xs fx) rewrite ∪-idʳ xs = insert-consview fx

∪-id : Identity _≈L_ [] _∪_
proj₁ ∪-id = λ x → ≈L-refl
proj₂ ∪-id = λ x → ≡→≈L (∪-idʳ x)

open ≈L-Reasoning

∪-comm : ( xs ys : SortedList ) -> (xs ∪ ys) ≈L (ys ∪ xs)
∪-comm [] ys rewrite ∪-idʳ ys = ≈L-refl
∪-comm (cons x xs fx) [] rewrite ∪-idʳ xs rewrite insert-consview fx = ≈L-refl
∪-comm (cons x xs fx) (cons y ys fy) =
  begin
    insert x (xs ∪ cons y ys fy)
  ≈⟨ insert-preserves-≈L ≈-refl (∪-comm xs (cons y ys fy)) ⟩
    insert x (insert y (ys ∪ xs))
  ≈⟨ insert-comm x y (ys ∪ xs) ⟩
    insert y (insert x (ys ∪ xs))
  ≈⟨ insert-preserves-≈L ≈-refl (insert-preserves-≈L ≈-refl (∪-comm ys xs)) ⟩
    insert y (insert x (xs ∪ ys))
  ≈⟨ insert-preserves-≈L ≈-refl (≈L-sym (∪-comm ys (cons x xs fx))) ⟩
    insert y (ys ∪ cons x xs fx)
  ∎

∪-idempotent : Idempotent _≈L_ _∪_
∪-idempotent [] = ≈L-refl
∪-idempotent (cons x xs fx) =
  begin
    (cons x xs fx ∪ cons x xs fx)
  ≈⟨ insert-preserves-≈L ≈-refl (∪-consʳ xs fx) ⟩
    insert x (insert x (xs ∪ xs))
  ≈⟨ insert-idempotent ≈-refl (xs ∪ xs) ⟩
    insert x (xs ∪ xs)
  ≈⟨ insert-preserves-≈L ≈-refl (∪-idempotent xs) ⟩
    insert x xs
  ≈⟨ ≡→≈L (insert-consview fx) ⟩
    cons x xs fx
  ∎

∪-preserves-≈L : {xs xs' ys ys' : SortedList} -> xs ≈L xs' -> ys ≈L ys' -> (xs ∪ ys) ≈L (xs' ∪ ys')
∪-preserves-≈L [] [] = []
∪-preserves-≈L {ys = cons y ys fy} {ys' = cons y' ys' fy'} [] (cons y≈y' ys≈ys')
  = cons y≈y' ys≈ys'
∪-preserves-≈L {cons x xs fx} {cons x' xs' fx'} (cons x≈x' xs≈xs') []
  rewrite ∪-idʳ xs
  rewrite ∪-idʳ xs'
  = insert-preserves-≈L x≈x' xs≈xs'
∪-preserves-≈L {cons x xs fx} {cons x' xs' fx'} {cons y ys fy} {cons y' ys' fy'} (cons x≈x' xs≈xs') (cons y≈y' ys≈ys')
  = insert-preserves-≈L x≈x' (∪-preserves-≈L xs≈xs' (cons y≈y' ys≈ys'))

∪-cancelˡ : {xs ys : SortedList} -> xs ≈L ys -> (xs ∪ ys) ≈L xs
∪-cancelˡ [] = ≈L-refl
∪-cancelˡ {cons x xs fx} {cons y ys fy} (cons x≈y xs≈ys) =
  begin
    insert x (xs ∪ cons y ys fy)
  ≈⟨ insert-preserves-≈L ≈-refl (∪-comm xs (cons y ys fy)) ⟩
    insert x (cons y ys fy ∪ xs)
  ≈⟨⟩
    insert x (insert y (ys ∪ xs))
  ≈⟨ insert-idempotent x≈y (ys ∪ xs) ⟩
    insert x (ys ∪ xs)
  ≈⟨ insert-preserves-≈L ≈-refl (∪-comm ys xs) ⟩
    insert x (xs ∪ ys)
  ≈⟨ insert-preserves-≈L ≈-refl (∪-cancelˡ xs≈ys)  ⟩
    insert x xs
  ≈⟨ ≡→≈L (insert-consview fx) ⟩
    cons x xs fx
  ∎

-- Union associates with insertion.
∪-insert-assoc : ∀ x ( xs ys : SortedList ) -> ((insert x xs) ∪ ys) ≈L (insert x (xs ∪ ys))
∪-insert-assoc x xs ys = extensionality (insert x xs ∪ ys) (insert x (xs ∪ ys)) (λ x → f x , g x) where
  f : ∀ a → a ∈ (insert x xs ∪ ys) → a ∈ insert x (xs ∪ ys)
  f a p with ∪∈ {xs = insert x xs} {ys = ys} p
  ... | inj₂ a∈ys = mk-insert∈ (xs ∪ ys) (inj₂ (∈∪ʳ xs a∈ys))
  ... | inj₁ q with cases-insert∈ xs q
  ... | inj₁ a≈x = mk-insert∈ (xs ∪ ys) (inj₁ a≈x)
  ... | inj₂ a∈xs = mk-insert∈ (xs ∪ ys) (inj₂ (∈∪ˡ a∈xs ys))

  g : ∀ a → a ∈ insert x (xs ∪ ys) → a ∈ (insert x xs ∪ ys)
  g a p with cases-insert∈ (xs ∪ ys) p
  ... | inj₁ a≈x = ∈∪ˡ (mk-insert∈ xs (inj₁ a≈x)) ys
  ... | inj₂ q with ∪∈ {xs = xs} {ys = ys} q
  ... | inj₁ a∈xs = ∈∪ˡ (mk-insert∈ xs (inj₂ a∈xs)) ys
  ... | inj₂ a∈ys = ∈∪ʳ (insert x xs) a∈ys

∪-assoc : (xs ys zs : SortedList) -> ((xs ∪ ys) ∪ zs) ≈L (xs ∪ (ys ∪ zs))
∪-assoc [] ys zy = ≈L-refl
∪-assoc (cons x xs fx) ys zs =
  begin
    (insert x (xs ∪ ys)) ∪ zs
  ≈⟨ ∪-insert-assoc x (xs ∪ ys) zs ⟩
    insert x ((xs ∪ ys) ∪ zs)
  ≈⟨ insert-preserves-≈L ≈-refl (∪-assoc xs ys zs) ⟩
    insert x (xs ∪ (ys ∪ zs))
  ∎

---------------------------
-- Properties of Removal --
---------------------------

-- Lemma for the general form; if a was already added to acc, then it will be in the final result.
remove'-∈acc : ∀ {a} {b} {acc xs : SortedList} -> (g : Gluable acc xs) -> (b∈xs : b ∈ xs) -> a ∈ acc -> a ∈ remove' g b∈xs
remove'-∈acc {a} {b} {acc} {cons x [] fx} g (here b≈x) a∈acc = a∈acc
remove'-∈acc {a} {b} {acc} {cons x (cons y ys fy) fx} g (here b≈x) a∈acc with fresh→all {xs = cons y ys fy} fx
... | x<y ∷ _ = concat∈l acc (cons y ys fy) a (all>-trans g x<y) a∈acc
remove'-∈acc {a} {b} {acc} {cons x (cons y ys fy) fx} g (there b∈xs) a∈acc with fresh→all {xs = cons y ys fy} fx
... | x<y ∷ _ = remove'-∈acc {a} {b} {snoc acc x _} {cons y ys fy} (snoc-all< x<y)
                  b∈xs (concat∈l acc (x ∷# []) a g a∈acc)

-- When you remove an element from a list, it's no longer in that list.
-- (general version that knows about the accumulator)
remove'-removes-correct-elem : ∀ {a} {acc xs : SortedList} -> (g : Gluable acc xs) -> (a∈xs : a ∈ xs) -> a ∉ (remove' g a∈xs)
remove'-removes-correct-elem {a} {acc} {x ∷# []} g (here a≈x) a∈rem = all>-irrefl a∈rem (all>-resp-≈ (≈-sym a≈x) g)
remove'-removes-correct-elem {a} {acc} {cons x (cons y ys fy) fx} g (here a≈x) a∈rem with fresh→all {xs = cons y ys fy} fx
... | x<y ∷ _ with view-concat∈ acc (cons y ys fy) a (all>-trans g x<y) a∈rem
... | inj₁ a∈acc = all>-irrefl a∈acc (all>-resp-≈ (≈-sym a≈x) g)
... | inj₂ a∈xs  = all<-irrefl a∈xs (all<-resp-≈ (≈-sym a≈x) (fresh→all fx))
remove'-removes-correct-elem {a} {acc} {cons x (cons y ys fy) fx} g (there a∈xs) a∈rem with fresh→all {xs = cons y ys fy} fx
... | x<y ∷ _ = remove'-removes-correct-elem (snoc-all< x<y) a∈xs a∈rem

-- When you remove an element from a list, it's no longer in that list.
-- (version for actual use)
remove-removes-correct-elem : ∀ {x} {xs : SortedList} -> (x∈xs : x ∈ xs) -> x ∉ (remove x∈xs)
remove-removes-correct-elem {a} {xs} a∈xs = remove'-removes-correct-elem ([]gluable-l xs) a∈xs

----

-- The result of the removal is a subset of the original list (nothing new was added).
-- (general version doesn't use the actual subset relation, because it may actually be in acc)
remove'-⊆ : ∀ {a b} {acc xs : SortedList} -> (g : Gluable acc xs) -> (a∈xs : a ∈ xs) -> b ∈ (remove' g a∈xs) -> b ∈ acc ⊎ b ∈ xs
remove'-⊆ {a} {b} {acc} {x ∷# []} g (here a≈x) b∈rem = inj₁ b∈rem
remove'-⊆ {a} {b} {acc} {cons x (cons y ys fy) fx} g (here a≈x) b∈rem with fresh→all {xs = cons y ys fy} fx
... | x<y ∷ _ with view-concat∈ acc (cons y ys fy) b (all>-trans g x<y) b∈rem
... | inj₁ b∈acc = inj₁ b∈acc
... | inj₂ x∈xs  = inj₂ (there x∈xs)
remove'-⊆ {a} {b} {acc} {cons x (cons y ys fy) fx} g (there a∈xs) b∈rem with fresh→all {xs = cons y ys fy} fx
... | x<y ∷ _ with remove'-⊆ (snoc-all< x<y) a∈xs b∈rem
... | inj₂ b∈xs = inj₂ (there b∈xs)
... | inj₁ b∈ax with view-concat∈ acc (x ∷# []) b g b∈ax
... | inj₁ b∈acc = inj₁ b∈acc
... | inj₂ (here b≈x) = inj₂ (here b≈x)


remove-⊆ : ∀ {a} {xs : SortedList} -> (a∈xs : a ∈ xs) -> (remove a∈xs) ⊆ xs
remove-⊆ {xs = xs} a∈xs b∈rem with remove'-⊆ ([]gluable-l xs) a∈xs b∈rem
... | inj₁ ()
... | inj₂ b∈xs = b∈xs

-- Everything that was already in the list aside from the removed element is still there
-- after the removal.
mk∈-remove' : ∀ {a} {b} {acc xs : SortedList} -> (g : Gluable acc xs) -> (b∈xs : b ∈ xs) -> a ∈ xs -> ¬ (a ≈ b) -> a ∈ (remove' g b∈xs)
mk∈-remove' g (here b≈x) (here a≈x) a≉b = ⊥-elim (a≉b (≈-trans a≈x (≈-sym b≈x)))
mk∈-remove' {a} {b} {acc} {cons x (cons y ys fy) fx} g (here b≈x) (there a∈xs) a≉b with fresh→all {xs = cons y ys fy} fx
... | x<y ∷ _ = concat∈r acc (cons y ys fy) a (all>-trans g x<y) a∈xs
mk∈-remove' {a} {b} {acc} {cons x (cons y ys fy) fx} g (there b∈xs) (here a≈x) a≉b with fresh→all {xs = cons y ys fy} fx
... | x<y ∷ _ = remove'-∈acc (snoc-all< x<y) b∈xs (snoc∈ acc _ a≈x)
mk∈-remove' {a} {b} {acc} {cons x (cons y ys fy) fx} g (there b∈xs) (there a∈xs) a≉b with fresh→all {xs = cons y ys fy} fx
... | x<y ∷ _ = mk∈-remove' (snoc-all< x<y) b∈xs a∈xs a≉b 

mk∈-remove : ∀ {a b} {xs : SortedList} -> (b∈xs : b ∈ xs) -> a ∈ xs -> ¬ (a ≈ b) -> a ∈ (remove b∈xs)
mk∈-remove {a} {b} {xs} b∈xs a∈xs a≉b = mk∈-remove' ([]gluable-l xs) b∈xs a∈xs a≉b

remove-insert-union-lem : ∀ {a} {xs ys : SortedList} -> (a∈xs : a ∈ xs) -> a ∉ ys -> (xs ∪ ys) ≈L ((remove a∈xs) ∪ (insert a ys))
remove-insert-union-lem {a} {xs} {ys} a∈xs a∉ys = extensionality (xs ∪ ys) ((remove a∈xs) ∪ (insert a ys)) (λ x → f x , g x) where
  f : ∀ b → b ∈ (xs ∪ ys) → b ∈ (remove a∈xs ∪ insert a ys)
  f b b∈u with b ≈? a | ∪∈ {b} {xs} {ys} b∈u
  ... | no  b≉a | inj₁ b∈xs = ∈∪ˡ (mk∈-remove a∈xs b∈xs b≉a) (insert a ys)
  ... | no  b≉a | inj₂ b∈ys = ∈∪ʳ (remove a∈xs) (mk-insert∈ ys (inj₂ b∈ys))
  ... | yes b≈a | _ = ∈∪ʳ (remove a∈xs) (mk-insert∈ ys (inj₁ b≈a))

  g : ∀ b → b ∈ (remove a∈xs ∪ insert a ys) → b ∈ (xs ∪ ys)
  g b b∈u with ∪∈ {b} {remove a∈xs} {insert a ys} b∈u
  ... | inj₁ b∈l = ∈∪ˡ (remove-⊆ a∈xs b∈l) ys
  ... | inj₂ b∈r with cases-insert∈ ys b∈r
  ... | inj₁ b≈a  = ∈∪ˡ (≈-preserves-∈ a∈xs (≈-sym b≈a)) ys
  ... | inj₂ b∈ys = ∈∪ʳ xs b∈ys

------------------
-- Disjointness --
------------------

Disjoint : SortedList -> SortedList -> Set
Disjoint xs ys = ∀ {x y} -> x ≈ y -> x ∈ xs -> y ∈ ys -> ⊥

disjoint-sym : ∀ {xs ys} -> Disjoint xs ys -> Disjoint ys xs
disjoint-sym d x≈y b∈ys a∈xs = d (≈-sym x≈y) a∈xs b∈ys

disjoint-∪ : ∀ {xs ys zs} -> Disjoint xs ys -> Disjoint xs zs -> Disjoint xs (ys ∪ zs)
disjoint-∪ {xs} {ys} {zs} d e {a} {b} a≈b a∈xs a∈∪ with ∪∈ a∈∪
... | inj₁ a∈ys = d a≈b a∈xs a∈ys
... | inj₂ a∈zs = e a≈b a∈xs a∈zs

disjoint-weakenˡ : ∀ {x xs ys} {fx : x # xs} -> Disjoint (cons x xs fx) ys -> Disjoint xs ys
disjoint-weakenˡ d a≈b a∈xs a∈ys = d a≈b (there a∈xs) a∈ys

disjoint-union-length : ∀ {xs ys} -> Disjoint xs ys -> length (xs ∪ ys) ≡ (length xs) + (length ys)
disjoint-union-length {[]} {ys} d = refl
disjoint-union-length {cons x xs fx} {ys} d
  rewrite insert-length∉ (∉∪ {x} {xs} {ys} (#→∉ fx) (d ≈-refl (here ≈-refl)))
  = cong suc (disjoint-union-length {xs} {ys} (disjoint-weakenˡ d))

-- Insertion preserves disjointness when the thing you insert wasn't already in the other side
insert-preserves-disjointˡ : ∀ {a xs ys} -> Disjoint xs ys -> a ∉ ys -> Disjoint (insert a xs) ys
insert-preserves-disjointˡ {a} {xs} {ys} d a∉ys x≈y x∈axs y∈ys with cases-insert∈ xs x∈axs
... | inj₁ x≈a = a∉ys (≈-preserves-∈ y∈ys (≈-trans (≈-sym x≈y) x≈a))
... | inj₂ x∈xs = d x≈y x∈xs y∈ys

insert-preserves-disjointʳ : ∀ {a xs ys} -> Disjoint xs ys -> a ∉ xs -> Disjoint xs (insert a ys)
insert-preserves-disjointʳ d p = disjoint-sym (insert-preserves-disjointˡ (disjoint-sym d) p) 

∈-disjoint-intersection-of-unions : ∀ {a xs ys zs} -> Disjoint xs ys -> a ∈ (xs ∪ zs) -> a ∈ (ys ∪ zs) -> a ∈ zs
∈-disjoint-intersection-of-unions {a} {xs} {ys} {zs} d p q with ∪∈ {a} {xs} {zs} p
... | inj₂ a∈zs = a∈zs
... | inj₁ a∈xs with ∪∈ {a} {ys} {zs} q
... | inj₂ a∈zs = a∈zs
... | inj₁ a∈ys = ⊥-elim (d ≈-refl a∈xs a∈ys)

remove-preserves-disjointˡ : ∀ {a xs ys} -> (a∈xs : a ∈ xs) -> Disjoint xs ys -> Disjoint (remove a∈xs) ys
remove-preserves-disjointˡ a∈xs d x≈y x∈rem y∈ys = d x≈y (remove-⊆ a∈xs x∈rem) y∈ys

remove-preserves-disjointʳ : ∀ {a xs ys} -> (a∈ys : a ∈ ys) -> Disjoint xs ys -> Disjoint xs (remove a∈ys)
remove-preserves-disjointʳ a∈ys d = disjoint-sym (remove-preserves-disjointˡ a∈ys (disjoint-sym d))

---------------------------
-- Paritioning of Unions --
---------------------------

-- If at least one element in the right is not in the left, then the union is strictly
-- larger than the left.
--
-- This actually turned out to be tricky to do directly.
-- Here's a sketch of the proof that ended up being the nicest in agda.
--
-- In general, any element x is uniquely either:
--   * In the left only, or
--   * In the right only, or
--   * In both.
-- In other words, if we formulate the above as three subsets of the union,
-- then those subsets are all disjoint.
--
-- Consider (xs ∪ ys).
-- xs consists of all elements which are in left-only and both.
-- ys consists of all elements which are in right-only and both.
-- The overall union consists of all three.
--
-- Let L, R, and B denote the sizes of these disjoint collections.
-- size xs ≡ L + B
-- size ys ≡ R + B
-- size union ≡ L + R + B
--
-- It follows that (size union > size xs) when R is nonempty, and similarly for ys and L.

-- And so, without further ado....
record PartitionedUnion (xs ys : SortedList) : Set where
  constructor PU
  field
    -- The 3 pieces.
    left  : SortedList
    right : SortedList
    both  : SortedList

    preserves-xs : xs ≈L (left ∪ both)
    preserves-ys : ys ≈L (right ∪ both)

    lb-disjoint : Disjoint left both
    rb-disjoint : Disjoint right both
    lr-disjoint : Disjoint left right

  -- The conditions for membership in left, right or both. We
  -- can recover them from the above.
  preserves-∪ : (xs ∪ ys) ≈L ((left ∪ right) ∪ both)
  preserves-∪ =
    begin
      (xs ∪ ys)
    ≈⟨ ∪-preserves-≈L preserves-xs preserves-ys ⟩
      (left ∪ both) ∪ (right ∪ both)
    ≈⟨ ≈L-sym (∪-assoc (left ∪ both) right both) ⟩
      ((left ∪ both) ∪ right) ∪ both
    ≈⟨ ∪-preserves-≈L (∪-assoc left both right) (≈L-refl {both}) ⟩
      (left ∪ (both ∪ right)) ∪ both
    ≈⟨ ∪-preserves-≈L (∪-preserves-≈L (≈L-refl {left}) (∪-comm both right)) (≈L-refl {both}) ⟩
      (left ∪ (right ∪ both)) ∪ both
    ≈⟨ (∪-preserves-≈L (≈L-sym (∪-assoc left right both)) (≈L-refl {both})) ⟩
      ((left ∪ right) ∪ both) ∪ both
    ≈⟨ ∪-assoc (left ∪ right) both both ⟩
      (left ∪ right) ∪ (both ∪ both)
    ≈⟨  ∪-preserves-≈L (≈L-refl {left ∪ right}) (∪-cancelˡ (≈L-refl {both})) ⟩
      (left ∪ right) ∪ both
    ∎

  ∈l : ∀ {a} -> a ∈ xs -> a ∉ ys -> a ∈ left
  ∈l a∈xs a∉ys with ≈L-preserves-∈ a∈xs preserves-xs | ≈L-preserves-∉ a∉ys preserves-ys
  ... | a∈lb | a∉rb with ∪∈ a∈lb
  ... | inj₁ a∈l = a∈l
  ... | inj₂ a∈b = ⊥-elim (a∉rb (∈∪ʳ right a∈b))

  ∉l : ∀ {a} -> a ∉ xs → a ∉ left
  ∉l a∉xs a∈l with ≈L-preserves-∉ a∉xs preserves-xs
  ... | a∉lb = ∉∪ˡ a∉lb a∈l

  ∈r : ∀ {a} -> a ∉ xs -> a ∈ ys -> a ∈ right
  ∈r a∉xs a∈ys with ≈L-preserves-∈ a∈ys preserves-ys | ≈L-preserves-∉ a∉xs preserves-xs
  ... | a∈rb | a∉lb with ∪∈ a∈rb
  ... | inj₁ a∈r = a∈r
  ... | inj₂ a∈b = ⊥-elim (a∉lb (∈∪ʳ left a∈b))

  ∉r : ∀ {a} -> a ∉ ys -> a ∉ right
  ∉r a∉ys a∈r with ≈L-preserves-∉ a∉ys preserves-ys
  ... | a∉rb = ∉∪ˡ a∉rb a∈r

  ∈b : ∀ {a} -> a ∈ xs -> a ∈ ys -> a ∈ both
  ∈b {a} a∈xs a∈ys with ≈L-preserves-∈ a∈xs preserves-xs | ≈L-preserves-∈ a∈ys preserves-ys
  ... | a∈lb | a∈rb = ∈-disjoint-intersection-of-unions lr-disjoint a∈lb a∈rb

  ∉bx : ∀ {a} -> a ∉ xs -> a ∉ both
  ∉bx {a} a∉xs a∈b with ≈L-preserves-∉ a∉xs preserves-xs
  ... | a∉lb =  ∉∪ʳ {a} {left} {both} a∉lb a∈b

  ∉by : ∀ {a} -> a ∉ ys -> a ∉ both
  ∉by {a} a∉ys a∈b with ≈L-preserves-∉ a∉ys preserves-ys
  ... | a∉rb = ∉∪ʳ {a} {right} {both} a∉rb a∈b

open PartitionedUnion

preserves-len-xs : ∀ {xs ys} -> (p : PartitionedUnion xs ys) -> length xs ≡ (length (left p)) + (length (both p))
preserves-len-xs p = trans (≈L-preserves-length (preserves-xs p)) (disjoint-union-length (lb-disjoint p))

preserves-len-ys : ∀ {xs ys} -> (p : PartitionedUnion xs ys) -> length ys ≡ (length (right p)) + (length (both p))
preserves-len-ys p = trans (≈L-preserves-length (preserves-ys p)) (disjoint-union-length (rb-disjoint p))

preserves-len-union : ∀ {xs ys} -> (p : PartitionedUnion xs ys) -> length (xs ∪ ys) ≡ (length (left p)) + (length (right p)) + (length (both p))
preserves-len-union p = trans (≈L-preserves-length (preserves-∪ p))
                       (trans (disjoint-union-length (disjoint-sym (disjoint-∪ (disjoint-sym (lb-disjoint p)) (disjoint-sym (rb-disjoint p)))))
                        (cong (_+ length (both p)) (disjoint-union-length (lr-disjoint p))))

∪-len-right-nonempty : ∀ {xs ys} -> (p : PartitionedUnion xs ys) -> length (right p) > 0 -> length (xs ∪ ys) > length xs
∪-len-right-nonempty p r>0
  rewrite preserves-len-xs p
  rewrite preserves-len-union p
  rewrite +-assoc (length (left p)) (length (right p)) (length (both p))
  rewrite +-comm (length (right p)) (length (both p))
  rewrite sym (+-assoc (length (left p)) (length (both p)) (length (right p)))
  = m<m+n (length (left p) + length (both p)) {length (right p)} r>0

right-ne : ∀ {a xs ys} -> (p : PartitionedUnion xs ys) -> a ∉ xs -> a ∈ ys -> NonEmpty (right p)
right-ne p a∉xs a∈ys with right p | ∈r p a∉xs a∈ys
... | (cons z zs fz) | here _ = cons z zs fz
... | (cons z zs fz) | there _ = cons z zs fz


empty-partition : PartitionedUnion [] []
left empty-partition = []
right empty-partition = []
both empty-partition = []
preserves-xs empty-partition = []
preserves-ys empty-partition = []
lb-disjoint empty-partition = λ {_ ()}
rb-disjoint empty-partition = λ {_ ()}
lr-disjoint empty-partition = λ {_ ()}

update-left : {xs ys : SortedList} (x : X) (fx : x # xs) -> x ∉ ys -> PartitionedUnion xs ys -> PartitionedUnion (cons x xs fx) ys
update-left {xs} {ys} x fx x∉ys p
  = PU (insert x (left p)) (right p) (both p)
       pxs (preserves-ys p)
       (insert-preserves-disjointˡ (lb-disjoint p) (∉by p x∉ys)) (rb-disjoint p) (insert-preserves-disjointˡ (lr-disjoint p) (∉r p x∉ys))
       where
  pxs : cons x xs fx ≈L (insert x (left p) ∪ both p)
  pxs =
    begin
      cons x xs fx
    ≈⟨ ≡→≈L (sym (insert-consview fx)) ⟩
      insert x xs
    ≈⟨ insert-preserves-≈L ≈-refl (preserves-xs p) ⟩
      insert x (left p ∪ both p)
    ≈⟨ ≈L-sym (∪-insert-assoc x (left p) (both p)) ⟩
      (insert x (left p) ∪ both p)
    ∎

update-right : {xs ys : SortedList} (y : X) (fy : y # ys) -> y ∉ xs -> PartitionedUnion xs ys -> PartitionedUnion xs (cons y ys fy)
update-right {xs} {ys} y fy y∉xs p
  = PU (left p) (insert y (right p)) (both p)
       (preserves-xs p) pys
       (lb-disjoint p) (insert-preserves-disjointˡ (rb-disjoint p) (∉bx p y∉xs)) (insert-preserves-disjointʳ (lr-disjoint p) (∉l p y∉xs))
       where
  pys : cons y ys fy ≈L (insert y (right p) ∪ both p)
  pys =
    begin
      cons y ys fy
    ≈⟨ ≡→≈L (sym (insert-consview fy)) ⟩
      insert y ys
    ≈⟨ insert-preserves-≈L ≈-refl (preserves-ys p) ⟩
      insert y (right p ∪ both p)
    ≈⟨ ≈L-sym (∪-insert-assoc y (right p) (both p)) ⟩
      (insert y (right p) ∪ both p)
    ∎

update-both : {xs ys : SortedList} (x : X) (fx : x # xs) -> x ∈ ys -> PartitionedUnion xs ys -> PartitionedUnion (cons x xs fx) ys
update-both {xs} {ys} x fx x∈ys p
  = PU (left p) (remove {x} {right p} (∈r p (#→∉ fx) x∈ys)) (insert x (both p))
       pxs pys
       (insert-preserves-disjointʳ (lb-disjoint p) (∉l p (#→∉ fx)))
       (insert-preserves-disjointʳ (remove-preserves-disjointˡ {x} {right p} {both p} (∈r p (#→∉ fx) x∈ys) (rb-disjoint p))
         (remove-removes-correct-elem (∈r p (#→∉ fx) x∈ys)))
       (remove-preserves-disjointʳ (∈r p (#→∉ fx) x∈ys) (lr-disjoint p) )
       where
  pxs : cons x xs fx ≈L (left p ∪ (insert x (both p)))
  pxs =
    begin
      cons x xs fx
    ≈⟨ ≡→≈L (sym (insert-consview fx)) ⟩
      insert x xs
    ≈⟨ insert-preserves-≈L ≈-refl (preserves-xs p) ⟩
      insert x (left p ∪ both p)
    ≈⟨ insert-preserves-≈L ≈-refl (∪-comm (left p) (both p)) ⟩
      insert x (both p ∪ left p)
    ≈⟨ ≈L-sym (∪-insert-assoc x (both p) (left p)) ⟩
      (insert x (both p) ∪ left p)
    ≈⟨ ∪-comm (insert x (both p)) (left p) ⟩
      (left p ∪ insert x (both p))
    ∎
  pys : ys ≈L ((remove (∈r p (#→∉ fx) x∈ys)) ∪ (insert x (both p)))
  pys = -- fx → x∉xs; x∈ys
    begin
      ys
    ≈⟨ preserves-ys p ⟩
      (right p ∪ both p)
    ≈⟨ remove-insert-union-lem (∈r p (#→∉ fx) x∈ys) (∉bx p (#→∉ fx)) ⟩
      (remove (∈r p (#→∉ fx) x∈ys) ∪ insert x (both p))
    ∎


partition-by-origin : (xs ys : SortedList) -> PartitionedUnion xs ys
partition-by-origin [] [] = empty-partition
partition-by-origin [] (cons y ys fy) =  update-right y fy (λ {()}) (partition-by-origin [] ys) 
partition-by-origin (cons x xs fx) ys with partition-by-origin xs ys | x ∈? ys
... | k | yes x∈ys = update-both x fx x∈ys k -- x in both
... | k | no x∉ys  = update-left x fx x∉ys k -- x in left only




-----------------------
-- Union Size Lemmas --
-----------------------

∪-size-∉ˡ : ∀ {a} {xs ys : SortedList} -> a ∉ xs -> a ∈ ys -> length (xs ∪ ys) > length xs
∪-size-∉ˡ {a} {xs} {cons y ys fy} a∉xs a∈ys with partition-by-origin xs (cons y ys fy)
... | p = ∪-len-right-nonempty p (NonEmpty-length (right-ne p a∉xs a∈ys))

-- The union least as large as either side.
∪-sizeˡ : (xs ys : SortedList) -> length (xs ∪ ys) ≥ length xs
∪-sizeˡ [] ys = z≤n
∪-sizeˡ (cons x xs fx) [] rewrite ∪-idʳ xs rewrite insert-consview fx = ≤-refl
∪-sizeˡ (cons x xs fx) (cons y ys fy) with x ∈? (cons y ys fy)
... | no x∉ys
  rewrite insert-length∉ (∉∪ (#→∉ fx) x∉ys)
  = s≤s (∪-sizeˡ xs (cons y ys fy))
... | yes x∈ys
  rewrite insert-length∈ {x} {xs ∪ cons y ys fy} (∈∪ʳ xs x∈ys)
  = ∪-size-∉ˡ (#→∉ fx) x∈ys

∪-sizeʳ : (xs ys : SortedList) -> length (xs ∪ ys) ≥ length ys
∪-sizeʳ xs ys rewrite ≈L-preserves-length (∪-comm xs ys) = ∪-sizeˡ ys xs


-- Stating the above in terms of some k, which is how we need it for the closure finiteness proof.
∪-size-kʳ : ∀ {k} {xs ys : SortedList} -> k ≥ length (xs ∪ ys) -> k ≥ length xs
∪-size-kʳ {k} {xs} {ys} p = ≤-trans (∪-sizeˡ xs ys) p

∪-size-kˡ : ∀ {k} {xs ys : SortedList} -> k ≥ length (xs ∪ ys) -> k ≥ length ys
∪-size-kˡ {k} {xs} {ys} p = ≤-trans (∪-sizeʳ xs ys) p

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

<-lex-STO : IsStrictTotalOrder _≈L_ _<-lex_
IsStrictTotalOrder.isEquivalence <-lex-STO = isEquivalence
IsStrictTotalOrder.trans <-lex-STO = <-lex-trans
IsStrictTotalOrder.compare <-lex-STO = compareL

<-lex-concat : ∀ xs {ys'} (ys : NonEmpty ys') g → xs <-lex (xs ++[ g ] ys')
<-lex-concat [] (cons y ys fy) g = []
<-lex-concat (cons x xs fx) ys g = there ≈-refl (<-lex-concat xs ys (Gluable-weaken g))

<L-trans = <-lex-trans
_<L_ = _<-lex_
<L-STO = <-lex-STO


{-
concat-<L-eql : ∀ l {r r'} g g' -> r <L r' -> (l ++[ g ] r) <L (l ++[ g' ] r')
concat-<L-eql l g g' x = {!!}

ins-preserves-<L : ∀ x l {r r'} g g' p → r <L r' → proj₁ (ins l r x g p) <L proj₁ (ins l r' x g' p)
ins-preserves-<L x l {[]} {cons r rs fr} g g' p [] with compare x r
... | tri< a ¬b ¬c = <L-concat (concat l (x ∷# []) p) (cons r rs fr) _
... | tri≈ ¬a b ¬c = concat-<L-eql l p g' (there b {!!}) -- uhhhh this is a problem. rs might be empty, in which case the goal is impossible
... | tri> ¬a ¬b c = {!!}
ins-preserves-<L x l {cons r rs fr} {cons s ss fs} g g' p (here r<s) = {!!}
ins-preserves-<L x l {cons r rs fr} {cons s ss fs} g g' p (there r≈s rs<ss) = {!!}

insert-preserves-<L : ∀ x {xs ys} → xs <L ys → insert x xs <L insert x ys
insert-preserves-<L x xs<ys = ins-preserves-<L x [] ([]gluable-l _) ([]gluable-l _) [] xs<ys

-- this is already clearly false. counterexample:
-- xs = [0,1,2,3], as = [0,1], bs = [2,3]
-- as < bs, but the unions are equal.
-- For this lemma to be true there also needs to be an extra disjointness property
∪-preservesˡ-<L : ∀ {as bs} xs → as <L bs → (xs ∪ as) <L (xs ∪ bs)
∪-preservesˡ-<L [] as<bs = as<bs
∪-preservesˡ-<L (cons x xs fx) as<bs = insert-preserves-<L x (∪-preservesˡ-<L xs as<bs)

[]-minimal : ∀ {xs} → [] ≢ xs → [] <L xs
[]-minimal {[]} ¬refl = ⊥-elim (¬refl refl)
[]-minimal {cons x xs fx} _ = []
-}

{-
-- Other More Different Ordering --
-- Want xs < ys if xs is smaller in length. If they are the same length, then
-- fall back on lexicographic order. This may be tricky to do in a proof relevant way.

data LenEncoded : ℕ → SortedList → Set where
  [] : LenEncoded 0 []
  cons : ∀ x {xs} {n : ℕ} → LenEncoded n xs → (x#xs : x # xs) → LenEncoded (suc n) (cons x xs x#xs)

encode-len : (xs : SortedList) → LenEncoded (length xs) xs
encode-len [] = []
encode-len (cons x xs x#xs) = cons x (encode-len xs) x#xs

data _<L'_ : {xs ys : SortedList} {n m : ℕ} → LenEncoded n xs → LenEncoded m ys → Set where
  len : ∀ {n m xs ys} → (nxs : LenEncoded n xs) (mys : LenEncoded m ys) → nxs <L' mys
  here : ∀ {x xs x#xs y ys y#ys n} {nxs : LenEncoded n xs} {nys : LenEncoded n ys} → x < y → (cons x nxs x#xs) <L' (cons y nys y#ys)
  there : ∀ {x xs x#xs y ys y#ys n} {nxs : LenEncoded n xs} {nys : LenEncoded n ys} → x ≈ y → nxs <L' nys → (cons x nxs x#xs) <L' (cons y nys y#ys)

_<L_ : SortedList → SortedList → Set
xs <L ys = (encode-len xs) <L' (encode-len ys)


<L-trans : ∀ {xs ys zs} → xs <L ys → ys <L zs → xs <L zs
<L-trans {xs} {[]} {zs} (len .(encode-len xs) .(encode-len [])) (len .(encode-len []) .(encode-len zs)) = {!!}
<L-trans {xs} {cons a ys x} {zs} p q = {!!}
-}

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
