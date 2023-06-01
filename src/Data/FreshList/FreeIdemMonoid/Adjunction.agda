{-# OPTIONS --type-in-type --with-K  #-}
-- Accepting heartache to keep the headache at bay --

open import Level renaming (suc to lsuc)

{-
open import Algebra
open import Function

open import Data.Product hiding (map)
open import Data.Sum
open import Data.List.Fresh
open import Data.Empty


open import Relation.Binary hiding (NonEmpty; StrictTotalOrder)

open import Relation.Nullary.Decidable hiding (map)
-}

open import Algebra.Structure.OICM
open import Relation.Binary.PropositionalEquality renaming (isEquivalence to ≡-isEquivalence)

module Data.FreshList.FreeIdemMonoid.Adjunction where

open import Data.Empty
open import Data.Sum
open import Data.Product
open import Algebra.Structures
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Structures
open import Function

open import Axiom.UniquenessOfIdentityProofs.WithK

open import Data.FreshList.InductiveInductive
open import Data.FreshList.FreeIdemMonoid
open import Data.FreshList.FreeIdemMonoid.Properties
open import Data.FreshList.FreeIdemMonoid.Structure

open import Category
open import Category.Adjunctions

module _
  {X : Set}
  {_≠_ : X → X → Set}
  (≠-AR : IsPropDecApartnessRelation _≡_ _≠_)
  where

  idemMonoid : IsIdempotentMonoidWithPropDecApartness _≡_ (λ x y → ¬ (x ≡ y)) (union ≠-AR) []
  IsMagma.isEquivalence (IsSemigroup.isMagma (IsMonoid.isSemigroup (IsIdempotentMonoidWithPropDecApartness.isICM idemMonoid))) = ≡-isEquivalence
  IsMagma.∙-cong (IsSemigroup.isMagma (IsMonoid.isSemigroup (IsIdempotentMonoidWithPropDecApartness.isICM idemMonoid))) = cong₂ (union ≠-AR)
  IsSemigroup.assoc (IsMonoid.isSemigroup (IsIdempotentMonoidWithPropDecApartness.isICM idemMonoid)) = assoc ≠-AR
  IsMonoid.identity (IsIdempotentMonoidWithPropDecApartness.isICM idemMonoid) = (unitˡ ≠-AR , unitʳ ≠-AR)
  IsIdempotentMonoidWithPropDecApartness.idempotent idemMonoid = idem ≠-AR
  IsIdempotentMonoidWithPropDecApartness.isApartness idemMonoid = denialApartness ≡-isEquivalence (WithIrr.lift-decEq _≠_ (IsPropDecApartnessRelation.prop ≠-AR) (_≟_ ≠-AR))

---------------------------------------------------------------------------
-- The Category of Idempotent Monoids with Decidable Apartness relations --
---------------------------------------------------------------------------

record IdempotentMonoidWithPropDecApartness : Set where
  constructor MkIcm
  field
    Carrier : Set
    _¬≈_ : Carrier → Carrier → Set
    _∙_ : Carrier → Carrier → Carrier
    ε : Carrier
    proof : IsIdempotentMonoidWithPropDecApartness _≡_ _¬≈_ _∙_ ε
open IdempotentMonoidWithPropDecApartness

record IcmMorphism (A B : IdempotentMonoidWithPropDecApartness) : Set where
  constructor MkIcmMorphism
  private
    module A = IdempotentMonoidWithPropDecApartness A
    module B = IdempotentMonoidWithPropDecApartness B

  field
    fun : Carrier A → Carrier B
    preserves-ε : fun (A.ε) ≡ B.ε
    preserves-∙ : ∀ x y → fun (x A.∙ y) ≡ (fun x) B.∙ (fun y)
open IcmMorphism

icm-id : ∀ {A} → IcmMorphism A A
fun icm-id = Function.id
preserves-ε icm-id = refl
preserves-∙ icm-id _ _ = refl

icm-comp : ∀ {A B C} → IcmMorphism A B → IcmMorphism B C → IcmMorphism A C
fun (icm-comp f g) = (fun g) ∘ (fun f)
preserves-ε (icm-comp f g) = trans (cong (fun g) (preserves-ε f)) (preserves-ε g)
preserves-∙ (icm-comp f g) _ _ = trans (cong (fun g) (preserves-∙ f _ _)) (preserves-∙ g _ _)


eqIcmMorphism : ∀ {A B} → {f g : IcmMorphism A B} → fun f ≡ fun g → f ≡ g
eqIcmMorphism {A} {B} {MkIcmMorphism .f refl p∙} {MkIcmMorphism f refl q∙} refl
  = cong (MkIcmMorphism f refl) ((ext λ x → ext λ y → uip (p∙ x y) (q∙ x y)))


ICM : Category
Category.Obj ICM = IdempotentMonoidWithPropDecApartness
Category.Hom ICM = IcmMorphism
Category.id ICM = icm-id
Category.comp ICM = icm-comp
Category.assoc ICM {A} {B} {C} {D} {f} {g} {h} = eqIcmMorphism refl
Category.identityˡ ICM {A} {B} {f} = eqIcmMorphism refl
Category.identityʳ ICM {A} {B} {f} = eqIcmMorphism refl


-------------------------------------------------------------
-- The Category of Propositional Decidable Apartness Types --
-------------------------------------------------------------

record DecApartnessType : Set where
  constructor MkAT
  field
    Carrier : Set
    _¬≈_ : Carrier → Carrier → Set
    proof : IsPropDecApartnessRelation _≡_ _¬≈_
open DecApartnessType

AT : Category
Category.Obj AT = DecApartnessType
Category.Hom AT X Y = Carrier X → Carrier Y
Category.id AT = id
Category.comp AT f g = g ∘ f
Category.assoc AT = refl
Category.identityˡ AT = refl
Category.identityʳ AT = refl

---------------------------
-- The Forgetful Functor --
---------------------------

open Functor

FORGET : Functor ICM AT
act FORGET (MkIcm S _¬≈_ _∙_ ε icm) = MkAT S _¬≈_ (IsIdempotentMonoidWithPropDecApartness.isApartness icm)
fmap FORGET f = fun f
identity FORGET = refl
homomorphism FORGET = refl

----------------------
-- The Free Functor --
----------------------

UL-map : {X Y : DecApartnessType} → (Carrier X → Carrier Y) → UniqueList (proof X) → UniqueList (proof Y)
UL-map f [] = []
UL-map {X} {Y} f (cons x xs fx) = cons (f x) (_-[_] (proof Y) (UL-map {X} {Y} f xs) (f x) ) (remove-removes (proof Y) (UL-map {X} {Y} f xs) (f x))

-- insert (proof Y) (f x) (UL-map {X} {Y} f xs)

map-remove : {X Y : DecApartnessType} →
             let _-[_]X = _-[_] (proof X)
                 _-[_]Y = _-[_] (proof Y) in
             (f : Carrier X → Carrier Y) → (xs : UniqueList (proof X)) → (y : Carrier X) →
             (UL-map {X} {Y} f (xs -[ y ]X)) -[ f y ]Y ≡ (UL-map {X} {Y} f xs) -[ f y ]Y
map-remove f [] y = refl
map-remove {X} {Y} f (cons x xs x#xs) y with IsPropDecApartnessRelation.dec (proof X) x y | IsPropDecApartnessRelation.dec (proof Y) (f x) (f y) in eqfxfy
... | inj₁ x≡y  | inj₁ fx≡fy  = cong (_-[_] (proof Y) (UL-map f xs)) (sym fx≡fy)
... | inj₁ x≡y  | inj₂ ¬fx≈fy = ⊥-elim (IsPropDecApartnessRelation.irrefl (proof Y) (cong f x≡y) ¬fx≈fy)
... | inj₂ ¬x≈y | inj₁ fx≡fy  rewrite eqfxfy = begin
  mapf (xs -[ y ]X) -[ f x ]Y
    ≡⟨ cong (λ z → mapf (xs -[ y ]X) -[ z ]Y) fx≡fy ⟩
  mapf (xs -[ y ]X) -[ f y ]Y
    ≡⟨ map-remove {X} {Y} f xs y ⟩
  mapf xs -[ f y ]Y
    ≡⟨ cong (λ z → mapf xs -[ z ]Y) (sym fx≡fy) ⟩
  mapf xs -[ f x ]Y
    ∎ where
      open ≡-Reasoning
      mapf = UL-map {X} {Y} f
      unionX = union (proof X)
      unionY = union (proof Y)
      _-[_]X = _-[_] (proof X)
      _-[_]Y = _-[_] (proof Y)

... | inj₂ ¬x≈y | inj₂ ¬fx≈fy rewrite eqfxfy = WithIrr.cons-cong _ (IsPropDecApartnessRelation.prop (proof Y)) refl (begin
  (mapf (xs -[ y ]X) -[ f x ]Y) -[ f y ]Y
    ≡⟨ -[]-order-irrelevant (proof Y) (mapf (xs -[ y ]X)) (f x) (f y) ⟩
  (mapf (xs -[ y ]X) -[ f y ]Y) -[ f x ]Y
    ≡⟨ cong (_-[ f x ]Y) (map-remove {X} {Y} f xs y) ⟩
  (mapf xs -[ f y ]Y) -[ f x ]Y
    ≡⟨ -[]-order-irrelevant (proof Y) (mapf xs) (f y) (f x) ⟩
  (mapf xs -[ f x ]Y) -[ f y ]Y
    ∎) where
      open ≡-Reasoning
      mapf = UL-map {X} {Y} f
      unionX = union (proof X)
      unionY = union (proof Y)
      _-[_]X = _-[_] (proof X)
      _-[_]Y = _-[_] (proof Y)

map-union : {X Y : DecApartnessType} → (f : Carrier X → Carrier Y) → (xs ys : UniqueList (proof X)) →
            UL-map {X} {Y} f (union (proof X) xs ys) ≡ union (proof Y) (UL-map {X} {Y} f xs) (UL-map {X} {Y} f ys)
map-union f [] ys = refl
map-union {X} {Y} f (cons x xs x#xs) ys = WithIrr.cons-cong _ (IsPropDecApartnessRelation.prop (proof Y)) refl (begin
  mapf (unionX xs ys -[ x ]X) -[ f x ]Y
    ≡⟨ cong (λ w → mapf w -[ f x ]Y) (remove-union (proof X) xs ys x)  ⟩
  mapf (unionX (xs -[ x ]X) (ys -[ x ]X)) -[ f x ]Y
    ≡⟨ cong (λ w → mapf (unionX w (ys -[ x ]X)) -[ f x ]Y) (remove-fresh-idempotent (proof X) xs x x#xs) ⟩
  mapf (unionX xs (ys -[ x ]X)) -[ f x ]Y
    ≡⟨ cong (_-[ f x ]Y) (map-union {X} {Y} f xs (ys -[ x ]X)) ⟩
  unionY (mapf xs) (mapf (ys -[ x ]X)) -[ f x ]Y
    ≡⟨ remove-union (proof Y) (mapf xs) (mapf (ys -[ x ]X)) (f x) ⟩
  unionY (mapf xs -[ f x ]Y) ((mapf (ys -[ x ]X)) -[ f x ]Y)
    ≡⟨ cong₂ unionY
             (sym (remove-fresh-idempotent (proof Y) (mapf xs -[ f x ]Y) (f x) (remove-removes (proof Y) (mapf xs) (f x))))
             (map-remove {X} {Y} f ys x) ⟩
  unionY (mapf xs -[ f x ]Y -[ f x ]Y) (mapf ys -[ f x ]Y)
    ≡⟨ sym (remove-union (proof Y) (mapf xs -[ f x ]Y) (mapf ys) (f x)) ⟩
  unionY (mapf xs -[ f x ]Y) (mapf ys) -[ f x ]Y
  ∎) where
    open ≡-Reasoning
    mapf = UL-map {X} {Y} f
    unionX = union (proof X)
    unionY = union (proof Y)
    _-[_]X = _-[_] (proof X)
    _-[_]Y = _-[_] (proof Y)

UNIQUELIST : Functor AT ICM
act UNIQUELIST (MkAT X _¬≈_ isAT) = MkIcm (UniqueList isAT) _ (union isAT) [] (idemMonoid isAT)
fmap UNIQUELIST {X} {Y} f = MkIcmMorphism (UL-map {X} {Y} f) refl (map-union {X} {Y} f)
identity UNIQUELIST {X} = eqIcmMorphism (ext lemma)
  where
    lemma : ∀ xs → UL-map id xs ≡ xs
    lemma [] = refl
    lemma (cons x xs x#xs) = WithIrr.cons-cong _ (IsPropDecApartnessRelation.prop (proof X)) refl
                                               (trans (cong (λ w → _-[_] (proof X) w x) (lemma xs) )
                                                      (remove-fresh-idempotent (proof X) xs x x#xs))
homomorphism UNIQUELIST {X} {Y} {Z} {f} {g} = eqIcmMorphism (ext lemma)
  where
    lemma : ∀ xs → UL-map (λ x → g (f x)) xs ≡ UL-map g (UL-map f xs)
    lemma [] = refl
    lemma (cons x xs x#xs) = WithIrr.cons-cong _ (IsPropDecApartnessRelation.prop (proof Z)) refl
                                               (begin
                                                 mapgf  xs -[ g (f x) ]Z
                                                   ≡⟨ cong (_-[ g (f x) ]Z) (lemma xs) ⟩
                                                 mapg (mapf xs) -[ g (f x) ]Z
                                                   ≡⟨ sym (map-remove {Y} {Z} g (mapf xs) (f x)) ⟩
                                                 mapg (mapf xs -[ f x ]Y) -[ g (f x) ]Z
                                                   ∎)
     where
      open ≡-Reasoning
      mapf  = UL-map {X} {Y} f
      mapg  = UL-map {Y} {Z} g
      mapgf = UL-map {X} {Z} (λ x → g (f x))
      _-[_]Y = _-[_] (proof Y)
      _-[_]Z = _-[_] (proof Z)



{-



-}

{-

SL-map-lem : ∀ {X Y : StrictTotalOrder}
           → (f : Carrier X → Carrier Y)
           → (x : Carrier X) (xs : SortedList (proof X))
           → (_∈_ $ proof X) x xs                        -- if x ∈ xs...
           → (_∈_ $ proof Y) (f x) (SL-map {X} {Y} f xs) -- then (f x) ∈ (map f xs)
SL-map-lem {X} {Y} f x (cons y ys fy) (here refl)  = mk-insert∈ (proof Y) (SL-map f ys) (inj₁ refl)
SL-map-lem {X} {Y} f x (cons y ys fy) (there x∈ys) = mk-insert∈ (proof Y) (SL-map f ys) (inj₂ (SL-map-lem f x ys x∈ys))

SL-map-lem2 : ∀ {X Y : StrictTotalOrder}
            → (f : Carrier X → Carrier Y)
            → (x : Carrier Y) (xs : SortedList (proof X)) (ys : SortedList (proof X))
            → _⊆_ (proof X) xs ys                     -- if everything in xs is in ys
            → (_∈_ $ proof Y) x (SL-map {X} {Y} f xs) -- and x is in (map f xs)
            → (_∈_ $ proof Y) x (SL-map {X} {Y} f ys) -- then x is in (map f ys)
SL-map-lem2 {X} {Y} f a (cons x₀ xs fx) ys xs⊆ys x∈fxs with cases-insert∈ (proof Y) (SL-map f xs) x∈fxs
... | inj₁ refl  = SL-map-lem  f x₀ ys (xs⊆ys (here refl))
... | inj₂ a∈fxs = SL-map-lem2 f a xs ys (⊆-weaken (proof X) xs⊆ys) a∈fxs

SL-map-concat : ∀ {X Y : StrictTotalOrder}
             → (f : Carrier X → Carrier Y)
             → (a : Carrier Y)
             → (l : SortedList (proof X)) (r : SortedList (proof X))
             → (g : Gluable (proof X) l r)
             → _∈_ (proof Y) a (SL-map {X} {Y} f (concat (proof X) l r g))
             → (_∈_ (proof Y) a (SL-map {X} {Y} f l)) ⊎ (_∈_ (proof Y) a (SL-map {X} {Y} f r))
SL-map-concat f a [] r g pa = inj₂ pa
SL-map-concat {X} {Y} f a (cons l₀ l fl) r g pa with cases-insert∈ (proof Y) (SL-map f (concat (proof X) l r (Gluable-weaken (proof X) g))) pa
... | inj₁ a≡fl₀ = inj₁ (mk-ins∈-here (proof Y) [] (SL-map f l) (f l₀) _ _ a≡fl₀)
... | inj₂ y with SL-map-concat f a l r (Gluable-weaken (proof X) g) y
... | inj₁ a∈mapl = inj₁ (mk-ins∈-r (proof Y) [] (SL-map f l) (f l₀) _ _ a∈mapl)
... | inj₂ a∈mapr = inj₂ a∈mapr

SL-map-ins : ∀ {X Y : StrictTotalOrder}
           → (f : Carrier X → Carrier Y)
           → (a : Carrier Y)
           → (l : SortedList (proof X)) (x : Carrier X) (r : SortedList (proof X))
           → (g : Gluable (proof X) l r) (p : All (λ z → (_<_ X) z x) l)
           → _∈_ (proof Y) a (SL-map {X} {Y} f (proj₁ $ ins (proof X) l r x g p))
           → (_∈_ (proof Y) a (SL-map {X} {Y} f l)) ⊎ (a ≡ f x) ⊎ (_∈_ (proof Y) a (SL-map {X} {Y} f r))
SL-map-ins f a l x [] g p a∈map with SL-map-concat f a l (x ∷# []) p a∈map
... | inj₁ a∈l = inj₁ a∈l
... | inj₂ (here a≡fx) = inj₂ $ inj₁ a≡fx

SL-map-ins {X} {Y} f a l x (cons r₀ r fr) g p a∈map with compare (proof X) x r₀
SL-map-ins {X} {Y} f a l x (cons r₀ r fr) g p a∈map | tri< x<r₀ x≢r₀ x≯r₀
  with SL-map-concat f a (snoc (proof X) l x p) (cons r₀ r fr) (snoc-all< (proof X) x<r₀) a∈map
SL-map-ins {X} {Y} f a l x (cons r₀ r fr) g p a∈map | tri< x<r₀ x≢r₀ x≯r₀ | inj₁ y with SL-map-concat f a l (x ∷# []) p y 
... | inj₁ a∈mapl = inj₁ a∈mapl
... | inj₂ (here a≡fx) = inj₂ $ inj₁ a≡fx
SL-map-ins {X} {Y} f a l x (cons r₀ r fr) g p a∈map | tri< x<r₀ x≢r₀ x≯r₀ | inj₂ y with cases-insert∈ (proof Y) (SL-map f r) y
... | inj₁ a≡fr₀ = inj₂ $ inj₂ (mk-insert∈ (proof Y) (SL-map f r) (inj₁ a≡fr₀))
... | inj₂ a∈mapr = inj₂ $ inj₂ (mk-insert∈ (proof Y) (SL-map f r) (inj₂ a∈mapr))

SL-map-ins {X} {Y} f a l x (cons r₀ r fr) g p a∈map | tri≈ x≮r₀ x≡r₀ x≯r₀ with SL-map-concat f a l (cons r₀ r fr) g a∈map
... | inj₁ a∈mapl = inj₁ a∈mapl
... | inj₂ y with cases-insert∈ (proof Y) (SL-map f r) y
... | inj₁ a≡fr₀ = inj₂ $ inj₂ (mk-insert∈ (proof Y) (SL-map f r) (inj₁ a≡fr₀))
... | inj₂ a∈mapr = inj₂ $ inj₂ (mk-insert∈ (proof Y) (SL-map f r) (inj₂ a∈mapr))

SL-map-ins {X} {Y} f a l x (cons r₀ r fr) g p a∈map | tri> x≮r₀ x≢r₀ x>r₀ with SL-map-ins f a (snoc (proof X) l r₀ g) x r _ _ a∈map
... | inj₂ (inj₁ a≡fx) = inj₂ $ inj₁ a≡fx
... | inj₂ (inj₂ a∈mapr) = inj₂ $ inj₂ (mk-insert∈ (proof Y) (SL-map f r) (inj₂ a∈mapr))
... | inj₁ y with SL-map-concat f a l (r₀ ∷# []) g y
... | inj₁ a∈mapl = inj₁ a∈mapl
... | inj₂ (here a≡fr₀) = inj₂ $ inj₂ (mk-insert∈ (proof Y) (SL-map f r) (inj₁ a≡fr₀))


SL-map-insert : ∀ {X Y : StrictTotalOrder}
              → (f : Carrier X → Carrier Y)
              → (a : Carrier Y) (x : Carrier X) (xs : SortedList (proof X))
              → _∈_ (proof Y) a (SL-map {X} {Y} f (insert (proof X) x xs))
              →  a ≡ f x ⊎ (_∈_ (proof Y) a (SL-map {X} {Y} f xs))
SL-map-insert {X} {Y} f a x xs pxs with SL-map-ins f a [] x xs ([]gluable-l (proof X) xs) [] pxs
... | inj₂ z = z

-- NB: map does *not* preserve gluability because of the lack of monotonicity, so
-- it therefore does not preserve concat. ie, map f (xs ++ ys) is not (map f xs) ++ (map f ys). This might not even
-- be a well-formed statement. But, we can get there by extensionality (and even avoid hassle by applying it further up
-- the chain, so we don't need to think about ins).


SL-map-preserves-insert : ∀ {X Y}
                        → {f : Carrier X → Carrier Y}
                        → (x : Carrier X) (xs : SortedList (proof X))
                        → SL-map {X} {Y} f (insert (proof X) x xs) ≡ insert (proof Y) (f x) (SL-map {X} {Y} f xs)
SL-map-preserves-insert {X} {Y} {f} x xs = ≈L→≡ (proof Y) (extensionality (proof Y) (SL-map f (insertX x xs)) (insertY (f x) (SL-map {X} {Y} f xs)) (λ z → p z , q z)) where
  insertX = insert (proof X)
  insertY = insert (proof Y)
  insX = ins (proof X)
  insY = ins (proof Y)
  _∈X_ = _∈_ (proof X)
  _∈Y_ = _∈_ (proof Y)

  p : ∀ z → z ∈Y (SL-map {X} {Y} f (insertX x xs)) → z ∈Y (insertY (f x) (SL-map {X} {Y} f xs))
  p z pz = mk-insert∈ (proof Y) (SL-map f xs) (SL-map-insert f z x xs pz)


  q : ∀ z → z ∈Y (insertY (f x) (SL-map {X} {Y} f xs)) → z ∈Y (SL-map {X} {Y} f (insertX x xs))
  q z pz with cases-insert∈ (proof Y) (SL-map f xs) pz
  ... | inj₁ refl = SL-map-lem f x (insertX x xs) (mk-insert∈ (proof X) xs (inj₁ refl))
  ... | inj₂ py = SL-map-lem2 f z xs (insert (proof X) x xs) (λ a∈xs → mk-insert∈ (proof X) xs (inj₂ a∈xs)) py


SL-map-preserves-∪ : {X Y : StrictTotalOrder}
                   → {f : Carrier X → Carrier Y}
                   → (xs ys : SortedList (proof X))
                   → SL-map {X} {Y} f (_∪_ (proof X) xs ys) ≡ _∪_ (proof Y) (SL-map {X} {Y} f xs) (SL-map {X} {Y} f ys)
SL-map-preserves-∪ [] ys = refl
SL-map-preserves-∪ {X} {Y} {f} (cons x xs fx) ys =
  begin
    SL-map f (insertX x (xs ∪X ys))
  ≡⟨ SL-map-preserves-insert {X} {Y} {f} x (xs ∪X ys)  ⟩
    insertY (f x) (SL-map f (xs ∪X ys))
  ≡⟨ cong (insertY (f x)) (SL-map-preserves-∪ {X} {Y} {f} xs ys)  ⟩
    insertY (f x) ((SL-map f xs) ∪Y (SL-map f ys))
  ≡⟨ (sym $ ≈L→≡ (proof Y) (∪-insert-assoc (proof Y) (f x) (SL-map f xs) (SL-map f ys))) ⟩
    (insertY (f x) (SL-map f xs)) ∪Y (SL-map f ys)
  ∎ where open ≡-Reasoning
          insertX = insert (proof X)
          insertY = insert (proof Y)
          _∪X_ = _∪_ (proof X)
          _∪Y_ = _∪_ (proof Y)


SORTEDLIST : Functor AT ICM
act SORTEDLIST (MkSto S _<_ sto) = MkOicm (SortedList sto) (_<L_ sto) (_∪_ sto) [] (SL-isICM sto)
fmap SORTEDLIST {X} {Y} f = MkOicmMorphism (SL-map {X} {Y} f) refl SL-map-preserves-∪
identity SORTEDLIST {X} = eqOicmMorphism (ext lem) where
  lem : ∀ xs → SL-map id xs ≡ xs
  lem [] = refl
  lem (cons x xs fx) = trans (≈L→≡ (proof X) (insert-preserves-≈L (proof X) {x} {x} {SL-map id xs} {xs} refl (≡→≈L (proof X) (lem xs))))
                             (insert-consview (proof X) fx)
homomorphism SORTEDLIST {X} {Y} {Z} {f} {g} = eqOicmMorphism (ext lem) where
  lem : ∀ xs
      → SL-map (g ∘ f) xs
      ≡ (SL-map {Y} {Z} g ∘ SL-map {X} {Y} f) xs
  lem [] = refl
  lem (cons x xs fx) = trans (≈L→≡ (proof Z) (insert-preserves-≈L (proof Z) refl (≡→≈L (proof Z) (lem xs))))
                             (sym $ SL-map-preserves-insert {f = g} (f x) (SL-map {X} {Y} f xs))


-----------------------------------
-- The Free-Forgetful Adjunction --
-----------------------------------

foldr : ∀ {A : StrictTotalOrder} {B : Set} → (Carrier A → B → B) → B → SortedList (proof A) → B
foldr f ε [] = ε
foldr {A} f ε (cons x xs fx) = f x (foldr {A} f ε xs)

-- foldr is the universal property of sorted lists
foldr-universal : ∀ {A} {B : Set}
                → (h : SortedList (proof A) → B)                         -- Given some way 'h' of turning SortedLists of As into Bs...
                → (f : Carrier A → B → B) (e : B)                        -- and some function and initial B to fold with...
                → (h [] ≡ e)                                             -- such that the empty list maps to the initial thing...
                → (∀ x xs (fx : x # xs) → h (cons x xs fx) ≡ f x (h xs)) -- and cons maps to an appropriate application of f...
                → h ≗ foldr {A} {B} f e                                  -- then h is exactly the fold.
foldr-universal h f e base step [] = base
foldr-universal h f e base step (cons x xs fx) =
  begin
    h (cons x xs fx)
  ≡⟨ step x xs fx ⟩
    f x (h xs)
  ≡⟨ cong (f x) (foldr-universal h f e base step xs) ⟩
    foldr f e (cons x xs fx)
  ∎ where open ≡-Reasoning

-- foldr, specialised to functions built from _∙_
foldr-∙ : (A : StrictTotalOrder)
        → (B : OrderedIdempotentCommutativeMonoid)
        → (f : Carrier A → Carrier B)            -- Given a way of turning As into Bs...
        → Carrier (act SORTEDLIST A) → Carrier B -- we get a way for flattening a sorted lists of As into a B
foldr-∙ A B f = foldr {A} (λ a b → (_∙_ B) (f a) b) (ε B)

foldr-∙-preserves-concat : (A : StrictTotalOrder) (B : OrderedIdempotentCommutativeMonoid)
                     → (f : Carrier A → Carrier B)
                     → (xs ys : SortedList (proof A)) (g : Gluable (proof A) xs ys)
                     → foldr-∙ A B f (concat (proof A) xs ys g) ≡ (_∙_ B) (foldr-∙ A B f xs) (foldr-∙ A B f ys)
foldr-∙-preserves-concat A B f [] ys p =
  begin
    foldr-∙ A B f ys
  ≡⟨ (sym $ (identityʳ $ isICM $ proof B) (foldr-∙ A B f ys)) ⟩
    (foldr-∙ A B f ys) ∙' (ε B)
  ≡⟨ (comm $ isICM $ proof B) (foldr-∙ A B f ys) (ε B) ⟩
    (ε B) ∙' (foldr-∙ A B f ys)
  ∎ where open ≡-Reasoning; _∙'_ = _∙_ B
foldr-∙-preserves-concat A B f (cons x xs fx) ys g =
  begin
    foldr-∙ A B f (cons x (concat (proof A) xs ys (Gluable-weaken (proof A) g)) (all→fresh $ concat-fresh (proof A) x xs ys fx g))
  ≡⟨⟩
    (f x) ∙' foldr-∙ A B f (concat (proof A) xs ys (Gluable-weaken (proof A) g))
  ≡⟨ cong (f x ∙'_) (foldr-∙-preserves-concat A B f xs ys (Gluable-weaken (proof A) g)) ⟩
    (f x) ∙' ((foldr-∙ A B f xs) ∙' (foldr-∙ A B f ys))
  ≡⟨ (sym $ (assoc $ isICM $ proof B) (f x) (foldr-∙ A B f xs) (foldr-∙ A B f ys)) ⟩
    ((f x) ∙' (foldr-∙ A B f xs))  ∙' (foldr-∙ A B f ys)
  ≡⟨⟩
    (foldr-∙ A B f (cons x xs fx)) ∙' (foldr-∙ A B f ys)
  ∎ where open ≡-Reasoning; _∙'_ = _∙_ B

foldr-∙-preserves-ins : (A : StrictTotalOrder) (B : OrderedIdempotentCommutativeMonoid)
                    → (f : Carrier A → Carrier B)
                    → (x : Carrier A) (l r : SortedList (proof A)) (g : Gluable (proof A) l r) (p : All (λ y → (_<_ A) y x) l)
                    → foldr-∙ A B f (proj₁ (ins (proof A) l r x g p)) ≡ (_∙_ B) (f x) (foldr-∙ A B f (concat (proof A) l r g))
foldr-∙-preserves-ins A B f x l [] g p =
  begin
    foldr-∙ A B f (proj₁ (ins (proof A) l [] x g p))
  ≡⟨  foldr-∙-preserves-concat A B f l (x ∷# []) p  ⟩
    (foldr-∙ A B f l) ∙' (foldr-∙ A B f (x ∷# []))
  ≡⟨⟩
    (foldr-∙ A B f l) ∙' ((f x) ∙' (ε B))
  ≡⟨ (comm $ isICM $ proof B) (foldr-∙ A B f l) (f x ∙' ε B) ⟩
    ((f x) ∙' (ε B)) ∙' (foldr-∙ A B f l)
  ≡⟨ cong (_∙' foldr-∙ A B f l) ((identityʳ $ isICM $ proof B) (f x)) ⟩
    (f x) ∙' (foldr-∙ A B f l)
  ≡⟨ (sym $ cong (λ xs → (_∙_ B) (f x) (foldr-∙ A B f xs)) (concat-idʳ (proof A) l)) ⟩
    (f x) ∙' (foldr-∙ A B f (concat (proof A) l [] g))
  ∎ where open ≡-Reasoning; _∙'_ = _∙_ B
foldr-∙-preserves-ins A B f x l (cons r₀ r fr) g p with compare (proof A) x r₀
... | tri< a ¬b ¬c =
  begin
    foldr-∙ A B f (concat (proof A) (snoc (proof A) l x p) (cons r₀ r fr) (snoc-all< (proof A) a))
  ≡⟨ foldr-∙-preserves-concat A B f (snoc (proof A) l x p) (cons r₀ r fr) (snoc-all< (proof A) a) ⟩
    (foldr-∙ A B f (snoc (proof A) l x p)) ∙' (foldr-∙ A B f (cons r₀ r fr))
  ≡⟨ cong (_∙' _) (foldr-∙-preserves-concat A B f l (x ∷# []) p) ⟩
    ((foldr-∙ A B f l) ∙' (f x ∙' ε B)) ∙' (f r₀ ∙' foldr-∙ A B f r)
  ≡⟨ cong (_∙' (f r₀ ∙' foldr-∙ A B f r)) ((comm $ isICM $ proof B) (foldr-∙ A B f l) (f x ∙' ε B)) ⟩
    ((f x ∙' ε B) ∙' (foldr-∙ A B f l)) ∙' (f r₀ ∙' foldr-∙ A B f r)
  ≡⟨ (assoc $ isICM $ proof B) _ _ _ ⟩
    (f x ∙' ε B) ∙' ((foldr-∙ A B f l) ∙' (f r₀ ∙' foldr-∙ A B f r))
  ≡⟨ cong (_∙' (foldr-∙ A B f l ∙' (f r₀ ∙' foldr-∙ A B f r))) ((identityʳ $ isICM $ proof B) (f x)) ⟩
    (f x) ∙' ((foldr-∙ A B f l) ∙' (f r₀ ∙' foldr-∙ A B f r))
  ≡⟨⟩
    (f x) ∙' ((foldr-∙ A B f l) ∙' (foldr-∙ A B f (cons r₀ r fr)))
  ≡⟨ cong (f x ∙'_) (sym $ foldr-∙-preserves-concat A B f l (cons r₀ r fr) g) ⟩
    (f x) ∙' (foldr-∙ A B f (concat (proof A) l (cons r₀ r fr) g))
  ∎ where open ≡-Reasoning; _∙'_ = _∙_ B
... | tri≈ ¬a refl ¬c =
  begin
    foldr-∙ A B f (concat (proof A) l (cons x r fr) g)
  ≡⟨ foldr-∙-preserves-concat A B f l (cons x r fr) g ⟩
    foldr-∙ A B f l ∙' (foldr-∙ A B f (cons x r fr))
  ≡⟨⟩
    foldr-∙ A B f l ∙' (f x ∙' foldr-∙ A B f r)
  ≡⟨ cong (λ z → foldr-∙ A B f l ∙' (z ∙' foldr-∙ A B f r)) (sym $ (idem $ isICM $ proof B) _) ⟩
    foldr-∙ A B f l ∙' ((f x ∙' f x) ∙' foldr-∙ A B f r)
  ≡⟨ cong (foldr-∙ A B f l ∙'_) ((assoc $ isICM $ proof B) _ _ _) ⟩
    foldr-∙ A B f l ∙' (f x ∙' (f x ∙' foldr-∙ A B f r))
  ≡⟨ (sym $ (assoc $ isICM $ proof B) _ _ _) ⟩
    (foldr-∙ A B f l ∙' f x) ∙' (f x ∙' foldr-∙ A B f r)
  ≡⟨ cong (_∙' (f x ∙' foldr-∙ A B f r)) ((comm $ isICM $ proof B) _ _) ⟩
    (f x ∙' foldr-∙ A B f l) ∙' (f x ∙' foldr-∙ A B f r)
  ≡⟨ (assoc $ isICM $ proof B) _ _ _ ⟩
    (f x ∙' ((foldr-∙ A B f l) ∙' (f x ∙' foldr-∙ A B f r)))
  ≡⟨⟩
    (f x ∙' ((foldr-∙ A B f l) ∙' (foldr-∙ A B f (cons x r fr))))
  ≡⟨ cong (f x ∙'_) (sym $ foldr-∙-preserves-concat A B f l (cons x r fr) g) ⟩
    (f x) ∙' (foldr-∙ A B f (concat (proof A) l (cons x r fr) g))
  ∎ where open ≡-Reasoning; _∙'_ = _∙_ B
... | tri> ¬a ¬b c =
  begin
    foldr-∙ A B f (proj₁ $ ins (proof A) (snoc (proof A) l r₀ g) r x (snoc-gluable (proof A) (fresh→all fr)) (snoc-all< (proof A) c))
  ≡⟨ foldr-∙-preserves-ins A B f x (snoc (proof A) l r₀ g) r (snoc-gluable (proof A) (fresh→all fr)) (snoc-all< (proof A) c) ⟩
    f x ∙' foldr-∙ A B f (concat (proof A) (snoc (proof A) l r₀ g) r (snoc-gluable (proof A) (fresh→all fr)))
  ≡⟨ cong (λ z → f x ∙' foldr-∙ A B f z)
       {concat (proof A) (concat (proof A) l (r₀ ∷# []) g) r (snoc-gluable (proof A) (fresh→all fr))}
       {concat (proof A) l (concat (proof A) (r₀ ∷# []) r (gluable-singleton (proof A) r₀ r (fresh→all fr))) g}
       (concat-assoc (proof A) l (r₀ ∷# []) r) ⟩
    f x ∙' foldr-∙ A B f (concat (proof A) l (concat (proof A) (r₀ ∷# []) r (gluable-singleton (proof A) r₀ r (fresh→all fr))) g)
  ≡⟨ cong (λ z → f x ∙' foldr-∙ A B f (concat (proof A) l (cons r₀ r z) g)) (fresh-irrelevant _ _) ⟩
    f x ∙' foldr-∙ A B f (concat (proof A) l (cons r₀ r fr) g)
  ∎ where open ≡-Reasoning; _∙'_ = _∙_ B

foldr-∙-preserves-insert : (A : StrictTotalOrder) (B : OrderedIdempotentCommutativeMonoid)
                       → (f : Carrier A → Carrier B)
                       → (x : Carrier A) (xs : SortedList (proof A))
                       → foldr-∙ A B f (insert (proof A) x xs) ≡ (_∙_ B) (f x) (foldr-∙ A B f xs)
foldr-∙-preserves-insert A B f x xs = foldr-∙-preserves-ins A B f x [] xs ([]gluable-l (proof A) xs) []

foldr-∙-preserves-∙ : (A : StrictTotalOrder) (B : OrderedIdempotentCommutativeMonoid)
                  → (f : Carrier A → Carrier B)
                  → (xs ys : SortedList (proof A))
                  → foldr-∙ A B f ((_∪_ (proof A)) xs ys)
                  ≡ (_∙_ B) (foldr-∙ A B f xs) (foldr-∙ A B f ys)
foldr-∙-preserves-∙ A B f [] [] = sym $ (identityʳ $ isICM $ proof B) (ε B)
foldr-∙-preserves-∙ A B f [] (cons y ys fy) =
  begin
    (f y) ∙' foldr-∙' f ys
  ≡⟨ cong (_∙' foldr-∙' f ys)
          (trans (sym $ (identityʳ $ isICM $ proof B) (f y))
                 ((comm $ isICM $ proof B) _ _)) ⟩
    ((ε B) ∙' (f y)) ∙' (foldr-∙' f ys)
  ≡⟨ (assoc $ isICM $ proof B) _ _ _ ⟩
    (ε B) ∙' ((f y) ∙' foldr-∙' f ys)
  ∎ where open ≡-Reasoning; _∙'_ = (_∙_ B); foldr-∙' = foldr-∙ A B
foldr-∙-preserves-∙ A B f (cons x xs fx) ys =
  begin
    foldr-∙' f (insert (proof A) x ((proof A ∪ xs) ys))
  ≡⟨ foldr-∙-preserves-insert A B f x (_∪_ (proof A) xs ys) ⟩
    f x ∙' foldr-∙' f ((proof A ∪ xs) ys)
  ≡⟨  cong (f x ∙'_) (foldr-∙-preserves-∙ A B f xs ys) ⟩
    (f x) ∙' ((foldr-∙' f xs) ∙' (foldr-∙' f ys))
  ≡⟨ sym ((assoc $ isICM $ proof B) _ _ _) ⟩
    ((f x) ∙' (foldr-∙' f xs)) ∙' (foldr-∙' f ys)
  ∎ where open ≡-Reasoning; _∙'_ = (_∙_ B); foldr-∙' = foldr-∙ A B


SL-Adjunction : SORTEDLIST ⊣ FORGET
to SL-Adjunction f x = fun f (x ∷# [])

fun (from SL-Adjunction {A} {B} f) = foldr-∙ A B f
preserves-ε (from SL-Adjunction f) = refl
preserves-∙ (from SL-Adjunction {A} {B} f) = foldr-∙-preserves-∙ A B f

left-inverse-of SL-Adjunction {A} {B} f
  = eqOicmMorphism (ext λ xs →
      sym (foldr-universal (fun f) (λ a → (_∙_ B) (fun f (a ∷# []))) (ε B) (preserves-ε f)
        (λ x xs fx → trans (cong (fun f) (sym $ insert-consview (proof A) fx)) (preserves-∙ f (x ∷# []) xs)) xs))
right-inverse-of SL-Adjunction {A} {B} f = ext λ x → (identityʳ $ isICM $ proof B) (f x)
to-natural SL-Adjunction f g = ext (λ _ → ext (λ _ → refl))
-}
