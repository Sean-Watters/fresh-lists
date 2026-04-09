{-# OPTIONS --safe --cubical-compatible #-}
module Free.Category.Base where

open import Algebra.Structure.PartialMonoid
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product
open import Data.FreshList.InductiveInductive
open import Relation.Binary hiding (REL)
open import Relation.Binary.PropositionalEquality
open import Function as Fun using (_∘′_)


record Category (ℓ : Level) : Set (lsuc (lsuc ℓ)) where
  eta-equality

  field
    Obj : Set (lsuc ℓ)
    Hom : Obj -> Obj -> Set ℓ

  field
    id  : ∀ {A} → Hom A A
    comp : ∀ {A B C} → Hom A B → Hom B C → Hom A C

  field -- laws
    assoc     : ∀ {A B C D} {f : Hom A B} {g : Hom B C}{h : Hom C D} →
                comp f (comp g h) ≡ (comp (comp f g) h)
    identityˡ : ∀ {A B} {f : Hom A B} → comp id f ≡ f
    identityʳ : ∀ {A B} {f : Hom A B} → comp f id ≡ f
open Category

record Functor {ℓ} (C D : Category ℓ) : Set (lsuc ℓ) where
  eta-equality
  private
    module C = Category C
    module D = Category D

  field
    act : C.Obj → D.Obj
    fmap : ∀ {X Y} (f : C.Hom X Y) → D.Hom (act X) (act Y)

  field -- laws
    identity     : ∀ {X} → fmap (C.id {X}) ≡ D.id {act X}
    homomorphism : ∀ {X Y Z} {f : C.Hom X Y}{g : C.Hom Y Z} →
                   fmap (C.comp f g) ≡ D.comp (fmap f) (fmap g)
open Functor

idFunctor : ∀ {ℓ} {C : Category ℓ} -> Functor C C
act idFunctor X = X
fmap idFunctor f = f
identity idFunctor = refl
homomorphism idFunctor = refl

compFunctor : ∀ {ℓ} {A B C : Category ℓ} -> Functor A B → Functor B C → Functor A C
act (compFunctor F G) =  (act G) ∘′ (act F)
fmap (compFunctor F G) f = fmap G (fmap F f)
identity (compFunctor F G) = trans (cong (fmap G) (identity F)) (identity G)
homomorphism (compFunctor F G) = trans (cong (fmap G) (homomorphism F)) (homomorphism G)


------------------
------------------
------------------




-- Category where objects are sets plus relations, and morphisms are set functions which ignore the relations.
-- It's almost the category of graphs, excepts the morphisms ignore the edges.
-- Is this something like the grothendieck construction of the slice category of REL?
GRAPH⁻ : ∀ ℓ → Category (lsuc ℓ)
GRAPH⁻ ℓ .Obj = Σ[ X ∈ Set (lsuc ℓ) ] (X → X → Set ℓ)
GRAPH⁻ ℓ .Hom (X , R) (X' , R') = X → X'
GRAPH⁻ ℓ .id x = x
GRAPH⁻ ℓ .comp f g = g ∘′ f
GRAPH⁻ ℓ .assoc = refl
GRAPH⁻ ℓ .identityˡ = refl
GRAPH⁻ ℓ .identityʳ = refl

-- I think ignoring the 2-cells is ok, since the codomain of Forget is a 1-category?
-- But then are we getting into trouble with Free? Surely the free 2-cells would be
-- trivial...
CAT : ∀ ℓ → Category (lsuc ℓ)
CAT ℓ .Obj = Category ℓ
CAT ℓ .Hom = Functor
CAT ℓ .id = idFunctor
CAT ℓ .comp = compFunctor
CAT ℓ .assoc = {!!}
CAT ℓ .identityˡ = {!!}
CAT ℓ .identityʳ = {!!}

record PartialMonoid (ℓ : Level) : Set (lsuc ℓ) where
  constructor MkPMon
  field
    -- A carrier set
    Carrier : Set ℓ

    -- A partially defined monoid structure
    _~_ : Carrier → Carrier → Set
    op : (x y : Carrier) → x ~ y → Carrier
    ε : Carrier
    proof : IsPartialMonoid (_≡_ {A = Carrier}) _~_ op ε

    -- And a relation on the carrier which ignores that monoid structure
    R : Carrier → Carrier → Set
  open IsPartialMonoid public
open PartialMonoid

record PMonMorphism {ℓ} (A B : PartialMonoid ℓ) : Set ℓ where
  constructor MkPMonMorphism
  private
    module A = PartialMonoid A
    module B = PartialMonoid B
  field
    -- A function on the underlying sets...
    fun : Carrier A → Carrier B

    -- which preserves the monoid structure (and ignores the extra relation).
    preserves-ε : fun (A.ε) ≡ B.ε
    preserves-R : ∀ {x y} → x A.~ y → (fun x) B.~ (fun y)
    preserves-∙ : ∀ {x y} (p : x A.~ y) → fun (A.op x y p) ≡ B.op (fun x) (fun y) (preserves-R p)
open PMonMorphism

pmon-id : ∀ {ℓ} {A : PartialMonoid ℓ} → PMonMorphism A A
pmon-id .fun x = x
pmon-id .preserves-ε = refl
pmon-id .preserves-R x = x
pmon-id .preserves-∙ p = refl

pmon-comp : ∀ {ℓ} {A B C : PartialMonoid ℓ} → PMonMorphism A B → PMonMorphism B C → PMonMorphism A C
pmon-comp f g .fun x = g .fun (f .fun x)
pmon-comp f g .preserves-ε = {!!}
pmon-comp f g .preserves-R = {!!}
pmon-comp f g .preserves-∙ = {!!}

PMON : ∀ ℓ → Category ℓ
PMON ℓ .Obj = PartialMonoid ℓ
PMON ℓ .Hom = PMonMorphism
PMON ℓ .id = pmon-id
PMON ℓ .comp = pmon-comp
PMON ℓ .assoc = {!!}
PMON ℓ .identityˡ = {!!}
PMON ℓ .identityʳ = {!!}

-- Forget the category structure, and functoriality of functors.
Forget : ∀ ℓ → Functor (CAT ℓ) (GRAPH⁻ ℓ)
Forget ℓ .act C = (Obj C) , (Hom C)
Forget ℓ .fmap F = F .act
Forget ℓ .identity = refl
Forget ℓ .homomorphism = refl


-- The left-adjoint free functor is, in some sense, fresh lists?
Free : ∀ ℓ → Functor (GRAPH⁻ ℓ) (PMON (lsuc ℓ))
Free ℓ .act (X , R) = {!!}
Free ℓ .fmap = {!!}
Free ℓ .identity = {!!}
Free ℓ .homomorphism = {!!}

-- Idea:
--
-- PMON ≅ CAT
--
-- `FList R` may be the
