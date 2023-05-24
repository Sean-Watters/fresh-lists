{-# OPTIONS --type-in-type #-}
module Category where

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Axiom.Extensionality.Propositional
open import Axiom.UniquenessOfIdentityProofs.WithK
open import Function as Fun using (_∘′_)
open import Data.Product hiding (map)

----------------------------
-- Function extensionality
----------------------------

postulate
  ext : Extensionality _ _

----------------------------
-- Categories
----------------------------

record Category : Set where
  eta-equality

  field
    Obj : Set
    Hom : Obj -> Obj -> Set

  field
    id  : ∀ {A} → Hom A A
    comp : ∀ {A B C} → Hom A B → Hom B C → Hom A C

  field -- laws
    assoc     : ∀ {A B C D} {f : Hom A B} {g : Hom B C}{h : Hom C D} →
                comp f (comp g h) ≡ (comp (comp f g) h)
    identityˡ : ∀ {A B} {f : Hom A B} → comp id f ≡ f
    identityʳ : ∀ {A B} {f : Hom A B} → comp f id ≡ f
open Category

----------------------------
-- Functors
----------------------------

record Functor (C D : Category) : Set where
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


-- How to prove Functors equal
eqFunctor : {C D : Category}{F G : Functor C D} ->
            (p : act F ≡ act G) ->
            (∀ {A B} → subst (λ z → Hom C A B -> Hom D (z A) (z B)) p (fmap F) ≡ (fmap G {A} {B})) ->
            F ≡ G
eqFunctor {G = G} refl q with iext (λ {A} → iext (λ {B} → q {A} {B}))
  where   iext = implicit-extensionality ext
... | refl = eqFunctor' {G = G} (implicit-extensionality ext λ {A} → uip _ _) (iext (iext (iext (iext (iext (uip _ _)))))) where
  iext = implicit-extensionality ext
  eqFunctor' : ∀ {C} {D} {G : Functor C D}
               {identity' identity'' : {A : Obj C} → fmap G {A} (Category.id C) ≡ Category.id D}
               {homomorphism' homomorphism'' : {X Y Z : Obj C} {f : Hom C X Y} {g : Hom C Y Z} → fmap G (comp C f g) ≡ comp D (fmap G f) (fmap G g)} →
               (_≡_ {A = ∀ {A} → fmap G {A} (Category.id C) ≡ Category.id D} identity' identity'') ->
               (_≡_ {A = {X Y Z : Obj C} {f : Hom C X Y} {g : Hom C Y Z} → fmap G (comp C f g) ≡ comp D (fmap G f) (fmap G g)} homomorphism' homomorphism'') ->
             _≡_ {A = Functor C D} (record { act = act G; fmap = fmap G; identity = identity'; homomorphism = homomorphism' })
                                   (record { act = act G; fmap = fmap G; identity = identity''; homomorphism = homomorphism'' })
  eqFunctor' refl refl = refl

idFunctor : {C : Category} -> Functor C C
act idFunctor X = X
fmap idFunctor f = f
identity idFunctor = refl
homomorphism idFunctor = refl

compFunctor : {A B C : Category} -> Functor A B → Functor B C → Functor A C
act (compFunctor F G) =  (act G) ∘′ (act F)
fmap (compFunctor F G) f = fmap G (fmap F f)
identity (compFunctor F G) = trans (cong (fmap G) (identity F)) (identity G)
homomorphism (compFunctor F G) = trans (cong (fmap G) (homomorphism F)) (homomorphism G)

Full : {A B : Category} → Functor A B → Set
Full {A} {B} S = ∀ {x y} {g : Category.Hom B (act S x) (act S y)} → Σ[ f ∈ Category.Hom A x y ] g ≡ (fmap S f)

Faithful : {A B : Category} → Functor A B → Set
Faithful {A} {B} S = ∀ {x y} {f g : Category.Hom A x y} → fmap S f ≡ fmap S g → f ≡ g

FullyFaithful : {A B : Category} → Functor A B → Set
FullyFaithful S = Full S × Faithful S

----------------------------
-- Natural transformations
----------------------------

record NaturalTransformation {C D : Category}
                             (F G : Functor C D) : Set where
  eta-equality
  private
    module F = Functor F
    module G = Functor G
    module C = Category C
    module D = Category D

  field
    transform   : ∀ X → D.Hom (F.act X) (G.act X)
    natural     : ∀ X Y (f : C.Hom X Y) →
                  D.comp (F.fmap f) (transform Y) ≡ D.comp (transform X) (G.fmap f)
open NaturalTransformation

-- How to prove natural transformations equal
eqNatTrans : {C D : Category}{F G : Functor C D} ->
             (η ρ : NaturalTransformation F G) ->
             ((X : Category.Obj C) -> transform η X ≡ transform ρ X) ->
             η ≡ ρ
eqNatTrans {C} η ρ p with ext p
... | refl = eqNatTrans' η ρ refl (ext λ X → ext λ Y → ext λ f → uip _ _) where
  eqNatTrans' : {C D : Category}{F G : Functor C D} ->
                (η ρ : NaturalTransformation F G) ->
                (p : transform η ≡ transform ρ) ->
                subst (λ z → (X Y : Category.Obj C)(f : Category.Hom C X Y) → Category.comp D (fmap F f) (z Y) ≡ Category.comp D (z X) (fmap G f)) p (natural η) ≡ (natural ρ) ->
               η ≡ ρ
  eqNatTrans' η ρ refl refl = refl

----------------------------
-- The category of Sets
----------------------------

SET : Category
Category.Obj SET = Set
Category.Hom SET A B = A -> B
Category.id SET = Fun.id
Category.comp SET f g = g Fun.∘′ f
Category.assoc SET = refl
Category.identityˡ SET = refl
Category.identityʳ SET = refl


----------------------------
-- Monads
----------------------------

record Monad (C : Category) : Set where
  open Category C
  open Functor

  field
    functor : Functor C C

  private
    M = functor

  field
    returnNT : NaturalTransformation idFunctor M
    joinNT   : NaturalTransformation (compFunctor M M) M

  return = NaturalTransformation.transform returnNT
  join   = NaturalTransformation.transform joinNT

  field
    returnJoin : {X : Obj C}    -> comp C (return (act M X)) (join X) ≡ id C
    mapReturnJoin : {X : Obj C} -> comp C (fmap M (return X)) (join X)  ≡ id C
    joinJoin : {X : Obj C}      -> comp C (join (act M X)) (join X) ≡ comp C (fmap M (join X)) (join X)

  open Functor M


---------------------------
-- Equivalence of Cats
---------------------------

record _≅_ (C D : Category) : Set where
  constructor MkCatIso
  field
    S : Functor C D
    T : Functor D C
    idL : compFunctor S T ≡ idFunctor
    idR : compFunctor T S ≡ idFunctor
open _≅_

-----------------
-- Anafunctors --
-----------------

record Anafunctor (C D : Category) : Set where
  constructor MkAnafunctor
  field
    SpecF : Set    -- Set of specifications of F
    σ : SpecF → Obj C  -- An object of C for each spec
    τ : SpecF → Obj D  -- An object of D for each spec

  -- What it means for y to be the specified object of F at x.
  specified : (x : Obj C) (y : Obj D) → Set
  specified x y = Σ[ s ∈ SpecF ] (x ≡ σ s) × (y ≡ τ s) -- s "specifies" y at x

  field
    map : (s t : SpecF) → Hom C (σ s) (σ t) → Hom D (τ s) (τ t)
