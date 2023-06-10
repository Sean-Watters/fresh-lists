{-# OPTIONS --safe --without-K #-}

open import Axiom.Extensionality.Propositional

open import Level
open import Algebra.Definitions
open import Algebra.Structures
open import Function
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Const


open import Data.FreshList.InductiveInductive
open import Category.Base




module Free.PointedSet.Adjunction where

open import Free.PointedSet.Base
open import Free.PointedSet.Properties

record PointedSet : Set₁ where
  constructor PSet
  field
    Carrier : Set
    ε : Carrier
    isSet : Irrelevant (_≡_ {A = Carrier})
open PointedSet

record PointedSetMorphism (A B : PointedSet) : Set where
  constructor PSetMorphism
  private
    module A = PointedSet A
    module B = PointedSet B
  field
    fun : Carrier A → Carrier B
    preserves-ε : fun (A.ε) ≡ B.ε
open PointedSetMorphism

eqPsetMorphism : ∀ {A B} → {f g : PointedSetMorphism A B} → fun f ≡ fun g → f ≡ g
eqPsetMorphism {A} {B} {PSetMorphism .f refl} {PSetMorphism f q} refl
  = cong (PSetMorphism f) (isSet B refl q)

pset-id : ∀ {A} → PointedSetMorphism A A
PointedSetMorphism.fun pset-id = Function.id
PointedSetMorphism.preserves-ε pset-id = refl

pset-comp : ∀ {A B C} → PointedSetMorphism A B → PointedSetMorphism B C → PointedSetMorphism A C
PointedSetMorphism.fun (pset-comp f g) = (fun g) ∘ (fun f)
PointedSetMorphism.preserves-ε (pset-comp f g) = trans (cong (fun g) (preserves-ε f)) (preserves-ε g)


PSET : Category
Category.Obj PSET = PointedSet
Category.Hom PSET = PointedSetMorphism
Category.id PSET = pset-id
Category.comp PSET = pset-comp
Category.assoc PSET = eqPsetMorphism refl
Category.identityˡ PSET = eqPsetMorphism refl
Category.identityʳ PSET = eqPsetMorphism refl

open Functor

-- forgetful functor
Forget : Functor PSET HSET
act Forget x = hset (Carrier x) (isSet x)
fmap Forget f x = (fun f) x
identity Forget = refl
homomorphism Forget = refl



-- free functor

Maybe' : hSet → PointedSet
Carrier (Maybe' X) = Maybe (hSet.Carrier X)
ε (Maybe' X) = []
isSet (Maybe' X) = MaybehSet (hSet.isSet X)


fmap-maybe : {X Y : hSet} → (hSet.Carrier X → hSet.Carrier Y) → PointedSetMorphism (Maybe' X) (Maybe' Y)
fun (fmap-maybe f) = map-maybe f
preserves-ε (fmap-maybe f) = refl

FreePSet : (ext : Extensionality _ _) → Functor HSET PSET
act (FreePSet ext) X = Maybe' X
fmap (FreePSet ext) = fmap-maybe
identity (FreePSet ext) = eqPsetMorphism (ext (λ { [] → refl ; (just x) → refl}))
homomorphism (FreePSet ext) = eqPsetMorphism (ext (λ { [] → refl ; (just x) → refl}))

-- adjunction

open Adjunction

PSetAdjunction : (ext : Extensionality _ _) → (FreePSet ext) ⊣ Forget
to (PSetAdjunction ext) f x = fun f (just x)
fun (from (PSetAdjunction ext) {B = B} f) [] = ε B
fun (from (PSetAdjunction ext) f) (just x) = f x
preserves-ε (from (PSetAdjunction ext) f) = refl
left-inverse-of (PSetAdjunction ext) h = eqPsetMorphism (ext  λ { [] → sym $ preserves-ε h ; (just x) → refl})
right-inverse-of (PSetAdjunction ext) k = refl
to-natural (PSetAdjunction ext) f g = refl
