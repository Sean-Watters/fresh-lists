{-# OPTIONS --type-in-type --with-K #-}
open import Axiom.UniquenessOfIdentityProofs.WithK

open import Level
open import Algebra.Definitions
open import Algebra.Structures
open import Algebra.Structure.PointedSet
open import Algebra.Structure.PointedSet.WithK
open import Function
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Const


open import Data.FreshList.InductiveInductive
open import Category
open import Category.Adjunctions
open import Category.Instances.PointedSets


module Data.FreshList.FreePointedSet.Adjunction where

open PointedSet
open PointedSetMorphism
open Functor
open Adjunction

-- free functor
Maybe : Set → Set
Maybe X = List# {A = X} R⊥

pattern just x = cons x [] []

Maybe' : Set → PointedSet
Carrier (Maybe' X) = Maybe X
ε (Maybe' X) = []

map-maybe : {X Y : Set} → (X → Y) → PointedSetMorphism (Maybe' X) (Maybe' Y)
fun (map-maybe f) [] = []
fun (map-maybe f) (just x) = just (f x)
preserves-ε (map-maybe f) = refl

FreePSet : Functor SET PSET
act FreePSet X = Maybe' X
fmap FreePSet = map-maybe
identity FreePSet = eqPsetMorphism (ext (λ { [] → refl ; (just x) → refl}))
homomorphism FreePSet = eqPsetMorphism (ext (λ { [] → refl ; (just x) → refl}))

-- adjunction
PSetAdjunction : FreePSet ⊣ Forget
to PSetAdjunction f x = fun f (just x)
fun (from PSetAdjunction {B = B} f) [] = ε B
fun (from PSetAdjunction f) (just x) = f x
preserves-ε (from PSetAdjunction f) = refl
left-inverse-of PSetAdjunction h = eqPsetMorphism (ext  λ { [] → sym $ preserves-ε h ; (just x) → refl})
right-inverse-of PSetAdjunction k = refl
to-natural PSetAdjunction f g = refl
