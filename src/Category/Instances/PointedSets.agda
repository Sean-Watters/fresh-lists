{-# OPTIONS --type-in-type --with-K #-}

open import Category
open import Algebra.Structure.PointedSet
open import Algebra.Structure.PointedSet.WithK
open import Relation.Binary.PropositionalEquality

module Category.Instances.PointedSets where

open Functor
open PointedSet
open PointedSetMorphism

PSET : Category
Category.Obj PSET = PointedSet
Category.Hom PSET = PointedSetMorphism
Category.id PSET = pset-id
Category.comp PSET = pset-comp
Category.assoc PSET = eqPsetMorphism refl
Category.identityˡ PSET = eqPsetMorphism refl
Category.identityʳ PSET = eqPsetMorphism refl

-- forgetful functor
Forget : Functor PSET SET
act Forget x = Carrier x
fmap Forget f x = (fun f) x
identity Forget = refl
homomorphism Forget = refl
