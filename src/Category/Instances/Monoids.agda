{-# OPTIONS --type-in-type --with-K #-}

open import Axiom.Extensionality.Propositional
open import Category
open import Algebra.Structure.Monoid
open import Relation.Binary.PropositionalEquality

module Category.Instances.Monoids (funext : Extensionality _ _) where

open import Algebra.Structure.Monoid.WithFunExtAndK funext

open Functor
open Monoid
open MonoidMorphism

MON : Category
Category.Obj MON = Monoid
Category.Hom MON = MonoidMorphism
Category.id MON = mon-id
Category.comp MON = mon-comp
Category.assoc MON = eqMonMorphism refl
Category.identityˡ MON = eqMonMorphism refl
Category.identityʳ MON = eqMonMorphism refl

-- forgetful functor
Forget : Functor MON SET
act Forget X = Carrier X
fmap Forget f x = fun f x
identity Forget = refl
homomorphism Forget = refl
