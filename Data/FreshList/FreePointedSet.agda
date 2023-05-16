{-# OPTIONS --safe --without-K #-}
open import Algebra.Definitions
open import Algebra.Structures
open import Algebra.Structure.PointedSet
open import Function
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Const


open import Data.FreshList.InductiveInductive


module Data.FreshList.FreePointedSet where

open PointedSet
open PointedSetMorphism

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
