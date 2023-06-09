{-# OPTIONS --with-K #-}

-- postulate funext
open import Axiom.FunExt.Postulate

open import Algebra.Structures
open import Algebra.Structure.Monoid
open import Category
open import Category.Adjunctions
open import Data.FreshList.InductiveInductive
open import Data.FreshList.FreeMonoid
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Const

module Data.FreshList.FreeMonoid.Adjunction where

open import Algebra.Structure.Monoid.WithFunExtAndK funext
open import Category.Instances.Monoids funext

open Functor
open Adjunction
open Monoid
open MonoidMorphism

FreeMonoid : Functor SET MON
act FreeMonoid = List'
fmap FreeMonoid = map-list
identity FreeMonoid {X} = eqMonMorphism (ext lem) where
  lem : (xs : List X) → fun (map-list id) xs ≡ xs
  lem [] = refl
  lem (cons x xs x#xs) = trans (cong (λ z → cons x z tt#) (lem xs)) (cong (cons x xs) (WithIrr.#-irrelevant R⊤ (λ {tt tt → refl}) tt# x#xs))
homomorphism FreeMonoid {X} {Y} {Z} {f} {g} = eqMonMorphism (ext lem) where
  lem : (xs : List X) → fun (map-list (λ x → g (f x))) xs ≡ fun (map-list g) (fun (map-list f) xs)
  lem [] = refl
  lem (cons x xs x#xs) = cong (λ z → cons (g (f x)) z tt#) (lem xs)

MonoidAdjunction : FreeMonoid ⊣ Forget
to MonoidAdjunction f x = fun f (cons x [] [])
fun (from MonoidAdjunction {A} {B} f) = fold-∙ B f
preserves-ε (from MonoidAdjunction f) = refl
preserves-∙ (from MonoidAdjunction {A} {B} f) = fold-∙-preserves-∙ B f
left-inverse-of MonoidAdjunction {A} {B} h = eqMonMorphism (ext λ xs → foldr-universal (fun h) (λ a → _∙_ B (fun h (a ∷# []))) (ε B) (preserves-ε h) (λ a as a#as → trans (cong (fun h) (WithIrr.cons-cong R⊤ (λ p q → refl) refl refl)) (preserves-∙ h (a ∷# []) as)) xs)
right-inverse-of MonoidAdjunction {A} {B} k = ext (λ x → proj₂ (IsMonoid.identity $ proof B) (k x))
to-natural MonoidAdjunction f g = refl
