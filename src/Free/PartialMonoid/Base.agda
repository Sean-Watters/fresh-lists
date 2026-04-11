{-# OPTIONS --safe --cubical-compatible #-}
module Free.PartialMonoid.Base where

open import Level
open import Function.Partial as PFun
open import Data.FreshList.InductiveInductive

private variable
  ℓx ℓr : Level
  X : Set ℓx
  R : X → X → Set ℓr

-- To conctenate two fresh lists, everything in the first needs to be
-- fresh for everything in the second.
Gluable : List# R → List# R → Set _
Gluable xs ys = All (_# ys) xs

-- Partial concatenation for fresh lists on an arbitrary relation
mutual
  concat : PFun.Op₂ {X = List# R} Gluable
  concat [] ys [] = ys
  concat (cons x xs x#xs) ys (x#ys ∷ g) = cons x (concat xs ys g) (concat-fresh g x#xs x#ys)

  concat-fresh : {a : X} {xs ys : List# R}
               → (g : All (_# ys) xs)
               → (a#xs : a # xs)
               → a # ys
               → a # concat xs ys g
  concat-fresh [] a#xs a#ys = a#ys
  concat-fresh (x#ys ∷ g) (Rax ∷ a#xs) a#ys = Rax ∷ concat-fresh g a#xs a#ys

-- Conveient syntax for concatenation
∙[_] : {x y : List# R} → Gluable x y → List# R
∙[ xy ] = concat _ _ xy
