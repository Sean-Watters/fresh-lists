
module Data.FreshList.Merge where

open import Relation.Nullary
open import Relation.Binary renaming (Decidable to Decidable₂)

open import Data.FreshList.InductiveInductive



module _ {X : Set} {R : X → X → Set} where
  mutual
    merge : Decidable₂ R → List# R → List# R → List# R
    merge _R?_ [] ys = ys
    merge _R?_ (cons x xs x#xs) [] = cons x xs x#xs
    merge _R?_ (cons x xs x#xs) (cons y ys y#ys) with x R? y
    ... | yes xRy = cons x (merge _R?_ xs (cons y ys y#ys)) {!!}
    ... | no ¬xRy = {!gen!}
