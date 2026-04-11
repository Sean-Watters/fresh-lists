{-# OPTIONS --safe --cubical-compatible #-}
module Free.PartialMonoid.Properties where

open import Level
open import Data.FreshList.InductiveInductive
open import Free.PartialMonoid.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

private variable
  ℓx ℓr : Level
  X : Set ℓx
  R : X → X → Set ℓr

------------------------
-- Gluable and Concat --
------------------------

-- Gluable is propositional when R is too.
Gluable-prop : ({x y : X} → Irrelevant (R x y))
             → {xs ys : List# R} → Irrelevant (Gluable xs ys)
Gluable-prop R-prop [] [] = refl
Gluable-prop {R = R} R-prop (p ∷ ps) (q ∷ qs)
  = cong₂ _∷_ (#-irrelevant p q) (Gluable-prop R-prop ps qs)
  where open WithIrr R R-prop

-- Identity --

-- The empty list is always gluable
Gluable-[]ˡ : {xs : List# R} → Gluable [] xs
Gluable-[]ˡ = []

Gluable-[]ʳ : {xs : List# R} → Gluable xs []
Gluable-[]ʳ {xs = []} = []
Gluable-[]ʳ {xs = cons x xs x#xs} = [] ∷ Gluable-[]ʳ

concat-idˡ : {xs : List# R} {p : Gluable [] xs}
           → concat [] xs p ≡ xs
concat-idˡ = {!!}

concat-idʳ : {xs : List# R} {p : Gluable xs []}
           → concat xs [] p ≡ xs
concat-idʳ = {!!}


-- Splitting freshness and gluability proofs along a concatenation
-- (crucial for associativity)

#-splitˡ : {x : X} {y z : List# R} {yz : Gluable y z}
         → x # ∙[ yz ]
         → x # y
#-splitˡ {yz = []} x#yz = []
#-splitˡ {yz = y#zs ∷ yz} (Rxy ∷ x#yz) = Rxy ∷ (#-splitˡ x#yz)

#-splitʳ : {x : X} {y z : List# R} {yz : Gluable y z}
         → x # ∙[ yz ]
         → x # z
#-splitʳ {yz = []} x#yz = x#yz
#-splitʳ {yz = x ∷ yz} (_ ∷ x#yz) = #-splitʳ x#yz

Gluable-splitˡ : {x y z : List# R}
               → (yz : Gluable y z) → (x[yz] : Gluable x ∙[ yz ]) → Gluable x y
Gluable-splitˡ yz [] = []
Gluable-splitˡ yz (x₀#yz ∷ x[yz]) = #-splitˡ x₀#yz ∷ Gluable-splitˡ yz x[yz]

Gluable-splitʳ : {x y z : List# R}
               → (xy : Gluable x y) → ([xy]z : Gluable ∙[ xy ] z) → Gluable y z
Gluable-splitʳ [] [xy]z = [xy]z
Gluable-splitʳ (_ ∷ xy) (_ ∷ [xy]z) = Gluable-splitʳ xy [xy]z

-- After splitting a Gluable proof like above, we can reassociate.

Gluable-associateˡ : {x y z : List# R}
                   → (yz : Gluable y z)
                   → (x[yz] : Gluable x ∙[ yz ])
                   → (xy : Gluable x y)
                   → Gluable ∙[ xy ] z
Gluable-associateˡ yz x[yz] [] = yz
Gluable-associateˡ yz (x#yz ∷ x[yz]) (x#y ∷ xy) = (#-splitʳ x#yz) ∷ (Gluable-associateˡ yz x[yz] xy)

Gluable-associateʳ : {x y z : List# R}
                   → (xy : Gluable x y)
                   → ([xy]z : Gluable ∙[ xy ] z)
                   → (yz : Gluable y z)
                   → Gluable x ∙[ yz ]
Gluable-associateʳ [] [xy]z yz = []
Gluable-associateʳ {z = z} (x#y ∷ xy) (x#z ∷ [xy]z) [] = x#z ∷ subst (λ u → Gluable u z) concat-idʳ [xy]z
Gluable-associateʳ (x#y ∷ xy) (x#z ∷ [xy]z) (y#z ∷ yz) = {!!} ∷ {!!}

-- Finally, associativty of concatenation.
concat-assoc : {x y z : List# R}
              → (yz : Gluable y z)
              → (x[yz] : Gluable x ∙[ yz ])
              → (xy : Gluable x y)
              → ([xy]z : Gluable ∙[ xy ] z)
              → (∙[ x[yz] ] ≡ ∙[ [xy]z ])
concat-assoc = {!!}

-- Other properties of gluable
-- * transitivity
-- * joinˡ : xy → yz → [xy]z
-- * joinʳ : xy → yz → x[yz]

------------
-- Concat --
------------

