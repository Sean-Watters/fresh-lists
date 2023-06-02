{-# OPTIONS --safe --without-K #-}

open import Algebra.Structure.OICM

module Data.FreshList.FreeLeftRegularMonoid.Properties
  {X : Set} {_≈_ : X → X → Set} {_≠_ : X → X → Set}
  (≠-AR : IsPropDecApartnessRelation _≈_ _≠_)
  where

open import Data.Empty
open import Data.FreshList.InductiveInductive
-- open import Function
-- open import Relation.Binary.Isomorphism
open import Relation.Binary.PropositionalEquality renaming (isEquivalence to ≡-isEquivalence)
open import Relation.Nullary
open import Data.Sum
open import Data.Product
open import Algebra.Structures

open import Data.FreshList.FreeLeftRegularMonoid ≠-AR

private
  ≠-irrefl  = IsPropDecApartnessRelation.irrefl ≠-AR
  ≠-sym  = IsPropDecApartnessRelation.sym ≠-AR
  ≠-cotrans = IsPropDecApartnessRelation.cotrans ≠-AR
  ≠-prop = IsPropDecApartnessRelation.prop ≠-AR
  ≠-dec = IsPropDecApartnessRelation.dec ≠-AR
  ≈-refl = IsPropDecApartnessRelation.refl ≠-AR
  ≈-sym = IsPropDecApartnessRelation.≈-sym ≠-AR
  ≈-trans = IsPropDecApartnessRelation.trans ≠-AR

  ≠-cons-cong = WithIrr.cons-cong _≠_ ≠-prop

-[]-resp-≈ : (xs : UniqueList) → {y z : X} → y ≈ z → xs -[ y ] ≡ xs -[ z ]
-[]-resp-≈ [] y≈z = refl
-[]-resp-≈ (cons x xs x#xs) {y} {z} y≈z with ≠-dec x y |  ≠-dec x z
... | inj₁ x≈y | inj₁ x≈z = refl
... | inj₁ x≈y | inj₂ x≠z = ⊥-elim (≠-irrefl (≈-trans x≈y y≈z) x≠z)
... | inj₂ x≠y | inj₁ x≈z = ⊥-elim (≠-irrefl (≈-trans x≈z (≈-sym y≈z)) x≠y)
... | inj₂ x≠y | inj₂ x≠z = ≠-cons-cong refl (-[]-resp-≈ xs y≈z)

-[]-order-irrelevant : (xs : UniqueList) → (y z : X) → xs -[ y ] -[ z ] ≡ xs -[ z ] -[ y ]
-[]-order-irrelevant [] y z = refl
-[]-order-irrelevant (cons x xs x#xs) y z with ≠-dec x y in eqxy |  ≠-dec x z in eqxz
... | inj₁ x≈y | inj₁ x≈z = -[]-resp-≈ xs ((≈-trans (≈-sym x≈z) x≈y))
... | inj₁ x≈y | inj₂ x≠z rewrite eqxy = refl
... | inj₂ x≠y | inj₁ x≈z rewrite eqxz = refl
... | inj₂ x≠y | inj₂ x≠z rewrite eqxz rewrite eqxy = ≠-cons-cong refl (-[]-order-irrelevant xs y z)

remove-union : (xs ys : UniqueList) → (z : X) → union xs ys -[ z ] ≡ union (xs -[ z ]) (ys -[ z ])
remove-union [] ys z = refl
remove-union (cons x xs x#xs) ys z with ≠-dec x z
... | inj₁ x≈z = trans (remove-union xs ys x) (cong₂ union (remove-fresh-idempotent xs x x#xs) (-[]-resp-≈ ys x≈z))
... | inj₂ x≠z = ≠-cons-cong refl (trans (-[]-order-irrelevant (union xs ys) x z) (cong (_-[ x ]) (remove-union xs ys z)))

remove-union-fresh : (xs ys : UniqueList) → (x : X) → x # xs → union xs ys -[ x ] ≡ union xs (ys -[ x ])
remove-union-fresh xs ys x x#xs = trans (remove-union xs ys x) (cong (λ w → union w (ys -[ x ])) (remove-fresh-idempotent xs x x#xs))

remove-cons : (xs : UniqueList) → (x : X) → (x#xs : x # xs) → (y : X) → x ≈ y → cons x xs x#xs -[ y ] ≡ xs
remove-cons xs x x#xs y x≈y with ≠-dec x y
... | inj₁ x≈y = refl
... | inj₂ x≠y = ⊥-elim (≠-irrefl x≈y x≠y)

unitʳ : (xs : UniqueList) → union xs [] ≡ xs
unitʳ [] = refl
unitʳ (cons x xs x#xs) = ≠-cons-cong refl (trans (cong (_-[ x ]) (unitʳ xs)) (remove-fresh-idempotent xs x x#xs))

unitˡ : (xs : UniqueList) → union [] xs ≡ xs
unitˡ xs = refl

assoc : (xs ys zs : UniqueList) → union (union xs ys) zs ≡ union xs (union ys zs)
assoc [] ys zs = refl
assoc (cons x xs x#xs) ys zs = ≠-cons-cong refl (trans (lemma ys) (cong (_-[ x ]) (assoc xs ys zs))) where
  lemma : ∀ ys → (union (union xs ys -[ x ]) zs -[ x ]) ≡ (union (union xs ys) zs -[ x ])
  lemma [] = cong (λ w → union w zs -[ x ]) (trans (trans (cong (_-[ x ]) (unitʳ xs)) (remove-fresh-idempotent xs x x#xs)) (sym (unitʳ xs)))
  lemma (cons y ys y#ys) = begin
    union (union xs (cons y ys y#ys) -[ x ]) zs -[ x ]
      ≡⟨ remove-union (union xs (cons y ys y#ys) -[ x ]) zs x ⟩
    union (union xs (cons y ys y#ys) -[ x ] -[ x ]) (zs -[ x ])
      ≡⟨ cong (λ w → union w (zs -[ x ])) (remove-fresh-idempotent _ x (remove-removes (union xs (cons y ys y#ys)) x)) ⟩
    union (union xs (cons y ys y#ys) -[ x ]) (zs -[ x ])
      ≡⟨ sym (remove-union (union xs (cons y ys y#ys)) zs x) ⟩
    union (union xs (cons y ys y#ys)) zs -[ x ]
    ∎ where open ≡-Reasoning

idem : (xs : UniqueList) → union xs xs ≡ xs
idem [] = refl
idem (cons x xs x#xs) = ≠-cons-cong refl (trans lemma (idem xs))
  where
    lemma : (union xs (cons x xs x#xs) -[ x ]) ≡ union xs xs
    lemma = begin
      union xs (cons x xs x#xs) -[ x ]
        ≡⟨ remove-union xs (cons x xs x#xs) x ⟩
      union (xs -[ x ]) (cons x xs x#xs -[ x ])
        ≡⟨ cong₂ union (remove-fresh-idempotent xs x x#xs) (remove-cons xs x x#xs x ≈-refl) ⟩
      union xs xs ∎ where open ≡-Reasoning

leftregular : (xs ys : UniqueList) → union (union xs ys) xs ≡ union xs ys
leftregular [] ys = unitʳ ys
leftregular (cons x xs x#xs) ys = ≠-cons-cong refl (begin
  union (union xs ys -[ x ]) (cons x xs x#xs) -[ x ]
    ≡⟨ cong (λ w → union w (cons x xs x#xs) -[ x ]) (remove-union xs ys x) ⟩
  union (union (xs -[ x ]) (ys -[ x ])) (cons x xs x#xs) -[ x ]
    ≡⟨ remove-union (union (xs -[ x ]) (ys -[ x ])) (cons x xs x#xs) x ⟩
  union (union (xs -[ x ]) (ys -[ x ]) -[ x ]) ((cons x xs x#xs) -[ x ])
    ≡⟨ cong₂ union (trans (remove-union (xs -[ x ]) (ys -[ x ]) x)
                          (cong₂ union (trans (remove-fresh-idempotent (xs -[ x ]) x (remove-removes xs x)) (remove-fresh-idempotent xs x x#xs))
                                       (remove-fresh-idempotent (ys -[ x ]) x (remove-removes ys x))))
                   (remove-cons xs x x#xs x ≈-refl) ⟩
  union (union xs (ys -[ x ])) xs
    ≡⟨ leftregular xs (ys -[ x ]) ⟩
  union xs (ys -[ x ])
    ≡⟨ cong (λ w → union w (ys -[ x ])) (sym (remove-fresh-idempotent xs x x#xs)) ⟩
  union (xs -[ x ]) (ys -[ x ])
    ≡⟨ sym (remove-union xs ys x) ⟩
  union xs ys -[ x ]
    ∎) where open ≡-Reasoning

{-

peel-∈-iso-fun' : {b : X} {xs ys : UniqueList} {b#xs : b # xs} {b#ys : b # ys}
               → (iso : ∀ a → (a ∈ cons b xs b#xs) ≃ (a ∈ cons b ys b#ys))
               → (a : X)
               → (p : a ∈ xs)
               → (to-there : a ∈ cons b ys b#ys)
               → to-there ≡ to (iso a) (there p)
               → a ∈ ys
peel-∈-iso-fun' {b} iso a p (here a≈b) eq with to (iso a) (here a≈b) in eq'
... | here a≈b' = ⊥-elim (here≢there ( sym $ to-inj (iso a) (trans (sym eq) (trans (cong here (≈-prop a≈b a≈b') ) (sym eq')))))
... | there u = u
peel-∈-iso-fun' {b} iso a p (there a∈ys) eq = a∈ys

peel-∈-iso-fun : {b : X} {xs ys : SortedList} {b#xs : b # xs} {b#ys : b # ys}
               → (∀ a → (a ∈ cons b xs b#xs) ≃ (a ∈ cons b ys b#ys))
               → (∀ a → a ∈ xs → a ∈ ys)
peel-∈-iso-fun iso a p = peel-∈-iso-fun' iso a p (to (iso a) (there p)) refl

there-inj : {a x : X} {xs : SortedList} {x#xs : x # xs} {p q : a ∈ xs} → there {x = x} {xs} {x#xs} p ≡ there q → p ≡ q
there-inj refl = refl

from-to-peel' : {b : X} {xs ys : SortedList} {b#xs : b # xs} {b#ys : b # ys}
              → (iso : ∀ a → (a ∈ cons b xs b#xs) ≃ (a ∈ cons b ys b#ys))
              → (a : X)
              → (p : a ∈ xs)
              → (to-there : a ∈ cons b ys b#ys)
              → (eq : to-there ≡ to (iso a) (there p))
              → (from-there : a ∈ cons b xs b#xs)
              → (eq' : from-there ≡ to (≃-sym (iso a)) (there (peel-∈-iso-fun' iso a p to-there eq)))
              → p ≡ peel-∈-iso-fun' (λ x → ≃-sym (iso x)) a (peel-∈-iso-fun' iso a p to-there eq) from-there eq'
from-to-peel' iso a p (here a≈b) eq from-there eq' =  ⊥-elim (here≢there (sym (to-inj (iso a) (trans (sym eq) {!!}))))
from-to-peel' iso a p (there a∈ys) eq .(to (≃-sym (iso a)) (there (peel-∈-iso-fun' iso a p (there a∈ys) eq))) refl
  = subst (λ z → ∀ q → p ≡ peel-∈-iso-fun' (λ x → ≃-sym (iso x)) a a∈ys (from (iso a) z) q)
          (sym eq)
          (λ q → subst (λ z → ∀ q' → p ≡ peel-∈-iso-fun' (λ x → ≃-sym (iso x)) a a∈ys z q')
                       (from-to (iso a) (there p))
                       (λ _ → refl)
                       q)
          refl
-}
