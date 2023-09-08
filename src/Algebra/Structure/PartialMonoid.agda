{-# OPTIONS --safe --without-K #-}
module Algebra.Structure.PartialMonoid where

open import Level
open import Algebra.Core
open import Data.Product hiding (assocˡ; assocʳ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (subst; dcong₂; _≡_)

record IsPartialMonoid
  {a b c} {A : Set a}
  (_≈_ : Rel A b) (_R_ : Rel A c)
  (∙ : (x y : A) → x R y → A)
  (ε : A)
  : Set (a ⊔ b ⊔ c) where

  private
    ∙[_] : {x y : A} → x R y → A
    ∙[_] {x} {y} xy = ∙ x y xy

  field
    isEquivalence : IsEquivalence _≈_
    A-set : Irrelevant (_≡_ {A = A})
    R-prop : Irrelevant _R_
    ε-compatˡ : ∀ {x} → ε R x
    ε-compatʳ : ∀ {x} → x R ε
    identityˡ : ∀ {x} → ∙[ ε-compatˡ {x} ] ≈ x
    identityʳ : ∀ {x} → ∙[ ε-compatʳ {x} ] ≈ x
    assocˡ : ∀ {x y z} → (yz : y R z) → (p : x R (∙[ yz ])) → Σ[ xy ∈ x R y ] Σ[ q ∈ ∙[ xy ] R z ] (∙[ p ] ≈ ∙[ q ])
    assocʳ : ∀ {x y z} → (xy : x R y) → (p : ∙[ xy ] R z) → Σ[ yz ∈ y R z ] Σ[ q ∈ x R ∙[ yz ] ] (∙[ p ] ≈ ∙[ q ])

  assocL1 : ∀ {x y z} → (yz : y R z) → (p : x R (∙[ yz ])) → Σ[ xy ∈ x R y ] (∙[ xy ] R z)
  assocL1 yz p = let (a , b , _) = assocˡ yz p in a , b

  assocR1 : ∀ {x y z} → (xy : x R y) → (p : ∙[ xy ] R z) → Σ[ yz ∈ y R z ] (x R ∙[ yz ])
  assocR1 yz p = let (a , b , _) = assocʳ yz p in a , b

  identityˡ' : ∀ {x} (r : ε R x) → ∙[ r ] ≈ x
  identityˡ' {x} r = subst (λ z → ∙[ z ] ≈ x) (R-prop ε-compatˡ r) identityˡ

  identityʳ' : ∀ {x} (r : x R ε) → ∙[ r ] ≈ x
  identityʳ' {x} r = subst (λ z → ∙[ z ] ≈ x) (R-prop ε-compatʳ r) identityʳ

  assocˡ₁ : ∀ {x y z} → (yz : y R z) → (p : x R (∙[ yz ])) → x R y
  assocˡ₁ yz p = let (a , b , _) = assocˡ yz p in a

  assocˡ₃ : ∀ {x y z} → (yz : y R z) → (p : x R (∙[ yz ])) → (xy : x R y) → (q : ∙[ xy ] R z ) → (∙ x (∙ y z yz) p ≈ ∙ (∙ x y xy) z q)
  assocˡ₃ {x} {y} {z} yx p xy q = subst (λ w → ∙ x (∙ y z yx) p ≈ ∙ (∙ x y (proj₁ w)) z (proj₂ w)) goal (proj₂ (proj₂ (assocˡ yx p)))
    where
      goal : (proj₁ (assocˡ yx p) , proj₁ (proj₂ (assocˡ yx p))) ≡ (xy , q)
      goal = dcong₂ _,_ (R-prop _ xy) (R-prop _ q)

  assocʳ₃ : ∀ {x y z} → (xy : x R y) → (p : ∙[ xy ] R z) → (yz : y R z) (q : x R ∙[ yz ]) → (∙[ p ] ≈ ∙[ q ])
  assocʳ₃ {x} {y} {z} yx p xy q = subst (λ w → ∙ (∙ x y yx) z p ≈ ∙ x (∙ y z (proj₁ w)) (proj₂ w)) goal (proj₂ (proj₂ (assocʳ yx p)))
    where
      goal : (proj₁ (assocʳ yx p) , proj₁ (proj₂ (assocʳ yx p))) ≡ (xy , q)
      goal = dcong₂ _,_ (R-prop _ xy) (R-prop _ q)


record IsReflexivePartialMonoid
  {a b c} {A : Set a}
  (_≈_ : Rel A b) (_R_ : Rel A c)
  (∙ : (x y : A) → x R y → A)
  (ε : A)
  : Set (a ⊔ b ⊔ c) where
  field
    isPMon : IsPartialMonoid _≈_ _R_ ∙ ε
    reflexive : ∀ {x} → x R x
  open IsPartialMonoid isPMon public
