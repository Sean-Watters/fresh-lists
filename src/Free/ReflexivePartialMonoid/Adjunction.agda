{-# OPTIONS --allow-unsolved-metas --without-K #-}

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Free.ReflexivePartialMonoid.Adjunction where


open import Algebra.Structure.PartialMonoid
open import Data.FreshList.InductiveInductive
open import Free.ReflexivePartialMonoid.Base
open import Free.ReflexivePartialMonoid.Properties
open import Category.Base

open import Axiom.Extensionality.Propositional
open import Function
open import Relation.Nullary using () renaming (Irrelevant to Irrelevant₀)

-----------------------------------------------
-- The Category of Reflexive Partial Monoids --
-----------------------------------------------

-- thought for later if stuck, should we enforce that C is a set and
-- R is prop valued?
record ReflexivePartialMonoid : Set₁ where
  constructor MkRPMon
  field
    Carrier : Set
    _≈_ : Carrier → Carrier → Set
    _R_ : Carrier → Carrier → Set
    ∙[_] : {x y : Carrier} → x R y → Carrier
    ε : Carrier
    proof : IsReflexivePartialMonoid _≈_ _R_ ∙[_] ε
  open IsReflexivePartialMonoid public
open ReflexivePartialMonoid

record RPMonMorphism (A B : ReflexivePartialMonoid) : Set where
  constructor MkRPMonMorphism
  private
    module A = ReflexivePartialMonoid A
    module B = ReflexivePartialMonoid B
  field
    fun : Carrier A → Carrier B
    preserves-ε : fun (A.ε) ≡ B.ε
    preserves-R : ∀ {x y} → x A.R y → (fun x) B.R (fun y)
    preserves-∙ : ∀ {x y} (p : x A.R y) → fun A.∙[ p ] ≡ B.∙[ preserves-R p ]
open RPMonMorphism

rpmon-id : ∀ {A} → RPMonMorphism A A
fun rpmon-id = id
preserves-ε rpmon-id = refl
preserves-R rpmon-id = id
preserves-∙ rpmon-id _ = refl

rpmon-comp : ∀ {A B C} → RPMonMorphism A B → RPMonMorphism B C → RPMonMorphism A C
fun (rpmon-comp f g) = fun g ∘ fun f
preserves-ε (rpmon-comp f g) = trans (cong (fun g) (preserves-ε f)) (preserves-ε g)
preserves-R (rpmon-comp f g) = preserves-R g ∘ preserves-R f
preserves-∙ (rpmon-comp f g) p = trans (cong (fun g) (preserves-∙ f p)) (preserves-∙ g (preserves-R f p))

eqPropFun : Extensionality _ _
          → {A : Set} {B : A → Set} → (∀ x → Irrelevant₀ (B x)) → Irrelevant₀ ((x : A) → B x)
eqPropFun ext p f g = ext (λ x → p x (f x) (g x))

eqRPMonMorphism : Extensionality _ _
                → ∀ {A B} {f g : RPMonMorphism A B} → fun f ≡ fun g → f ≡ g
eqRPMonMorphism ext {A} {B} {MkRPMonMorphism f p q r} {MkRPMonMorphism .f p' q' r'} refl
  = trans (cong (λ z → MkRPMonMorphism f z q r) {!proof B!} ) {!!}
--  = {!IsPartialMonoid.R-prop (isPMon $ proof B)!}
