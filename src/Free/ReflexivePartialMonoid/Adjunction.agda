{-# OPTIONS --safe --without-K #-}

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
open import Data.Product

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

module _ (A B  : ReflexivePartialMonoid) where
  private
    module A = ReflexivePartialMonoid A
    module B = ReflexivePartialMonoid B


  cong-RPMonMorphism : (f : Carrier A → Carrier B) (p : f (A.ε) ≡ B.ε)
                    → {q q' : ∀ x y → x A.R y → (f x) B.R (f y)}
                    → {r  : ∀ {x y} (p : x A.R y) → f A.∙[ p ] ≡ B.∙[ q x y p ]}
                    → {r' : ∀ {x y} (p : x A.R y) → f A.∙[ p ] ≡ B.∙[ q' x y p ]}
                    → (qq : q ≡ q')
                    → (λ {x} {y} → r {x} {y}) ≡ subst (λ (z : ∀ x y → x A.R y → (f x) B.R (f y )) → {x y : A.Carrier} (p₁ : x A.R y) → f A.∙[ p₁ ] ≡ B.∙[ z x y p₁ ]) (sym qq) r'
                    → (RPMonMorphism A B ∋ MkRPMonMorphism f p (q _ _) r) ≡ MkRPMonMorphism f p (q' _ _) r'
  cong-RPMonMorphism f p {q} {.q} refl refl = refl


eqRPMonMorphism : Extensionality _ _
                → ∀ {A B} {f g : RPMonMorphism A B} → fun f ≡ fun g → f ≡ g
eqRPMonMorphism ext {A} {B} {MkRPMonMorphism f p q r} {MkRPMonMorphism .f p' q' r'} refl =
  begin
    MkRPMonMorphism f p q r
  ≡⟨ cong (λ z → MkRPMonMorphism f z q r) (A-set (isPMon $ proof B) p p')  ⟩
    MkRPMonMorphism f p' q r
  ≡⟨ cong-RPMonMorphism A B f p' (funprop ext (R-prop $ isPMon $ proof B) (λ x y z → q z) λ x y z → q' z) lem ⟩
    MkRPMonMorphism f p' q' r'
  ∎ where
    open ≡-Reasoning
    funprop : Extensionality _ _
            → ∀ {X : Set} {Y : X → X → Set} {Z : X → X → Set} → Irrelevant Z → (f g : (x y : X) → Y x y → Z x y) → f ≡ g
    funprop ext propZ f g = ext λ x → ext (λ y → ext (λ Yxy → propZ (f x y Yxy) (g x y Yxy)))

    lem : (λ {x} {y} → r {x} {y}) ≡ subst (λ z → {x y : Carrier A} (p₁ : (A R x) y) → f (∙[ A ] p₁) ≡ ∙[ B ] (z x y p₁))
                    (sym (funprop ext (R-prop (isPMon (proof B))) (λ x y z → q z) (λ x y z → q' z)))
                    r'
    lem = implicit-extensionality ext (implicit-extensionality ext (ext (λ x₁ → A-set (isPMon (proof B)) (r x₁) _)))


RPMON : Extensionality _ _ → Category
Category.Obj (RPMON ext) = ReflexivePartialMonoid
Category.Hom (RPMON ext) = RPMonMorphism
Category.id (RPMON ext) = rpmon-id
Category.comp (RPMON ext) = rpmon-comp
Category.assoc (RPMON ext) = eqRPMonMorphism ext (ext (λ x → refl))
Category.identityˡ (RPMON ext) = eqRPMonMorphism ext (ext (λ x → refl))
Category.identityʳ (RPMON ext) = eqRPMonMorphism ext (ext (λ x → refl))

---------------------------
-- The Forgetful Functor --
---------------------------

