{-# OPTIONS --safe --without-K #-}

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Free.ReflexivePartialMonoid.Adjunction where


open import Algebra.Structure.PartialMonoid
open import Data.FreshList.InductiveInductive
open import Free.ReflexivePartialMonoid.Base
open import Free.ReflexivePartialMonoid.Properties
open import Category.Base

open import Axiom.UniquenessOfIdentityProofs
open import Axiom.Extensionality.Propositional
open import Function
open import Relation.Nullary using () renaming (Irrelevant to Irrelevant₀)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Nat

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

--------------------------
-- The Category of Sets --
--------------------------

-- The category of sets. Note due to UIP this really is Set, not just
-- the category of Agda "Sets"

SetObj : Set₁
SetObj = Σ[ X ∈ Set ] UIP X

SetFun : SetObj → SetObj → Set
SetFun X Y = proj₁ X → proj₁ Y

SET : Extensionality _ _ → Category
Category.Obj (SET ext) = SetObj
Category.Hom (SET ext) = SetFun
Category.id (SET ext) = id
Category.comp (SET ext) f g = g ∘ f
Category.assoc (SET ext) = ext (λ x → refl)
Category.identityˡ (SET ext) = ext (λ x → refl)
Category.identityʳ (SET ext) = ext (λ x → refl)

---------------------------
-- The Forgetful Functor --
---------------------------

FORGET : (ext : Extensionality _ _) → Functor (RPMON ext) (SET ext)
Functor.act (FORGET ext) (MkRPMon X _ _ _ _ proof) = X , (A-set $ isPMon proof)
Functor.fmap (FORGET ext) (MkRPMonMorphism f _ _ _) x = f x
Functor.identity (FORGET ext) = ext (λ _ → refl)
Functor.homomorphism (FORGET ext) = ext (λ _ → refl)


----------------------
-- The Free Functor --
----------------------


FreeRPMon'-map : (X Y : SetObj) → SetFun X Y → (FreeRPMon' (proj₁ X) (proj₂ X)) → (FreeRPMon' (proj₁ Y) (proj₂ Y))
FreeRPMon'-map X Y f (inj₁ tt) = inj₁ tt
FreeRPMon'-map X Y f (inj₂ (x , n)) = inj₂ (f x , n)

FreeRPMon-map : (X Y : SetObj) → SetFun X Y → (FreeRPMon (proj₁ X) (proj₂ X)) → (FreeRPMon (proj₁ Y) (proj₂ Y))
FreeRPMon-map X Y f xs = from-alt (proj₁ Y) (proj₂ Y) (FreeRPMon'-map X Y f (to-alt (proj₁ X) (proj₂ X) xs))

map-preserves-R : (X Y : SetObj) (f : SetFun X Y)
                → {x y : FreeRPMon (proj₁ X) (proj₂ X)}
                → (proj₁ X ~ proj₂ X) x y
                → (proj₁ Y ~ proj₂ Y) (FreeRPMon-map X Y f x) (FreeRPMon-map X Y f y)
map-preserves-R X Y f {[]} {[]} oneb = oneb
map-preserves-R X Y f {[]} {cons _ _ _} onel = onel
map-preserves-R X Y f {cons _ _ _} {[]} oner = oner
map-preserves-R X Y f {cons x xs x#xs} {cons y ys y#ys} (rep refl) = rep refl

map-preserves-∙ : (X Y : SetObj) (f : SetFun X Y)
                → {x y : FreeRPMon (proj₁ X) (proj₂ X)}
                → (p : (proj₁ X ~ proj₂ X) x y)
                → FreeRPMon-map X Y f (∙ (proj₁ X) (proj₂ X) p)
                ≡ ∙ (proj₁ Y) (proj₂ Y) (map-preserves-R X Y f p)
map-preserves-∙ X Y f {[]} {[]} oneb = refl
map-preserves-∙ (X , X-set) (Y , Y-set) f {[]} {cons y ys y#ys} onel
  = WithIrr.cons-cong _≡_ Y-set refl (cong (repeat Y Y-set (f y))
                                               (trans (length-repeat X X-set y (length ys))
                                                      (sym $ length-repeat Y Y-set (f y) (length ys))))
map-preserves-∙ (X , X-set) (Y , Y-set) f {cons x xs x#xs} {[]} oner
  = WithIrr.cons-cong _≡_ Y-set refl (cong (repeat Y Y-set (f x))
                                               (trans (length-repeat X X-set x (length xs))
                                                      (sym $ length-repeat Y Y-set (f x) (length xs))))
map-preserves-∙ (X , X-set) (Y , Y-set) f {cons x xs x#xs} {cons .x ys x#ys} (rep refl)
  = WithIrr.cons-cong _≡_ Y-set refl (cong (repeat Y Y-set (f x)) lem) where
  open ≡-Reasoning
  lem : length (repeat X X-set x (length xs + suc (length ys)))
      ≡ length (repeat Y Y-set (f x) (length xs)) + suc (length (repeat Y Y-set (f x) (length ys)))
  lem =
    begin
      length (repeat X X-set x (length xs + suc (length ys)))
    ≡⟨ length-repeat X X-set x (length xs + suc (length ys))  ⟩
      length xs + suc (length ys)
    ≡⟨ (sym $ cong₂ (λ x y → x + suc y) (length-repeat Y Y-set (f x) (length xs)) (length-repeat Y Y-set (f x) (length ys))) ⟩
      length (repeat Y Y-set (f x) (length xs)) + suc (length (repeat Y Y-set (f x) (length ys)))
    ∎

map-id : {X : SetObj} (xs : FreeRPMon (proj₁ X) (proj₂ X))
            → FreeRPMon-map X X id xs ≡ xs
map-id [] = refl
map-id {X , X-set} (cons x xs x#xs) = WithIrr.cons-cong _≡_ X-set refl (rep-len X X-set xs x#xs)

map-comp : {X Y Z : SetObj} {f : SetFun X Y} {g : SetFun Y Z} (xs : FreeRPMon (proj₁ X) (proj₂ X))
         → FreeRPMon-map X Z (g ∘ f) xs
         ≡ FreeRPMon-map Y Z g (FreeRPMon-map X Y f xs)
map-comp {X , X-set} {Y , Y-set} {Z , Z-set} {f} {g} [] = refl
map-comp {X , X-set} {Y , Y-set} {Z , Z-set} {f} {g} (cons x xs x#xs) = WithIrr.cons-cong _≡_ Z-set refl (cong (repeat Z Z-set (g (f x))) (sym $ length-repeat Y Y-set (f x) (length xs)))


FREE : (ext : Extensionality _ _) → Functor (SET ext) (RPMON ext)
Functor.act (FREE ext) (X , X-set) = MkRPMon (FreeRPMon X X-set) _≡_ (_~_ X X-set) (∙ X X-set) [] (isReflexivePartialMonoid X X-set)
Functor.fmap (FREE ext) {X} {Y} f = MkRPMonMorphism (FreeRPMon-map X Y f) refl (map-preserves-R X Y f) (map-preserves-∙ X Y f)
Functor.identity (FREE ext) = eqRPMonMorphism ext (ext map-id)
Functor.homomorphism (FREE ext) = eqRPMonMorphism ext (ext map-comp)
