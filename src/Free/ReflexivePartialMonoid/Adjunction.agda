open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Free.ReflexivePartialMonoid.Adjunction where

open import Algebra.Structure.PartialMonoid
open import Data.FreshList.InductiveInductive
open import Free.ReflexivePartialMonoid.Base
open import Free.ReflexivePartialMonoid.Properties
open import Free.ReflexivePartialMonoid.Power
open import Category.Base

open import Axiom.UniquenessOfIdentityProofs
open import Axiom.Extensionality.Propositional
open import Function
open import Relation.Nullary using () renaming (Irrelevant to Irrelevant₀)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Nat
open import Data.PosNat

-----------------------------------------------
-- The Category of Reflexive Partial Monoids --
-----------------------------------------------

record ReflexivePartialMonoid : Set₁ where
  constructor MkRPMon
  field
    Carrier : Set
    _R_ : Carrier → Carrier → Set
    op : (x y : Carrier) → x R y → Carrier
    ε : Carrier
    proof : IsReflexivePartialMonoid (_≡_ {A = Carrier}) _R_ op ε
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
    preserves-∙ : ∀ {x y} (p : x A.R y) → fun (A.op x y p) ≡ B.op (fun x) (fun y) (preserves-R p)
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
                    → {r  : ∀ {x y} (p : x A.R y) → f (A.op x y p) ≡ B.op (f x) (f y) (q x y p)}
                    → {r' : ∀ {x y} (p : x A.R y) → f (A.op x y p) ≡ B.op (f x) (f y) (q' x y p)}
                    → (qq : q ≡ q')
                    → (λ {x} {y} → r {x} {y}) ≡ subst (λ (z : ∀ x y → x A.R y → (f x) B.R (f y )) → {x y : A.Carrier} (p₁ : x A.R y) → f (A.op x y p₁) ≡ B.op (f x) (f y) (z x y p₁)) (sym qq) r'
                    → (RPMonMorphism A B ∋ MkRPMonMorphism f p (q _ _) r) ≡ MkRPMonMorphism f p (q' _ _) r'
  cong-RPMonMorphism f p {q} {.q} refl refl = refl


eqRPMonMorphism : Extensionality _ _
                → ∀ {A B} {f g : RPMonMorphism A B} → fun f ≡ fun g → f ≡ g
eqRPMonMorphism ext {A} {B} {MkRPMonMorphism f p q r} {MkRPMonMorphism .f p' q' r'} refl =
  begin
    MkRPMonMorphism f p q r
  ≡⟨ cong (λ z → MkRPMonMorphism f z q r) (A-set (proof B) p p')  ⟩
    MkRPMonMorphism f p' q r
  ≡⟨ cong-RPMonMorphism A B f p' (funprop ext (R-prop $ proof B) (λ x y z → q z) λ x y z → q' z) lem ⟩
    MkRPMonMorphism f p' q' r'
  ∎ where
    open ≡-Reasoning
    funprop : Extensionality _ _
            → ∀ {X : Set} {Y : X → X → Set} {Z : X → X → Set} → Irrelevant Z → (f g : (x y : X) → Y x y → Z x y) → f ≡ g
    funprop ext propZ f g = ext λ x → ext (λ y → ext (λ Yxy → propZ (f x y Yxy) (g x y Yxy)))

    lem : (λ {x} {y} → r {x} {y}) ≡ subst (λ z → {x y : Carrier A} (p₁ : (A R x) y) → f (op A x y p₁) ≡ op B (f x) (f y) (z x y p₁))
                    (sym (funprop ext (R-prop (proof B)) (λ x y z → q z) (λ x y z → q' z)))
                    r'
    lem = implicit-extensionality ext (implicit-extensionality ext (ext (λ x₁ → A-set (proof B) (r x₁) _)))


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

open Functor

FORGET : (ext : Extensionality _ _) → Functor (RPMON ext) (SET ext)
act (FORGET ext) (MkRPMon X _ _ _ proof) = X , (A-set $ proof)
fmap (FORGET ext) (MkRPMonMorphism f _ _ _) x = f x
identity (FORGET ext) = ext (λ _ → refl)
homomorphism (FORGET ext) = ext (λ _ → refl)


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
                → FreeRPMon-map X Y f (∙ (proj₁ X) (proj₂ X) x y p)
                ≡ ∙ (proj₁ Y) (proj₂ Y) (from-alt (proj₁ Y) (proj₂ Y)
                                          (FreeRPMon'-map X Y f (to-alt (proj₁ X) (proj₂ X) x))) (from-alt (proj₁ Y) (proj₂ Y)
                                               (FreeRPMon'-map X Y f (to-alt (proj₁ X) (proj₂ X) y))) (map-preserves-R X Y f p)
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

FreeRPMon-Obj : SetObj → ReflexivePartialMonoid
FreeRPMon-Obj (X , X-set) = MkRPMon (FreeRPMon X X-set) (_~_ X X-set) (∙ X X-set) [] (isReflexivePartialMonoid X X-set)

-- Defining the alt presentation as an object here too, for later.
FreeRPMon'-Obj : SetObj → ReflexivePartialMonoid
FreeRPMon'-Obj (X , X-set) = MkRPMon (FreeRPMon' X X-set) (_~'_ X X-set) (∙' X X-set) (inj₁ tt) (isReflexivePartialMonoid' X X-set)

FREE : (ext : Extensionality _ _) → Functor (SET ext) (RPMON ext)
act (FREE ext) = FreeRPMon-Obj
fmap (FREE ext) {X} {Y} f = MkRPMonMorphism (FreeRPMon-map X Y f) refl (map-preserves-R X Y f) (map-preserves-∙ X Y f)
identity (FREE ext) = eqRPMonMorphism ext (ext map-id)
homomorphism (FREE ext) = eqRPMonMorphism ext (ext map-comp)


-----------------------------------
-- The Free-Forgetful Adjunction --
-----------------------------------

open Adjunction


foldr-∙' : (X : SetObj) (Y : ReflexivePartialMonoid)
         → (f : proj₁ X → Carrier Y)
         → FreeRPMon' (proj₁ X) (proj₂ X) → Carrier Y
foldr-∙' X Y f (inj₁ tt) = ε Y
foldr-∙' X Y f (inj₂ (x , n , _)) = pow (proof Y) n (f x)

foldr-∙ : (X : SetObj) (Y : ReflexivePartialMonoid)
        → (f : proj₁ X → Carrier Y)
        → FreeRPMon (proj₁ X) (proj₂ X) → Carrier Y
foldr-∙ (X , X-set) Y f x = foldr-∙' (X , X-set) Y f (to-alt X X-set x)

-- infix operators that take 4 arguments (due to instance args) aren't fun,
-- so here are some new names for the multiplication-is-defined relation
domain = _~_
domain' = _~'_


foldr-∙'-preserves-R : (X : SetObj) (Y : ReflexivePartialMonoid)
                     → (f : proj₁ X → Carrier Y)
                     → {x y : FreeRPMon' (proj₁ X) (proj₂ X)}
                     → domain' (proj₁ X) (proj₂ X) x y
                     → _R_ Y (foldr-∙' X Y f x) (foldr-∙' X Y f y)
foldr-∙'-preserves-R X Y f {inj₁ tt} {y} xRy = ε-compatˡ (proof Y)
foldr-∙'-preserves-R X Y f {inj₂ (x , n , p)} {inj₁ tt} xRy = ε-compatʳ (proof Y)
foldr-∙'-preserves-R (X , X-set) Y f {inj₂ (x , n , p)} {inj₂ (y , m , q)} xRy
  rewrite ~'→≡ X X-set xRy
  = powRpow (proof Y) n m (f y)

foldr-∙'-preserves-∙ : (X : SetObj) (Y : ReflexivePartialMonoid)
                     → (f : proj₁ X → Carrier Y)
                     → {x y : FreeRPMon' (proj₁ X) (proj₂ X)}
                     → (p : domain' (proj₁ X) (proj₂ X) x y)
                     → foldr-∙' X Y f (∙' (proj₁ X) (proj₂ X) x y p)
                     ≡ op Y (foldr-∙' X Y f x)
                            (foldr-∙' X Y f y)
                            (foldr-∙'-preserves-R X Y f p)
foldr-∙'-preserves-∙ (X , X-set) Y f oneb = sym $ identityˡ (proof Y)
foldr-∙'-preserves-∙ (X , X-set) Y f onel = sym $ identityˡ (proof Y)
foldr-∙'-preserves-∙ (X , X-set) Y f oner = sym $ identityʳ (proof Y)
foldr-∙'-preserves-∙ (X , X-set) Y f (rep {n , _} {m , _} {x} refl) = sym $ pow-mult (proof Y) n m (f x) (powRpow (proof Y) n m (f x))

foldr-∙-preserves-∙ : (X : SetObj) (Y : ReflexivePartialMonoid)
                     → (f : proj₁ X → Carrier Y)
                     → {x y : FreeRPMon (proj₁ X) (proj₂ X)}
                     → (p : domain (proj₁ X) (proj₂ X) x y)
                     → foldr-∙ X Y f (∙ (proj₁ X) (proj₂ X) x y p)
                     ≡ op Y (foldr-∙ X Y f x)
                            (foldr-∙ X Y f y)
                            (foldr-∙'-preserves-R X Y f p)
foldr-∙-preserves-∙ (X , X-set) Y f {x} {y} p
  = trans (cong (foldr-∙' (X , X-set) Y f) (to-from-alt X X-set (∙' X X-set (to-alt X X-set x) (to-alt X X-set y) p) ))
          (foldr-∙'-preserves-∙ (X , X-set) Y f {to-alt X X-set x} {to-alt X X-set y} p)

adjunction-lemma : (X : SetObj) (Y : ReflexivePartialMonoid)
                → (h : RPMonMorphism (FreeRPMon'-Obj X) Y)
                → (x : proj₁ X) (n : ℕ)
                → pow (proof Y) (suc n) (fun h (inj₂ (x , 1 , nonZero))) ≡ fun h (inj₂ (x , suc n , nonZero))
adjunction-lemma X Y h x zero = refl
adjunction-lemma X Y h x (suc n)
  = trans (∙-cong (proof Y) refl (adjunction-lemma X Y h x n))
          (sym $ preserves-∙ h (rep refl))

-- The last thing we need is to show is that the two representations of FreeRPMon are isomorphic objects in the category

from-alt-morphism : (X : SetObj) → RPMonMorphism (FreeRPMon'-Obj X) (FreeRPMon-Obj X)
from-alt-morphism (X , X-set) = MkRPMonMorphism (from-alt X X-set) refl
                                                (λ {x} {y} → subst₂ (domain' X X-set) (sym (to-from-alt X X-set x)) (sym (to-from-alt X X-set y)))
                                                (λ {x} {y} p → cong (from-alt X X-set) (∙-cong (proof (FreeRPMon'-Obj (X , X-set)))
                                                                                               {r = p}
                                                                                               {(subst₂ (X ~' X-set) (sym (to-from-alt X X-set x)) (sym (to-from-alt X X-set y)) p)}
                                                                                               (sym (to-from-alt X X-set x))
                                                                                               (sym (to-from-alt X X-set y))))


to-alt-morphism : (X : SetObj) → RPMonMorphism (FreeRPMon-Obj X) (FreeRPMon'-Obj X)
to-alt-morphism (X , X-set) = MkRPMonMorphism (to-alt X X-set) refl id lem where
  lem : {x y : Carrier (FreeRPMon-Obj (X , X-set))} (p : (FreeRPMon-Obj (X , X-set) R x) y)
      → to-alt X X-set (op (FreeRPMon-Obj (X , X-set)) x y p)
      ≡ op (FreeRPMon'-Obj (X , X-set)) (to-alt X X-set x) (to-alt X X-set y) (id p)
  lem {[]} {[]} oneb = refl
  lem {[]} {cons y ys y#ys} onel rewrite rep-len X X-set ys y#ys = refl
  lem {cons x xs x#xs} {[]} oner rewrite rep-len X X-set xs x#xs = refl
  lem {cons x xs x#xs} {cons y ys y#ys} (rep refl) rewrite length-repeat X X-set x (length xs + suc (length ys)) = refl

RPMon-Adjunction : (ext : Extensionality _ _) → (FREE ext) ⊣ (FORGET ext)
to (RPMon-Adjunction ext) {X , X-set} {Y} f x = fun f (from-alt X X-set (inj₂ (x , 1 , nonZero)))
from (RPMon-Adjunction ext) {X , X-set} {Y} f
  = MkRPMonMorphism (foldr-∙ (X , X-set) Y f) refl (foldr-∙'-preserves-R (X , X-set) Y f) (foldr-∙-preserves-∙ (X , X-set) Y f)
left-inverse-of (RPMon-Adjunction ext) {X , X-set} {Y} h = eqRPMonMorphism ext (ext (λ x → lem x)) where
  lem : ∀ xs → foldr-∙ (X , X-set) Y (λ x → fun h (cons x [] [])) xs  ≡ fun h xs
  lem [] = sym (preserves-ε h)
  lem (cons x xs x#xs) = trans (adjunction-lemma (X , X-set) Y (rpmon-comp (from-alt-morphism (X , X-set)) h) x (length xs)) (cong (fun h) (from-to-alt X X-set (cons x xs x#xs)))
right-inverse-of (RPMon-Adjunction ext) k = ext (λ x → refl)
to-natural (RPMon-Adjunction ext) f g = ext (λ x → refl)
