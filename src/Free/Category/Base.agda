module Free.Category.Base where

open import Algebra.Structure.PartialMonoid
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product
open import Data.FreshList.InductiveInductive
open import Relation.Binary hiding (REL)
open import Relation.Binary.PropositionalEquality
open import Function as Fun using (_∘′_)
open import Function.Partial as PFun

open import Axiom.UniquenessOfIdentityProofs
open import Axiom.Extensionality.Propositional

private variable
  ℓc ℓr : Level

record Category (ℓ : Level) : Set (lsuc (lsuc ℓ)) where
  eta-equality

  field
    Obj : Set (lsuc ℓ)
    Hom : Obj -> Obj -> Set ℓ

  field
    id  : ∀ {A} → Hom A A
    comp : ∀ {A B C} → Hom A B → Hom B C → Hom A C

  field -- laws
    assoc     : ∀ {A B C D} {f : Hom A B} {g : Hom B C}{h : Hom C D} →
                comp f (comp g h) ≡ (comp (comp f g) h)
    identityˡ : ∀ {A B} {f : Hom A B} → comp id f ≡ f
    identityʳ : ∀ {A B} {f : Hom A B} → comp f id ≡ f
open Category

record Functor {ℓ} (C D : Category ℓ) : Set (lsuc ℓ) where
  eta-equality
  private
    module C = Category C
    module D = Category D

  field
    act : C.Obj → D.Obj
    fmap : ∀ {X Y} (f : C.Hom X Y) → D.Hom (act X) (act Y)

  field -- laws
    identity     : ∀ {X} → fmap (C.id {X}) ≡ D.id {act X}
    homomorphism : ∀ {X Y Z} {f : C.Hom X Y}{g : C.Hom Y Z} →
                   fmap (C.comp f g) ≡ D.comp (fmap f) (fmap g)
open Functor

idFunctor : ∀ {ℓ} {C : Category ℓ} -> Functor C C
act idFunctor X = X
fmap idFunctor f = f
identity idFunctor = refl
homomorphism idFunctor = refl

compFunctor : ∀ {ℓ} {A B C : Category ℓ} -> Functor A B → Functor B C → Functor A C
act (compFunctor F G) =  (act G) ∘′ (act F)
fmap (compFunctor F G) f = fmap G (fmap F f)
identity (compFunctor F G) = trans (cong (fmap G) (identity F)) (identity G)
homomorphism (compFunctor F G) = trans (cong (fmap G) (homomorphism F)) (homomorphism G)


------------------
------------------
------------------




-- Category where objects are sets plus relations, and morphisms are set functions which ignore the relations.
-- It's almost the category of graphs, excepts the morphisms ignore the edges.
-- Is this something like the grothendieck construction of the slice category of REL?
GRAPH⁻ : ∀ ℓ → Category (lsuc ℓ)
GRAPH⁻ ℓ .Obj = Σ[ X ∈ Set (lsuc ℓ) ] (X → X → Set ℓ)
GRAPH⁻ ℓ .Hom (X , R) (X' , R') = X → X'
GRAPH⁻ ℓ .id x = x
GRAPH⁻ ℓ .comp f g = g ∘′ f
GRAPH⁻ ℓ .assoc = refl
GRAPH⁻ ℓ .identityˡ = refl
GRAPH⁻ ℓ .identityʳ = refl

record PartialMonoid (ℓc ℓr : Level) : Set (lsuc (ℓc ⊔ ℓr)) where
  constructor MkPMon
  field
    -- A carrier set
    Carrier : Set ℓc

    -- A partially defined monoid structure
    ε : Carrier
    _~_ : Carrier → Carrier → Set
    op : PFun.Op₂ _~_
    proof : IsPartialMonoid (_≡_ {A = Carrier}) _~_ op ε

    -- We also need the partiality relation to be propositonal
    ~-prop : ∀ {x y} (p q : x ~ y) → p ≡ q

    -- And a relation on the carrier which ignores that monoid structure
    R : Carrier → Carrier → Set ℓr
  open IsPartialMonoid public
open PartialMonoid

record PMonMorphism (A B : PartialMonoid ℓc ℓr) : Set (ℓc ⊔ ℓr) where
  constructor MkPMonMorphism
  private
    module A = PartialMonoid A
    module B = PartialMonoid B
  field
    -- A function on the underlying sets...
    fun : Carrier A → Carrier B

    -- which preserves the monoid structure (and ignores the extra relation).
    preserves-ε : fun (A.ε) ≡ B.ε
    preserves-~ : Monotonic₁ (A._~_) (B._~_) fun
    preserves-op : PFun.Preserves₂ fun preserves-~ A.op B.op
open PMonMorphism

pmon-id : {A : PartialMonoid ℓc ℓr} → PMonMorphism A A
pmon-id .fun x = x
pmon-id .preserves-ε = refl
pmon-id .preserves-~ x = x
pmon-id .preserves-op p = refl

pmon-comp : {A B C : PartialMonoid ℓc ℓr} → PMonMorphism A B → PMonMorphism B C → PMonMorphism A C
pmon-comp f g .fun x = g .fun (f .fun x)
pmon-comp {A = A} {B = B} {C = C} f g .preserves-ε =
  begin
    g .fun (f .fun (A .ε))
  ≡⟨ cong (g .fun) (f .preserves-ε) ⟩
    g .fun (ε B)
  ≡⟨ g .preserves-ε ⟩
    C .ε
  ∎ where open ≡-Reasoning
pmon-comp f g .preserves-~ x~y = g .preserves-~ (f .preserves-~ x~y)
pmon-comp {A = A} {B = B} {C = C} f g .preserves-op {x} {y} x~y =
  begin
    g .fun (f .fun (op A x y x~y))
  ≡⟨ cong (g .fun) (f .preserves-op x~y) ⟩
    g .fun (op B (f .fun x) (f .fun y) (f .preserves-~ x~y))
  ≡⟨ g .preserves-op (f .preserves-~ x~y) ⟩
    op C (g .fun (f .fun x)) (g .fun (f .fun y)) (g .preserves-~ (f .preserves-~ x~y))
  ∎ where open ≡-Reasoning

module WithUIP+Funext (uip : ∀ {a} (A : Set a) → UIP A) (ext : ∀ i j → Extensionality i j) where

  -- First, an eta rule for pmon morphisms.
  -- We assume definitional equality of f, to tame subst hell a little.
  pmon-mor-η' : {A B : PartialMonoid ℓc ℓr}
             → {f : Carrier A → Carrier B}
             → {pε qε : f (A .ε) ≡ B .ε}
             → pε ≡ qε
             → {p~ q~ : Monotonic₁ (A ._~_) (B ._~_) f}
             → (p~≡q~ : (λ {x} {y} → p~ {x} {y}) ≡ q~)
             → {p∙ : PFun.Preserves₂ f p~ (A .op) (B .op)}
             → {q∙ : PFun.Preserves₂ f q~ (A .op) (B .op)}
             → (λ {x} {y} → p∙ {x} {y})
             ≡ (λ {x} {y} (r : A ._~_ x y)
                   → subst (λ u → f (op A x y r) ≡ op B (f x) (f y) (u r)) (sym p~≡q~) (q∙ r))
             → MkPMonMorphism {A = A} {B} f pε p~ p∙ ≡ MkPMonMorphism f qε q~ q∙
  pmon-mor-η' refl refl refl = refl

  -- Now we stengthen it by showing that everything follows from UIP and funext.
  pmon-mor-η : {A B : PartialMonoid ℓc ℓr}
             → (f : Carrier A → Carrier B)
             → (pε qε : f (A .ε) ≡ B .ε)
             → (p~ q~ : Monotonic₁ (A ._~_) (B ._~_) f)
             → (p∙ : PFun.Preserves₂ f p~ (A .op) (B .op))
             → (q∙ : PFun.Preserves₂ f q~ (A .op) (B .op))
             → MkPMonMorphism {A = A} {B} f pε p~ p∙ ≡ MkPMonMorphism f qε q~ q∙
  pmon-mor-η {A = A} {B = B} f pε qε p~ q~ p∙ q∙ = pmon-mor-η' pε≡qε p~≡q~ (p∙≡q∙ (sym p~≡q~)) where
    pε≡qε : pε ≡ qε
    pε≡qε = uip (Carrier B) pε qε

    p~≡q~ : (λ {x} {y} → p~ {x} {y}) ≡ q~
    p~≡q~
      = implicit-extensionality (ext _ _) λ {x} → implicit-extensionality (ext _ _) (λ {y} → ext _ _ λ x~y → B .~-prop (p~ x~y) (q~ x~y))

    p∙≡q∙ : (eq : (λ {x} {y} → q~ {x} {y}) ≡ p~)
          → (λ {x} {y} → p∙ {x} {y})
          ≡ (λ {x} {y} (r : A ._~_ x y)
               → subst (λ u → f (op A x y r) ≡ op B (f x) (f y) (u r)) eq (q∙ r))
    p∙≡q∙ refl = implicit-extensionality (ext _ _) λ {x} → implicit-extensionality (ext _ _) (λ {y} → ext _ _ (λ x~y → uip (Carrier B) (p∙ x~y) (q∙ x~y)))

  -- Therefore if the underlying functions are equal, the morphisms are equal
  eq-pmon-mor : {A B : PartialMonoid ℓc ℓr} {f g : PMonMorphism A B}
              → f .fun ≡ g .fun
              → f ≡ g
  eq-pmon-mor {f = f} {g = g} refl
    = pmon-mor-η (f .fun) (f .preserves-ε) (g .preserves-ε) (f .preserves-~) (g .preserves-~) (f .preserves-op) (g .preserves-op)

  PMON : ∀ ℓc ℓr → Category (ℓc ⊔ ℓr)
  PMON ℓc ℓr .Obj = PartialMonoid ℓc ℓr
  PMON ℓc ℓr .Hom = PMonMorphism
  PMON ℓc ℓr .id = pmon-id
  PMON ℓc ℓr .comp = pmon-comp
  PMON ℓc ℓr .assoc = eq-pmon-mor refl
  PMON ℓc ℓr .identityˡ = eq-pmon-mor refl
  PMON ℓc ℓr .identityʳ = eq-pmon-mor refl

  -- Forget the partial monoid structure, and that of their morphisms.
  -- (AKA sunce partial monoid = category, take the object set of the cat and forget that functors are functorial)
  Forget : ∀ ℓc ℓr → Functor (PMON (lsuc (ℓc ⊔ ℓr)) (ℓc ⊔ ℓr)) (GRAPH⁻ (ℓc ⊔ ℓr))
  Forget ℓc ℓr .act C = (Carrier C) , C .R
  Forget ℓc ℓr .fmap F = F .fun
  Forget ℓc ℓr .identity = refl
  Forget ℓc ℓr .homomorphism = refl


  -- The left-adjoint free functor is, in some sense, fresh lists?
  Free : ∀ ℓc ℓr → Functor (GRAPH⁻ (ℓc ⊔ ℓr)) (PMON (lsuc (ℓc ⊔ ℓr)) (ℓc ⊔ ℓr))
  Free ℓc ℓr .act (X , R) = {!!}
  Free ℓc ℓr .fmap = {!!}
  Free ℓc ℓr .identity = {!!}
  Free ℓc ℓr .homomorphism = {!!}

  -- Idea:
  --
  -- PMON ≅ CAT
  --
  -- `FList R` may be the
