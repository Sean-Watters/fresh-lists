module Free.Category.Base where

open import Algebra.Structure.PartialMonoid
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product
open import Data.FreshList.InductiveInductive
open import Relation.Binary hiding (REL)
open import Relation.Binary.PropositionalEquality
open import Function as Fun using (_∘′_)

open import Axiom.UniquenessOfIdentityProofs
open import Axiom.Extensionality.Propositional

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

record PartialMonoid (ℓ : Level) : Set (lsuc ℓ) where
  constructor MkPMon
  field
    -- A carrier set
    Carrier : Set ℓ

    -- A partially defined monoid structure
    ε : Carrier
    _~_ : Carrier → Carrier → Set
    op : (x y : Carrier) → x ~ y → Carrier
    proof : IsPartialMonoid (_≡_ {A = Carrier}) _~_ op ε

    -- We also need the partiality relation to be propositonal
    ~-prop : ∀ {x y} (p q : x ~ y) → p ≡ q

    -- And a relation on the carrier which ignores that monoid structure
    R : Carrier → Carrier → Set
  open IsPartialMonoid public
open PartialMonoid

record PMonMorphism {ℓ} (A B : PartialMonoid ℓ) : Set ℓ where
  constructor MkPMonMorphism
  private
    module A = PartialMonoid A
    module B = PartialMonoid B
  field
    -- A function on the underlying sets...
    fun : Carrier A → Carrier B

    -- which preserves the monoid structure (and ignores the extra relation).
    preserves-ε : fun (A.ε) ≡ B.ε
    preserves-~ : ∀ {x y} → x A.~ y → (fun x) B.~ (fun y)
    preserves-op : ∀ {x y} (p : x A.~ y) → fun (A.op x y p) ≡ B.op (fun x) (fun y) (preserves-~ p)
open PMonMorphism

pmon-id : ∀ {ℓ} {A : PartialMonoid ℓ} → PMonMorphism A A
pmon-id .fun x = x
pmon-id .preserves-ε = refl
pmon-id .preserves-~ x = x
pmon-id .preserves-op p = refl

pmon-comp : ∀ {ℓ} {A B C : PartialMonoid ℓ} → PMonMorphism A B → PMonMorphism B C → PMonMorphism A C
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
  pmon-mor-η' : ∀ {ℓ} {A B : PartialMonoid ℓ}
             → {f : Carrier A → Carrier B}
             → {pε qε : f (A .ε) ≡ B .ε}
             → pε ≡ qε
             → {p~ : ∀ {x y} → (A ._~_) x y → (B ._~_) (f x) (f y)}
             → {p∙ q∙ : ∀ {x y} → (x~y : (A ._~_) x y) → f ((A .op) x y x~y) ≡ (B .op) (f x) (f y) (p~ x~y) }
             → (λ {x} {y} → p∙ {x} {y}) ≡ q∙
             → MkPMonMorphism {ℓ} {A} {B} f pε p~ p∙ ≡ MkPMonMorphism f qε p~ q∙
  pmon-mor-η' refl refl = refl

  -- Now we stengthen it by showing that everything follows from UIP and funext.
  pmon-mor-η : ∀ {ℓ} {A B : PartialMonoid ℓ}
             → (f : Carrier A → Carrier B)
             → (pε qε : f (A .ε) ≡ B .ε)
             → (p~ : ∀ {x y} → (A ._~_) x y → (B ._~_) (f x) (f y))
             → (p∙ q∙ : ∀ {x y} → (x~y : (A ._~_) x y) → f ((A .op) x y x~y) ≡ (B .op) (f x) (f y) (p~ x~y) )
             → MkPMonMorphism {ℓ} {A} {B} f pε p~ p∙ ≡ MkPMonMorphism f qε p~ q∙
  pmon-mor-η {A = A} {B = B} f pε qε p~ p∙ q∙ = pmon-mor-η' pε≡qε p∙≡q∙ where
    pε≡qε : pε ≡ qε
    pε≡qε = uip (Carrier B) pε qε

    p∙≡q∙ : (λ {x} {y} → p∙ {x} {y}) ≡ q∙
    p∙≡q∙ = implicit-extensionality (ext _ _) λ {x} → implicit-extensionality (ext _ _) (λ {y} → ext _ _ (λ x~y → uip (Carrier B) (p∙ x~y) (q∙ x~y)))

  -- ... and from propositionality of ~.
  eq-~ : ∀ {ℓ} {A B : PartialMonoid ℓ}
       → (f : Carrier A → Carrier B)
       → (p q : ∀ {x y} → (A ._~_) x y → (B ._~_) (f x) (f y))
       → (λ {x} {y} → p {x} {y}) ≡ q
  eq-~ {A = A} {B} f p q = implicit-extensionality (ext _ _) λ {x} → implicit-extensionality (ext _ _) (λ {y} → ext _ _ λ x~y → B .~-prop (p x~y) (q x~y))

  -- Therefore, two morphisms are equal when their underlying functions are equal.
  eq-pmon-mor : ∀ {ℓ} {A B : PartialMonoid ℓ} {f g : PMonMorphism A B}
              → f .fun ≡ g .fun
              → A ≡ B
  eq-pmon-mor {A = A} {B} {f} {g} refl rewrite eq-~ (f .fun) (f .preserves-~) (g .preserves-~) = {!pmon-mor-η (f .fun) (f .preserves-ε) (g .preserves-ε) (f .preserves-~) (f .preserves-op) (g .preserves-op) !}

  PMON : ∀ ℓ → Category ℓ
  PMON ℓ .Obj = PartialMonoid ℓ
  PMON ℓ .Hom = PMonMorphism
  PMON ℓ .id = pmon-id
  PMON ℓ .comp = pmon-comp
  PMON ℓ .assoc {A} {B} {C} {D} {f} {g} {h} = {!!}
  PMON ℓ .identityˡ = {!!}
  PMON ℓ .identityʳ = {!!}

  -- Forget the category structure, and functoriality of functors.
  Forget : ∀ ℓ → Functor (PMON (lsuc ℓ)) (GRAPH⁻ ℓ)
  Forget ℓ .act C = {!!}
  Forget ℓ .fmap F = {!!}
  Forget ℓ .identity = {!!}
  Forget ℓ .homomorphism = {!!}


  -- The left-adjoint free functor is, in some sense, fresh lists?
  Free : ∀ ℓ → Functor (GRAPH⁻ ℓ) (PMON (lsuc ℓ))
  Free ℓ .act (X , R) = {!!}
  Free ℓ .fmap = {!!}
  Free ℓ .identity = {!!}
  Free ℓ .homomorphism = {!!}

  -- Idea:
  --
  -- PMON ≅ CAT
  --
  -- `FList R` may be the
