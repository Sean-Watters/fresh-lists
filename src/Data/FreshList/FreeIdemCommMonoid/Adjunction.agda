{-# OPTIONS --type-in-type --with-K  #-}
-- Accepting heartache to keep the headache at bay --

open import Level renaming (suc to lsuc)
open import Algebra
open import Function

open import Axiom.UniquenessOfIdentityProofs.WithK

open import Data.Product hiding (map)
open import Data.Sum
open import Data.List.Fresh
open import Data.Empty


open import Relation.Binary hiding (NonEmpty; StrictTotalOrder)
open import Relation.Binary.PropositionalEquality renaming (isEquivalence to ≡-isEquivalence)
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)

module Util.SortedList.FreeForgetful-NoMonotonicity where

open import Util.FreshList
open import Util.SortedList renaming (isOICM to isOICM')
open import Util.Category
open import Util.Category.Adjunctions
open import Util.OICM

open Functor
open Adjunction
_⊣_ = Adjunction


-- Categories library due to Fredrik Nordvall Forsberg.
-- Working with propositional equality here rather than a generic
-- equivalence relation to try and keep life a little easy.

--------------------------------------------------
-- Algebraic Structures on Sorted Lists (again) --
--------------------------------------------------

-- Because we're working with _≡_ here, we actually need to spend extra effort fixing up
-- some types from _≈_, _≈L_, etc.
-- The alternative is working in full generality with those, but losing the ease of use
-- of propositional equality for later proofs.

module _ {X : Set} {_<_ : X → X → Set} (<-STO : IsStrictTotalOrder _≡_ _<_)  where

  ≈L→≡ : ∀ {xs ys} → _≈L_ <-STO xs ys → xs ≡ ys
  ≈L→≡ [] = refl
  ≈L→≡ (cons refl p) = cons-cong _ (≈L→≡ p)

  Tri≈L→Tri≡ : ∀ {lt gt} x y → Tri lt (_≈L_ <-STO x y) gt -> Tri lt (x ≡ y) gt
  Tri≈L→Tri≡ x y (tri< a ¬b ¬c) = tri< a (λ { refl → ¬b (≈L-refl <-STO)}) ¬c
  Tri≈L→Tri≡ x y (tri≈ ¬a b ¬c) = tri≈ ¬a (≈L→≡ b) ¬c
  Tri≈L→Tri≡ x y (tri> ¬a ¬b c) = tri> ¬a (λ { refl → ¬b (≈L-refl <-STO)}) c

  open IsOrderedIdempotentCommutativeMonoid hiding (isICM; isSTO)
  open IsIdempotentCommutativeMonoid
  open IsCommutativeMonoid
  open IsMonoid
  open IsSemigroup
  open IsMagma

  SL-isM : IsMonoid _≡_ (_∪_ <-STO) []
  IsMagma.isEquivalence (IsSemigroup.isMagma (IsMonoid.isSemigroup SL-isM)) = ≡-isEquivalence
  ∙-cong (IsSemigroup.isMagma (IsMonoid.isSemigroup SL-isM)) _≡_.refl _≡_.refl = _≡_.refl
  assoc (IsMonoid.isSemigroup SL-isM) x y z = ≈L→≡ (∪-assoc <-STO x y z)
  identity SL-isM = (λ x → _≡_.refl) , (∪-idʳ <-STO)

  SL-isCM : IsCommutativeMonoid _≡_ (_∪_ <-STO) []
  IsCommutativeMonoid.isMonoid SL-isCM = SL-isM
  comm SL-isCM x y = ≈L→≡ (∪-comm <-STO x y)

  SL-isICM : IsIdempotentCommutativeMonoid _≡_ (_∪_ <-STO) []
  isCommutativeMonoid SL-isICM = SL-isCM
  idem SL-isICM x = ≈L→≡ (∪-idempotent <-STO x)

  SL-isSTO : IsStrictTotalOrder _≡_ (_<L_ <-STO)
  IsStrictTotalOrder.isEquivalence SL-isSTO = ≡-isEquivalence
  IsStrictTotalOrder.trans SL-isSTO = <L-trans <-STO
  IsStrictTotalOrder.compare SL-isSTO x y = Tri≈L→Tri≡ x y (compareL <-STO x y)

  SL-isOICM : IsOrderedIdempotentCommutativeMonoid _≡_ (_<L_ <-STO) (_∪_ <-STO) []
  IsOrderedIdempotentCommutativeMonoid.isICM SL-isOICM = SL-isICM
  IsOrderedIdempotentCommutativeMonoid.isSTO SL-isOICM = SL-isSTO


------------------------------------------------------------
-- The Category of Ordered Idempotent Commutative Monoids --
------------------------------------------------------------



record OrderedIdempotentCommutativeMonoid : Set where
  constructor MkOicm
  field
    Carrier : Set
    _<_ : Carrier → Carrier → Set
    _∙_ : Carrier → Carrier → Carrier
    ε : Carrier
    proof : IsOrderedIdempotentCommutativeMonoid _≡_ _<_ _∙_ ε
open OrderedIdempotentCommutativeMonoid

record OicmMorphism (A B : OrderedIdempotentCommutativeMonoid) : Set where
  constructor MkOicmMorphism
  private
    module A = OrderedIdempotentCommutativeMonoid A
    module B = OrderedIdempotentCommutativeMonoid B

  field
    fun : Carrier A → Carrier B
    preserves-ε : fun (A.ε) ≡ B.ε
    preserves-∙ : ∀ x y → fun (x A.∙ y) ≡ (fun x) B.∙ (fun y)
open OicmMorphism

oicm-id : ∀ {A} → OicmMorphism A A
fun oicm-id = Function.id
preserves-ε oicm-id = refl
preserves-∙ oicm-id _ _ = refl

oicm-comp : ∀ {A B C} → OicmMorphism A B → OicmMorphism B C → OicmMorphism A C
fun (oicm-comp f g) = (fun g) ∘ (fun f)
preserves-ε (oicm-comp f g) = trans (cong (fun g) (preserves-ε f)) (preserves-ε g)
preserves-∙ (oicm-comp f g) _ _ = trans (cong (fun g) (preserves-∙ f _ _)) (preserves-∙ g _ _)


eqOicmMorphism : ∀ {A B} → {f g : OicmMorphism A B} → fun f ≡ fun g → f ≡ g
eqOicmMorphism {A} {B} {MkOicmMorphism .f refl p∙} {MkOicmMorphism f refl q∙} refl
  = cong (MkOicmMorphism f refl) (ext λ x → ext λ y → uip (p∙ x y) (q∙ x y))


OICM : Category
Category.Obj OICM = OrderedIdempotentCommutativeMonoid
Category.Hom OICM = OicmMorphism
Category.id OICM = oicm-id
Category.comp OICM = oicm-comp
Category.assoc OICM {A} {B} {C} {D} {f} {g} {h} = eqOicmMorphism refl
Category.identityˡ OICM {A} {B} {f} = eqOicmMorphism refl
Category.identityʳ OICM {A} {B} {f} = eqOicmMorphism refl

-----------------------------------------
-- The Category of Strict Total Orders --
-----------------------------------------

record StrictTotalOrder : Set where
  constructor MkSto
  field
    Carrier : Set
    _<_ : Carrier → Carrier → Set
    proof : IsStrictTotalOrder _≡_ _<_
open StrictTotalOrder

STO : Category
Category.Obj STO = StrictTotalOrder
Category.Hom STO X Y = Carrier X → Carrier Y
Category.id STO = id
Category.comp STO f g = g ∘ f
Category.assoc STO = refl
Category.identityˡ STO = refl
Category.identityʳ STO = refl

---------------------------
-- The Forgetful Functor --
---------------------------


open IsOrderedIdempotentCommutativeMonoid

FORGET : Functor OICM STO
act FORGET (MkOicm S _<_ _∙_ ε oicm) = MkSto S _<_ (isSTO oicm)
fmap FORGET f = fun f
identity FORGET = refl
homomorphism FORGET = refl

----------------------
-- The Free Functor --
----------------------

SL-map : {X Y : StrictTotalOrder} → (Carrier X → Carrier Y) → SortedList (proof X) → SortedList (proof Y)
SL-map f [] = []
SL-map {X} {Y} f (cons x xs fx) = insert (proof Y) (f x) (SL-map {X} {Y} f xs)


SL-map-lem : ∀ {X Y : StrictTotalOrder}
           → (f : Carrier X → Carrier Y)
           → (x : Carrier X) (xs : SortedList (proof X))
           → (_∈_ $ proof X) x xs                        -- if x ∈ xs...
           → (_∈_ $ proof Y) (f x) (SL-map {X} {Y} f xs) -- then (f x) ∈ (map f xs)
SL-map-lem {X} {Y} f x (cons y ys fy) (here refl)  = mk-insert∈ (proof Y) (SL-map f ys) (inj₁ refl)
SL-map-lem {X} {Y} f x (cons y ys fy) (there x∈ys) = mk-insert∈ (proof Y) (SL-map f ys) (inj₂ (SL-map-lem f x ys x∈ys))

SL-map-lem2 : ∀ {X Y : StrictTotalOrder}
            → (f : Carrier X → Carrier Y)
            → (x : Carrier Y) (xs : SortedList (proof X)) (ys : SortedList (proof X))
            → _⊆_ (proof X) xs ys                     -- if everything in xs is in ys
            → (_∈_ $ proof Y) x (SL-map {X} {Y} f xs) -- and x is in (map f xs)
            → (_∈_ $ proof Y) x (SL-map {X} {Y} f ys) -- then x is in (map f ys)
SL-map-lem2 {X} {Y} f a (cons x₀ xs fx) ys xs⊆ys x∈fxs with cases-insert∈ (proof Y) (SL-map f xs) x∈fxs
... | inj₁ refl  = SL-map-lem  f x₀ ys (xs⊆ys (here refl))
... | inj₂ a∈fxs = SL-map-lem2 f a xs ys (⊆-weaken (proof X) xs⊆ys) a∈fxs

SL-map-concat : ∀ {X Y : StrictTotalOrder}
             → (f : Carrier X → Carrier Y)
             → (a : Carrier Y)
             → (l : SortedList (proof X)) (r : SortedList (proof X))
             → (g : Gluable (proof X) l r)
             → _∈_ (proof Y) a (SL-map {X} {Y} f (concat (proof X) l r g))
             → (_∈_ (proof Y) a (SL-map {X} {Y} f l)) ⊎ (_∈_ (proof Y) a (SL-map {X} {Y} f r))
SL-map-concat f a [] r g pa = inj₂ pa
SL-map-concat {X} {Y} f a (cons l₀ l fl) r g pa with cases-insert∈ (proof Y) (SL-map f (concat (proof X) l r (Gluable-weaken (proof X) g))) pa
... | inj₁ a≡fl₀ = inj₁ (mk-ins∈-here (proof Y) [] (SL-map f l) (f l₀) _ _ a≡fl₀)
... | inj₂ y with SL-map-concat f a l r (Gluable-weaken (proof X) g) y
... | inj₁ a∈mapl = inj₁ (mk-ins∈-r (proof Y) [] (SL-map f l) (f l₀) _ _ a∈mapl)
... | inj₂ a∈mapr = inj₂ a∈mapr

SL-map-ins : ∀ {X Y : StrictTotalOrder}
           → (f : Carrier X → Carrier Y)
           → (a : Carrier Y)
           → (l : SortedList (proof X)) (x : Carrier X) (r : SortedList (proof X))
           → (g : Gluable (proof X) l r) (p : All (λ z → (_<_ X) z x) l)
           → _∈_ (proof Y) a (SL-map {X} {Y} f (proj₁ $ ins (proof X) l r x g p))
           → (_∈_ (proof Y) a (SL-map {X} {Y} f l)) ⊎ (a ≡ f x) ⊎ (_∈_ (proof Y) a (SL-map {X} {Y} f r))
SL-map-ins f a l x [] g p a∈map with SL-map-concat f a l (x ∷# []) p a∈map
... | inj₁ a∈l = inj₁ a∈l
... | inj₂ (here a≡fx) = inj₂ $ inj₁ a≡fx

SL-map-ins {X} {Y} f a l x (cons r₀ r fr) g p a∈map with compare (proof X) x r₀
SL-map-ins {X} {Y} f a l x (cons r₀ r fr) g p a∈map | tri< x<r₀ x≢r₀ x≯r₀
  with SL-map-concat f a (snoc (proof X) l x p) (cons r₀ r fr) (snoc-all< (proof X) x<r₀) a∈map
SL-map-ins {X} {Y} f a l x (cons r₀ r fr) g p a∈map | tri< x<r₀ x≢r₀ x≯r₀ | inj₁ y with SL-map-concat f a l (x ∷# []) p y 
... | inj₁ a∈mapl = inj₁ a∈mapl
... | inj₂ (here a≡fx) = inj₂ $ inj₁ a≡fx
SL-map-ins {X} {Y} f a l x (cons r₀ r fr) g p a∈map | tri< x<r₀ x≢r₀ x≯r₀ | inj₂ y with cases-insert∈ (proof Y) (SL-map f r) y
... | inj₁ a≡fr₀ = inj₂ $ inj₂ (mk-insert∈ (proof Y) (SL-map f r) (inj₁ a≡fr₀))
... | inj₂ a∈mapr = inj₂ $ inj₂ (mk-insert∈ (proof Y) (SL-map f r) (inj₂ a∈mapr))

SL-map-ins {X} {Y} f a l x (cons r₀ r fr) g p a∈map | tri≈ x≮r₀ x≡r₀ x≯r₀ with SL-map-concat f a l (cons r₀ r fr) g a∈map
... | inj₁ a∈mapl = inj₁ a∈mapl
... | inj₂ y with cases-insert∈ (proof Y) (SL-map f r) y
... | inj₁ a≡fr₀ = inj₂ $ inj₂ (mk-insert∈ (proof Y) (SL-map f r) (inj₁ a≡fr₀))
... | inj₂ a∈mapr = inj₂ $ inj₂ (mk-insert∈ (proof Y) (SL-map f r) (inj₂ a∈mapr))

SL-map-ins {X} {Y} f a l x (cons r₀ r fr) g p a∈map | tri> x≮r₀ x≢r₀ x>r₀ with SL-map-ins f a (snoc (proof X) l r₀ g) x r _ _ a∈map
... | inj₂ (inj₁ a≡fx) = inj₂ $ inj₁ a≡fx
... | inj₂ (inj₂ a∈mapr) = inj₂ $ inj₂ (mk-insert∈ (proof Y) (SL-map f r) (inj₂ a∈mapr))
... | inj₁ y with SL-map-concat f a l (r₀ ∷# []) g y
... | inj₁ a∈mapl = inj₁ a∈mapl
... | inj₂ (here a≡fr₀) = inj₂ $ inj₂ (mk-insert∈ (proof Y) (SL-map f r) (inj₁ a≡fr₀))


SL-map-insert : ∀ {X Y : StrictTotalOrder}
              → (f : Carrier X → Carrier Y)
              → (a : Carrier Y) (x : Carrier X) (xs : SortedList (proof X))
              → _∈_ (proof Y) a (SL-map {X} {Y} f (insert (proof X) x xs))
              →  a ≡ f x ⊎ (_∈_ (proof Y) a (SL-map {X} {Y} f xs))
SL-map-insert {X} {Y} f a x xs pxs with SL-map-ins f a [] x xs ([]gluable-l (proof X) xs) [] pxs
... | inj₂ z = z

-- NB: map does *not* preserve gluability because of the lack of monotonicity, so
-- it therefore does not preserve concat. ie, map f (xs ++ ys) is not (map f xs) ++ (map f ys). This might not even
-- be a well-formed statement. But, we can get there by extensionality (and even avoid hassle by applying it further up
-- the chain, so we don't need to think about ins).


SL-map-preserves-insert : ∀ {X Y}
                        → {f : Carrier X → Carrier Y}
                        → (x : Carrier X) (xs : SortedList (proof X))
                        → SL-map {X} {Y} f (insert (proof X) x xs) ≡ insert (proof Y) (f x) (SL-map {X} {Y} f xs)
SL-map-preserves-insert {X} {Y} {f} x xs = ≈L→≡ (proof Y) (extensionality (proof Y) (SL-map f (insertX x xs)) (insertY (f x) (SL-map {X} {Y} f xs)) (λ z → p z , q z)) where
  insertX = insert (proof X)
  insertY = insert (proof Y)
  insX = ins (proof X)
  insY = ins (proof Y)
  _∈X_ = _∈_ (proof X)
  _∈Y_ = _∈_ (proof Y)

  p : ∀ z → z ∈Y (SL-map {X} {Y} f (insertX x xs)) → z ∈Y (insertY (f x) (SL-map {X} {Y} f xs))
  p z pz = mk-insert∈ (proof Y) (SL-map f xs) (SL-map-insert f z x xs pz)


  q : ∀ z → z ∈Y (insertY (f x) (SL-map {X} {Y} f xs)) → z ∈Y (SL-map {X} {Y} f (insertX x xs))
  q z pz with cases-insert∈ (proof Y) (SL-map f xs) pz
  ... | inj₁ refl = SL-map-lem f x (insertX x xs) (mk-insert∈ (proof X) xs (inj₁ refl))
  ... | inj₂ py = SL-map-lem2 f z xs (insert (proof X) x xs) (λ a∈xs → mk-insert∈ (proof X) xs (inj₂ a∈xs)) py


SL-map-preserves-∪ : {X Y : StrictTotalOrder}
                   → {f : Carrier X → Carrier Y}
                   → (xs ys : SortedList (proof X))
                   → SL-map {X} {Y} f (_∪_ (proof X) xs ys) ≡ _∪_ (proof Y) (SL-map {X} {Y} f xs) (SL-map {X} {Y} f ys)
SL-map-preserves-∪ [] ys = refl
SL-map-preserves-∪ {X} {Y} {f} (cons x xs fx) ys =
  begin
    SL-map f (insertX x (xs ∪X ys))
  ≡⟨ SL-map-preserves-insert {X} {Y} {f} x (xs ∪X ys)  ⟩
    insertY (f x) (SL-map f (xs ∪X ys))
  ≡⟨ cong (insertY (f x)) (SL-map-preserves-∪ {X} {Y} {f} xs ys)  ⟩
    insertY (f x) ((SL-map f xs) ∪Y (SL-map f ys))
  ≡⟨ (sym $ ≈L→≡ (proof Y) (∪-insert-assoc (proof Y) (f x) (SL-map f xs) (SL-map f ys))) ⟩
    (insertY (f x) (SL-map f xs)) ∪Y (SL-map f ys)
  ∎ where open ≡-Reasoning
          insertX = insert (proof X)
          insertY = insert (proof Y)
          _∪X_ = _∪_ (proof X)
          _∪Y_ = _∪_ (proof Y)


SORTEDLIST : Functor STO OICM
act SORTEDLIST (MkSto S _<_ sto) = MkOicm (SortedList sto) (_<L_ sto) (_∪_ sto) [] (SL-isOICM sto)
fmap SORTEDLIST {X} {Y} f = MkOicmMorphism (SL-map {X} {Y} f) refl SL-map-preserves-∪
identity SORTEDLIST {X} = eqOicmMorphism (ext lem) where
  lem : ∀ xs → SL-map id xs ≡ xs
  lem [] = refl
  lem (cons x xs fx) = trans (≈L→≡ (proof X) (insert-preserves-≈L (proof X) {x} {x} {SL-map id xs} {xs} refl (≡→≈L (proof X) (lem xs))))
                             (insert-consview (proof X) fx)
homomorphism SORTEDLIST {X} {Y} {Z} {f} {g} = eqOicmMorphism (ext lem) where
  lem : ∀ xs
      → SL-map (g ∘ f) xs
      ≡ (SL-map {Y} {Z} g ∘ SL-map {X} {Y} f) xs
  lem [] = refl
  lem (cons x xs fx) = trans (≈L→≡ (proof Z) (insert-preserves-≈L (proof Z) refl (≡→≈L (proof Z) (lem xs))))
                             (sym $ SL-map-preserves-insert {f = g} (f x) (SL-map {X} {Y} f xs))


-----------------------------------
-- The Free-Forgetful Adjunction --
-----------------------------------

foldr : ∀ {A : StrictTotalOrder} {B : Set} → (Carrier A → B → B) → B → SortedList (proof A) → B
foldr f ε [] = ε
foldr {A} f ε (cons x xs fx) = f x (foldr {A} f ε xs)

-- foldr is the universal property of sorted lists
foldr-universal : ∀ {A} {B : Set}
                → (h : SortedList (proof A) → B)                         -- Given some way 'h' of turning SortedLists of As into Bs...
                → (f : Carrier A → B → B) (e : B)                        -- and some function and initial B to fold with...
                → (h [] ≡ e)                                             -- such that the empty list maps to the initial thing...
                → (∀ x xs (fx : x # xs) → h (cons x xs fx) ≡ f x (h xs)) -- and cons maps to an appropriate application of f...
                → h ≗ foldr {A} {B} f e                                  -- then h is exactly the fold.
foldr-universal h f e base step [] = base
foldr-universal h f e base step (cons x xs fx) =
  begin
    h (cons x xs fx)
  ≡⟨ step x xs fx ⟩
    f x (h xs)
  ≡⟨ cong (f x) (foldr-universal h f e base step xs) ⟩
    foldr f e (cons x xs fx)
  ∎ where open ≡-Reasoning

-- foldr, specialised to functions built from _∙_
foldr-∙ : (A : StrictTotalOrder)
        → (B : OrderedIdempotentCommutativeMonoid)
        → (f : Carrier A → Carrier B)            -- Given a way of turning As into Bs...
        → Carrier (act SORTEDLIST A) → Carrier B -- we get a way for flattening a sorted lists of As into a B
foldr-∙ A B f = foldr {A} (λ a b → (_∙_ B) (f a) b) (ε B)

foldr-∙-preserves-concat : (A : StrictTotalOrder) (B : OrderedIdempotentCommutativeMonoid)
                     → (f : Carrier A → Carrier B)
                     → (xs ys : SortedList (proof A)) (g : Gluable (proof A) xs ys)
                     → foldr-∙ A B f (concat (proof A) xs ys g) ≡ (_∙_ B) (foldr-∙ A B f xs) (foldr-∙ A B f ys)
foldr-∙-preserves-concat A B f [] ys p =
  begin
    foldr-∙ A B f ys
  ≡⟨ (sym $ (identityʳ $ isICM $ proof B) (foldr-∙ A B f ys)) ⟩
    (foldr-∙ A B f ys) ∙' (ε B)
  ≡⟨ (comm $ isICM $ proof B) (foldr-∙ A B f ys) (ε B) ⟩
    (ε B) ∙' (foldr-∙ A B f ys)
  ∎ where open ≡-Reasoning; _∙'_ = _∙_ B
foldr-∙-preserves-concat A B f (cons x xs fx) ys g =
  begin
    foldr-∙ A B f (cons x (concat (proof A) xs ys (Gluable-weaken (proof A) g)) (all→fresh $ concat-fresh (proof A) x xs ys fx g))
  ≡⟨⟩
    (f x) ∙' foldr-∙ A B f (concat (proof A) xs ys (Gluable-weaken (proof A) g))
  ≡⟨ cong (f x ∙'_) (foldr-∙-preserves-concat A B f xs ys (Gluable-weaken (proof A) g)) ⟩
    (f x) ∙' ((foldr-∙ A B f xs) ∙' (foldr-∙ A B f ys))
  ≡⟨ (sym $ (assoc $ isICM $ proof B) (f x) (foldr-∙ A B f xs) (foldr-∙ A B f ys)) ⟩
    ((f x) ∙' (foldr-∙ A B f xs))  ∙' (foldr-∙ A B f ys)
  ≡⟨⟩
    (foldr-∙ A B f (cons x xs fx)) ∙' (foldr-∙ A B f ys)
  ∎ where open ≡-Reasoning; _∙'_ = _∙_ B

foldr-∙-preserves-ins : (A : StrictTotalOrder) (B : OrderedIdempotentCommutativeMonoid)
                    → (f : Carrier A → Carrier B)
                    → (x : Carrier A) (l r : SortedList (proof A)) (g : Gluable (proof A) l r) (p : All (λ y → (_<_ A) y x) l)
                    → foldr-∙ A B f (proj₁ (ins (proof A) l r x g p)) ≡ (_∙_ B) (f x) (foldr-∙ A B f (concat (proof A) l r g))
foldr-∙-preserves-ins A B f x l [] g p =
  begin
    foldr-∙ A B f (proj₁ (ins (proof A) l [] x g p))
  ≡⟨  foldr-∙-preserves-concat A B f l (x ∷# []) p  ⟩
    (foldr-∙ A B f l) ∙' (foldr-∙ A B f (x ∷# []))
  ≡⟨⟩
    (foldr-∙ A B f l) ∙' ((f x) ∙' (ε B))
  ≡⟨ (comm $ isICM $ proof B) (foldr-∙ A B f l) (f x ∙' ε B) ⟩
    ((f x) ∙' (ε B)) ∙' (foldr-∙ A B f l)
  ≡⟨ cong (_∙' foldr-∙ A B f l) ((identityʳ $ isICM $ proof B) (f x)) ⟩
    (f x) ∙' (foldr-∙ A B f l)
  ≡⟨ (sym $ cong (λ xs → (_∙_ B) (f x) (foldr-∙ A B f xs)) (concat-idʳ (proof A) l)) ⟩
    (f x) ∙' (foldr-∙ A B f (concat (proof A) l [] g))
  ∎ where open ≡-Reasoning; _∙'_ = _∙_ B
foldr-∙-preserves-ins A B f x l (cons r₀ r fr) g p with compare (proof A) x r₀
... | tri< a ¬b ¬c =
  begin
    foldr-∙ A B f (concat (proof A) (snoc (proof A) l x p) (cons r₀ r fr) (snoc-all< (proof A) a))
  ≡⟨ foldr-∙-preserves-concat A B f (snoc (proof A) l x p) (cons r₀ r fr) (snoc-all< (proof A) a) ⟩
    (foldr-∙ A B f (snoc (proof A) l x p)) ∙' (foldr-∙ A B f (cons r₀ r fr))
  ≡⟨ cong (_∙' _) (foldr-∙-preserves-concat A B f l (x ∷# []) p) ⟩
    ((foldr-∙ A B f l) ∙' (f x ∙' ε B)) ∙' (f r₀ ∙' foldr-∙ A B f r)
  ≡⟨ cong (_∙' (f r₀ ∙' foldr-∙ A B f r)) ((comm $ isICM $ proof B) (foldr-∙ A B f l) (f x ∙' ε B)) ⟩
    ((f x ∙' ε B) ∙' (foldr-∙ A B f l)) ∙' (f r₀ ∙' foldr-∙ A B f r)
  ≡⟨ (assoc $ isICM $ proof B) _ _ _ ⟩
    (f x ∙' ε B) ∙' ((foldr-∙ A B f l) ∙' (f r₀ ∙' foldr-∙ A B f r))
  ≡⟨ cong (_∙' (foldr-∙ A B f l ∙' (f r₀ ∙' foldr-∙ A B f r))) ((identityʳ $ isICM $ proof B) (f x)) ⟩
    (f x) ∙' ((foldr-∙ A B f l) ∙' (f r₀ ∙' foldr-∙ A B f r))
  ≡⟨⟩
    (f x) ∙' ((foldr-∙ A B f l) ∙' (foldr-∙ A B f (cons r₀ r fr)))
  ≡⟨ cong (f x ∙'_) (sym $ foldr-∙-preserves-concat A B f l (cons r₀ r fr) g) ⟩
    (f x) ∙' (foldr-∙ A B f (concat (proof A) l (cons r₀ r fr) g))
  ∎ where open ≡-Reasoning; _∙'_ = _∙_ B
... | tri≈ ¬a refl ¬c =
  begin
    foldr-∙ A B f (concat (proof A) l (cons x r fr) g)
  ≡⟨ foldr-∙-preserves-concat A B f l (cons x r fr) g ⟩
    foldr-∙ A B f l ∙' (foldr-∙ A B f (cons x r fr))
  ≡⟨⟩
    foldr-∙ A B f l ∙' (f x ∙' foldr-∙ A B f r)
  ≡⟨ cong (λ z → foldr-∙ A B f l ∙' (z ∙' foldr-∙ A B f r)) (sym $ (idem $ isICM $ proof B) _) ⟩
    foldr-∙ A B f l ∙' ((f x ∙' f x) ∙' foldr-∙ A B f r)
  ≡⟨ cong (foldr-∙ A B f l ∙'_) ((assoc $ isICM $ proof B) _ _ _) ⟩
    foldr-∙ A B f l ∙' (f x ∙' (f x ∙' foldr-∙ A B f r))
  ≡⟨ (sym $ (assoc $ isICM $ proof B) _ _ _) ⟩
    (foldr-∙ A B f l ∙' f x) ∙' (f x ∙' foldr-∙ A B f r)
  ≡⟨ cong (_∙' (f x ∙' foldr-∙ A B f r)) ((comm $ isICM $ proof B) _ _) ⟩
    (f x ∙' foldr-∙ A B f l) ∙' (f x ∙' foldr-∙ A B f r)
  ≡⟨ (assoc $ isICM $ proof B) _ _ _ ⟩
    (f x ∙' ((foldr-∙ A B f l) ∙' (f x ∙' foldr-∙ A B f r)))
  ≡⟨⟩
    (f x ∙' ((foldr-∙ A B f l) ∙' (foldr-∙ A B f (cons x r fr))))
  ≡⟨ cong (f x ∙'_) (sym $ foldr-∙-preserves-concat A B f l (cons x r fr) g) ⟩
    (f x) ∙' (foldr-∙ A B f (concat (proof A) l (cons x r fr) g))
  ∎ where open ≡-Reasoning; _∙'_ = _∙_ B
... | tri> ¬a ¬b c =
  begin
    foldr-∙ A B f (proj₁ $ ins (proof A) (snoc (proof A) l r₀ g) r x (snoc-gluable (proof A) (fresh→all fr)) (snoc-all< (proof A) c))
  ≡⟨ foldr-∙-preserves-ins A B f x (snoc (proof A) l r₀ g) r (snoc-gluable (proof A) (fresh→all fr)) (snoc-all< (proof A) c) ⟩
    f x ∙' foldr-∙ A B f (concat (proof A) (snoc (proof A) l r₀ g) r (snoc-gluable (proof A) (fresh→all fr)))
  ≡⟨ cong (λ z → f x ∙' foldr-∙ A B f z)
       {concat (proof A) (concat (proof A) l (r₀ ∷# []) g) r (snoc-gluable (proof A) (fresh→all fr))}
       {concat (proof A) l (concat (proof A) (r₀ ∷# []) r (gluable-singleton (proof A) r₀ r (fresh→all fr))) g}
       (concat-assoc (proof A) l (r₀ ∷# []) r) ⟩
    f x ∙' foldr-∙ A B f (concat (proof A) l (concat (proof A) (r₀ ∷# []) r (gluable-singleton (proof A) r₀ r (fresh→all fr))) g)
  ≡⟨ cong (λ z → f x ∙' foldr-∙ A B f (concat (proof A) l (cons r₀ r z) g)) (fresh-irrelevant _ _) ⟩
    f x ∙' foldr-∙ A B f (concat (proof A) l (cons r₀ r fr) g)
  ∎ where open ≡-Reasoning; _∙'_ = _∙_ B

foldr-∙-preserves-insert : (A : StrictTotalOrder) (B : OrderedIdempotentCommutativeMonoid)
                       → (f : Carrier A → Carrier B)
                       → (x : Carrier A) (xs : SortedList (proof A))
                       → foldr-∙ A B f (insert (proof A) x xs) ≡ (_∙_ B) (f x) (foldr-∙ A B f xs)
foldr-∙-preserves-insert A B f x xs = foldr-∙-preserves-ins A B f x [] xs ([]gluable-l (proof A) xs) []

foldr-∙-preserves-∙ : (A : StrictTotalOrder) (B : OrderedIdempotentCommutativeMonoid)
                  → (f : Carrier A → Carrier B)
                  → (xs ys : SortedList (proof A))
                  → foldr-∙ A B f ((_∪_ (proof A)) xs ys)
                  ≡ (_∙_ B) (foldr-∙ A B f xs) (foldr-∙ A B f ys)
foldr-∙-preserves-∙ A B f [] [] = sym $ (identityʳ $ isICM $ proof B) (ε B)
foldr-∙-preserves-∙ A B f [] (cons y ys fy) =
  begin
    (f y) ∙' foldr-∙' f ys
  ≡⟨ cong (_∙' foldr-∙' f ys)
          (trans (sym $ (identityʳ $ isICM $ proof B) (f y))
                 ((comm $ isICM $ proof B) _ _)) ⟩
    ((ε B) ∙' (f y)) ∙' (foldr-∙' f ys)
  ≡⟨ (assoc $ isICM $ proof B) _ _ _ ⟩
    (ε B) ∙' ((f y) ∙' foldr-∙' f ys)
  ∎ where open ≡-Reasoning; _∙'_ = (_∙_ B); foldr-∙' = foldr-∙ A B
foldr-∙-preserves-∙ A B f (cons x xs fx) ys =
  begin
    foldr-∙' f (insert (proof A) x ((proof A ∪ xs) ys))
  ≡⟨ foldr-∙-preserves-insert A B f x (_∪_ (proof A) xs ys) ⟩
    f x ∙' foldr-∙' f ((proof A ∪ xs) ys)
  ≡⟨  cong (f x ∙'_) (foldr-∙-preserves-∙ A B f xs ys) ⟩
    (f x) ∙' ((foldr-∙' f xs) ∙' (foldr-∙' f ys))
  ≡⟨ sym ((assoc $ isICM $ proof B) _ _ _) ⟩
    ((f x) ∙' (foldr-∙' f xs)) ∙' (foldr-∙' f ys)
  ∎ where open ≡-Reasoning; _∙'_ = (_∙_ B); foldr-∙' = foldr-∙ A B


SL-Adjunction : SORTEDLIST ⊣ FORGET
to SL-Adjunction f x = fun f (x ∷# [])

fun (from SL-Adjunction {A} {B} f) = foldr-∙ A B f
preserves-ε (from SL-Adjunction f) = refl
preserves-∙ (from SL-Adjunction {A} {B} f) = foldr-∙-preserves-∙ A B f

left-inverse-of SL-Adjunction {A} {B} f
  = eqOicmMorphism (ext λ xs →
      sym (foldr-universal (fun f) (λ a → (_∙_ B) (fun f (a ∷# []))) (ε B) (preserves-ε f)
        (λ x xs fx → trans (cong (fun f) (sym $ insert-consview (proof A) fx)) (preserves-∙ f (x ∷# []) xs)) xs))
right-inverse-of SL-Adjunction {A} {B} f = ext λ x → (identityʳ $ isICM $ proof B) (f x)
to-natural SL-Adjunction f g = ext (λ _ → ext (λ _ → refl))
