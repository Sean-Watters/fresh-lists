{-# OPTIONS --type-in-type --with-K #-}
-- Accepting heartache to keep the headache at bay --

-- open import Level renaming (suc to lsuc)
-- open import Algebra
open import Function

open import Axiom.UniquenessOfIdentityProofs.WithK
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s) renaming (_<_ to _<ℕ_)
open import Data.Nat.Induction
open import Data.Nat.Properties renaming (≤-refl to ≤ℕ-refl)
open import Data.Product hiding (map)
open import Data.Sum
open import Data.Unit using (⊤; tt)
open import Data.Bool hiding (_≤_)
open import Data.Bool.Properties using (push-function-into-if)

open import Induction.WellFounded

open import Relation.Binary hiding (NonEmpty; TotalOrder; Irrelevant)
open import Relation.Binary.PropositionalEquality renaming (isEquivalence to ≡-isEquivalence)
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)

module Util.SortedList.FreeCommMon where

open import Util.FreshListInductiveInductive
open import Util.SortedList.WithDupes
open import Util.Category
open import Util.Category.Adjunctions
open import Util.OICM

open Functor
open Adjunction
_⊣_ = Adjunction

------------------------------------------------------------
-- The Category of Ordered Commutative Idempotent Monoids --
------------------------------------------------------------



record OrderedCommutativeMonoid : Set where
  constructor MkOCM
  field
    Carrier : Set
    _≤_ : Carrier → Carrier → Set
    _∙_ : Carrier → Carrier → Carrier
    ε : Carrier
    proof : IsOrderedCommutativeMonoid _≡_ _≤_ _∙_ ε
  open IsOrderedCommutativeMonoid public
open OrderedCommutativeMonoid

record OcmMorphism (A B : OrderedCommutativeMonoid) : Set where
  constructor MkOcmMorphism
  private
    module A = OrderedCommutativeMonoid A
    module B = OrderedCommutativeMonoid B

  field
    fun : Carrier A → Carrier B
    preserves-ε : fun (A.ε) ≡ B.ε
    preserves-∙ : ∀ x y → fun (x A.∙ y) ≡ (fun x) B.∙ (fun y)
open OcmMorphism

ocm-id : ∀ {A} → OcmMorphism A A
fun ocm-id = Function.id
preserves-ε ocm-id = refl
preserves-∙ ocm-id _ _ = refl

ocm-comp : ∀ {A B C} → OcmMorphism A B → OcmMorphism B C → OcmMorphism A C
fun (ocm-comp f g) = (fun g) ∘ (fun f)
preserves-ε (ocm-comp f g) = trans (cong (fun g) (preserves-ε f)) (preserves-ε g)
preserves-∙ (ocm-comp f g) _ _ = trans (cong (fun g) (preserves-∙ f _ _)) (preserves-∙ g _ _)


eqOcmMorphism : ∀ {A B} → {f g : OcmMorphism A B} → fun f ≡ fun g → f ≡ g
eqOcmMorphism {A} {B} {MkOcmMorphism .f refl p∙} {MkOcmMorphism f refl q∙} refl
  = cong (MkOcmMorphism f refl) (ext λ x → ext λ y → uip (p∙ x y) (q∙ x y))

OCM : Category
Category.Obj OCM = OrderedCommutativeMonoid
Category.Hom OCM = OcmMorphism
Category.id OCM = ocm-id
Category.comp OCM = ocm-comp
Category.assoc OCM = eqOcmMorphism refl
Category.identityˡ OCM = eqOcmMorphism refl
Category.identityʳ OCM = eqOcmMorphism refl

--------------------------------------------------------
-- The Category of Decidable Proposional Total Orders --
--------------------------------------------------------

record PropDecTotalOrder : Set where
  constructor MkTo
  field
    Carrier : Set
    _≤_ : Carrier → Carrier → Set
    proof : IsPropDecTotalOrder _≡_ _≤_
open PropDecTotalOrder

PDTO : Category
Category.Obj PDTO = PropDecTotalOrder
Category.Hom PDTO X Y = Carrier X → Carrier Y
Category.id PDTO = id
Category.comp PDTO f g = g ∘ f
Category.assoc PDTO = refl
Category.identityˡ PDTO = refl
Category.identityʳ PDTO = refl

---------------------------
-- The Forgetful Functor --
---------------------------

FORGET : Functor OCM PDTO
act FORGET (MkOCM X _≤_ _ _ proof) = MkTo X _≤_ (IsOrderedCommutativeMonoid.isPDTO proof)
fmap FORGET f x = fun f x
identity FORGET = refl
homomorphism FORGET = refl

----------------------
-- The Free Functor --
----------------------

SL-map : (X Y : PropDecTotalOrder) → (Carrier X → Carrier Y) → SortedList (proof X) → SortedList (proof Y)
SL-map X Y f [] = []
SL-map X Y f (cons x xs x#xs) = insert (proof Y) (f x) (SL-map X Y f xs)

SL-map-length : (X Y : PropDecTotalOrder) → (f : Carrier X → Carrier Y)
              → (xs : SortedList (proof X))
              → length xs ≡ length (SL-map X Y f xs)
SL-map-length X Y f [] = refl
SL-map-length X Y f (cons x xs x#xs) = trans (cong suc (SL-map-length X Y f xs)) (sym $ insert-length (proof Y) (f x) (SL-map X Y f xs) _)

SL-map-countlem : (X Y : PropDecTotalOrder) (f : Carrier X → Carrier Y)
                → (xs ys : SortedList (proof X))
                → (p : Acc _<ℕ_ (length xs + length ys))
                → (q : Acc _<ℕ_ (length (SL-map X Y f xs) + length (SL-map X Y f ys)))
                → (a : Carrier Y)
                → count (proof Y) (SL-map X Y f (union (proof X) xs ys p)) a
                ≡ count (proof Y) (SL-map X Y f xs) a + count (proof Y) (SL-map X Y f ys) a
SL-map-countlem X Y f [] ys (acc p) (acc q) a = refl
SL-map-countlem X Y f (cons x xs x#xs) [] (acc p) (acc q) a = sym $ +-identityʳ _
SL-map-countlem X Y f (cons x xs x#xs) (cons y ys y#ys) (acc p) (acc q) a =
  begin
    count (proof Y) (SL-map X Y f (union (proof X) (cons x xs x#xs) (cons y ys y#ys) (acc p))) a
  ≡⟨ lem ⟩
    (if does $ a =Y? (f x) then suc cfxs else cfxs) + (if does $ a =Y? (f y) then suc cfys else cfys)
  ≡⟨⟩
    (if does (a =Y? f x) then 1 + cfxs else 0 + cfxs) + (if does (a =Y? f y) then 1 + cfys else 0 + cfys)
  ≡⟨ cong₂ _+_ (sym $ push-function-into-if (_+ cfxs) (does $ a =Y? (f x))) (sym $ push-function-into-if (_+ cfys) (does $ a =Y? (f y))) ⟩
    ((if does (a =Y? (f x)) then 1 else 0) + cfxs) + ((if does (a =Y? (f y)) then 1 else 0) + cfys)
  ≡⟨⟩
    (cfx + cfxs) + (cfy + cfys)
  ≡⟨ cong₂ _+_ (sym $ ∪-countlem (proof Y) (f x ∷# []) (SL-map X Y f xs) _ a) (sym $ ∪-countlem (proof Y) (f y ∷# []) (SL-map X Y f ys) _ a) ⟩
    count (proof Y) (union (proof Y) (f x ∷# []) (SL-map X Y f xs) _) a + count (proof Y) (union (proof Y) (f y ∷# []) (SL-map X Y f ys) _) a
  ≡⟨⟩
    count (proof Y) (SL-map X Y f (cons x xs x#xs)) a + count (proof Y) (SL-map X Y f (cons y ys y#ys)) a
  ∎ where
    open ≡-Reasoning

    _=Y?_ = Util.SortedList.WithDupes._≟_ (proof Y)
    cfx = count (proof Y) (cons (f x) [] []) a
    cfy = count (proof Y) (cons (f y) [] []) a
    cfxs = count (proof Y) (SL-map X Y f xs) a
    cfys = count (proof Y) (SL-map X Y f ys) a
    cfxfxs = count (proof Y) (insert (proof Y) (f x) (SL-map X Y f xs)) a
    cfyfys = count (proof Y) (insert (proof Y) (f y) (SL-map X Y f ys)) a

    acc1 : Acc _<ℕ_ (length (SL-map X Y f xs) + length (insert (proof Y) (f y) (SL-map X Y f ys)))
    acc1 = p _ (s≤s (≤-reflexive (cong₂ _+_ (sym $ SL-map-length X Y f xs) (trans (insert-length (proof Y) (f y) (SL-map X Y f ys) _) (cong suc (sym $ SL-map-length X Y f ys))))))

    acc2 : Acc _<ℕ_ (length (SL-map X Y f (cons x xs x#xs)) + length (SL-map X Y f ys))
    acc2 = p _ (s≤s (≤-reflexive (trans (cong₂ _+_ (trans (insert-length (proof Y) (f x) (SL-map X Y f xs) _) (cong suc (sym $ SL-map-length X Y f xs))) (sym $ SL-map-length X Y f ys))
                                        (sym $ +-suc _ _))))

    -- Note for cleanup later: the two cases here can probably be generalised to one lemma. Maybe.
    lem : count (proof Y) (SL-map X Y f (union (proof X) (cons x xs x#xs) (cons y ys y#ys) (acc p))) a
        ≡ (if does $ a =Y? (f x) then suc cfxs else cfxs)
        + (if does $ a =Y? (f y) then suc cfys else cfys)
    lem with total (proof X) x y
    ... | inj₁ x≤y =
      begin
        count (proof Y) (insert (proof Y) (f x) (SL-map X Y f (union (proof X) xs (cons y ys y#ys) (p _ ≤ℕ-refl)))) a
      ≡⟨ insert-countlem (proof Y) (f x) (SL-map X Y f (union (proof X) xs (cons y ys y#ys) _)) a _ ⟩
        (if does $ a =Y? (f x)
         then suc (count (proof Y) (SL-map X Y f (union (proof X) xs (cons y ys y#ys) (p _ ≤ℕ-refl))) a)
         else      count (proof Y) (SL-map X Y f (union (proof X) xs (cons y ys y#ys) (p _ ≤ℕ-refl))) a)
      ≡⟨ cong (λ z → if (does $ a =Y? (f x)) then suc z else z) (SL-map-countlem X Y f xs (cons y ys y#ys) _ acc1 a) ⟩
        (if does $ a =Y? (f x)
         then suc (cfxs + count (proof Y) (SL-map X Y f (cons y ys y#ys)) a)
         else      cfxs + count (proof Y) (SL-map X Y f (cons y ys y#ys)) a)
      ≡⟨⟩
        (if does $ a =Y? (f x) then ((suc cfxs) + cfyfys) else (cfxs  + cfyfys))
      ≡⟨ (sym $ push-function-into-if (_+ cfyfys) (does $ a =Y? (f x))) ⟩
        (if does $ a =Y? (f x) then suc cfxs else cfxs) + cfyfys
      ≡⟨ cong ((if does $ a =Y? (f x) then suc cfxs else cfxs) +_) (insert-countlem (proof Y) (f y) (SL-map X Y f ys) a _) ⟩
        (if does $ a =Y? (f x) then suc cfxs else cfxs)
        + (if does $ a =Y? (f y) then suc cfys else cfys)
      ∎
    ... | inj₂ y≤x =
      begin
        count (proof Y) (insert (proof Y) (f y) (SL-map X Y f (union (proof X) (cons x xs x#xs) ys (p _ (s≤s (≤-reflexive (sym $ +-suc _ _))))))) a
      ≡⟨ insert-countlem (proof Y) (f y) (SL-map X Y f (union (proof X) (cons x xs x#xs) ys _)) a _ ⟩
        (if (does $ a =Y? (f y))
         then suc (count (proof Y) (SL-map X Y f (union (proof X) (cons x xs x#xs) ys (p _ _))) a)
         else      count (proof Y) (SL-map X Y f (union (proof X) (cons x xs x#xs) ys (p _ _))) a)
      ≡⟨ cong (λ z → if (does $ a =Y? (f y)) then suc z else z) (SL-map-countlem X Y f (cons x xs x#xs) ys _ acc2 a) ⟩
        (if (does $ a =Y? (f y))
         then suc (count (proof Y) (SL-map X Y f (cons x xs x#xs)) a + cfys)
         else      count (proof Y) (SL-map X Y f (cons x xs x#xs)) a + cfys)
      ≡⟨⟩
        (if (does $ a =Y? (f y)) then ((suc cfxfxs) + cfys) else (cfxfxs + cfys))
      ≡⟨ cong (λ z → if does $ (a =Y? f y) then z else cfxfxs + cfys) (sym $ +-suc _ _) ⟩
        (if (does $ a =Y? (f y)) then (cfxfxs + suc cfys  ) else (cfxfxs + cfys))
      ≡⟨ (sym $ push-function-into-if (cfxfxs +_) (does $ a =Y? (f y))) ⟩
        cfxfxs
        + (if does $ a =Y? (f y) then suc cfys else cfys)
      ≡⟨ cong (_+ (if does $ (a =Y? f y) then suc cfys else cfys)) (insert-countlem (proof Y) (f x) (SL-map X Y f xs) a _) ⟩
        (if does $ a =Y? (f x) then suc cfxs else cfxs)
        + (if does $ a =Y? (f y) then suc cfys else cfys)
      ∎

SL-map-preserves-∪ : (X Y : PropDecTotalOrder) (f : Carrier X → Carrier Y)
                   → (xs ys : SortedList (proof X))
                   → (p : Acc _<ℕ_ (length xs + length ys)) (q : Acc _<ℕ_ (length (SL-map X Y f xs) + length (SL-map X Y f ys)))
                   → SL-map X Y f (union (proof X) xs ys p)
                   ≡ union (proof Y) (SL-map X Y f xs) (SL-map X Y f ys) q
SL-map-preserves-∪ X Y f xs ys p q = eqCount→eq (proof Y) (lem X Y f xs ys p q) where
  lem : (X Y : PropDecTotalOrder) (f : Carrier X → Carrier Y)
      → (xs ys : SortedList (proof X))
      → (p : Acc _<ℕ_ (length xs + length ys)) (q : Acc _<ℕ_ (length (SL-map X Y f xs) + length (SL-map X Y f ys)))
      → count (proof Y) (SL-map X Y f (union (proof X) xs ys p))
      ≗ count (proof Y) (union (proof Y) (SL-map X Y f xs) (SL-map X Y f ys) q)
  lem X Y f xs ys p q a =
    begin
      count (proof Y) (SL-map X Y f (union (proof X) xs ys p)) a
    ≡⟨ SL-map-countlem X Y f xs ys p q a ⟩
      (count (proof Y) (SL-map X Y f xs) a) + (count (proof Y) (SL-map X Y f ys) a)
    ≡⟨ sym $ ∪-countlem (proof Y) (SL-map X Y f xs) (SL-map X Y f ys) _ _  ⟩
      count (proof Y) (union (proof Y) (SL-map X Y f xs) (SL-map X Y f ys) q) a
    ∎ where open ≡-Reasoning

SL-map-id : (X : PropDecTotalOrder) (xs : SortedList (proof X))
          → SL-map X X id xs ≡ id xs
SL-map-id X [] = refl
SL-map-id X (cons x xs x#xs) = trans (cong (insert (proof X) x) (SL-map-id X xs)) (insert≡cons (proof X) x#xs _)

SL-map-comp : (X Y Z : PropDecTotalOrder) (f : Carrier X → Carrier Y) (g : Carrier Y → Carrier Z)
            → (xs : SortedList (proof X))
            → SL-map X Z (g ∘ f) xs ≡ SL-map Y Z g (SL-map X Y f xs)
SL-map-comp X Y Z f g [] = refl
SL-map-comp X Y Z f g (cons x xs x#xs) =
  begin
    SL-map X Z (g ∘ f) (cons x xs x#xs)
  ≡⟨⟩
    union (proof Z) (cons (g (f x)) [] []) (SL-map X Z (λ x₁ → g (f x₁)) xs) _
  ≡⟨ union-cong (proof Z) {cons (g (f x)) [] []} _ _ refl (SL-map-comp X Y Z f g xs) ⟩
    union (proof Z) (SL-map Y Z g (cons (f x) [] [])) (SL-map Y Z g (SL-map X Y f xs)) _
  ≡⟨ sym $ SL-map-preserves-∪ Y Z g (cons (f x) [] []) (SL-map X Y f xs) _ (<-wellFounded _) ⟩
    SL-map Y Z g (SL-map X Y f (cons x xs x#xs))
  ∎ where open ≡-Reasoning

SORTEDLIST : Functor PDTO OCM
act SORTEDLIST (MkTo X _≤_ proof) = MkOCM (SortedList proof) (_≤L_ proof) (_∪_ proof ) [] (SortedList-isOCM proof)
fmap SORTEDLIST {X} {Y} f = MkOcmMorphism (SL-map X Y f) refl (λ xs ys → SL-map-preserves-∪ X Y f xs ys _ _)
identity SORTEDLIST {X} = eqOcmMorphism (ext (SL-map-id X))
homomorphism SORTEDLIST {X} {Y} {Z} {f} {g} = eqOcmMorphism (ext (SL-map-comp X Y Z f g))

--------------------
-- The Adjunction --
--------------------

foldr : (A : PropDecTotalOrder) {B : Set}
      → (Carrier A → B → B) → B → SortedList (proof A) → B
foldr A f e [] = e
foldr A f e (cons x xs x#xs) = f x (foldr A f e xs)

foldr-universal : (A : PropDecTotalOrder) {B : Set}
                → (h : SortedList (proof A) → B)                         -- Given some way 'h' of turning SortedLists of As into Bs...
                → (f : Carrier A → B → B) (e : B)                        -- and some function and initial B to fold with...
                → (h [] ≡ e)                                             -- such that the empty list maps to the initial thing...
                → (∀ x xs (fx : x # xs) → h (cons x xs fx) ≡ f x (h xs)) -- and cons maps to an appropriate application of f...
                → foldr A f e ≗ h                                        -- then h is exactly the fold.
foldr-universal A h f e base step [] = sym base
foldr-universal A h f e base step (cons x xs x#xs) =
  begin
    foldr A f e (cons x xs x#xs)
  ≡⟨ cong (f x) (foldr-universal A h f e base step xs) ⟩
    f x (h xs)
  ≡⟨ (sym $ step x xs x#xs) ⟩
    h (cons x xs x#xs)
  ∎ where open ≡-Reasoning

foldr-∙ : (A : PropDecTotalOrder) (B : OrderedCommutativeMonoid)
        → (Carrier A → Carrier B) → SortedList (proof A) → Carrier B
foldr-∙ A B f = foldr A ((_∙_ B) ∘ f) (ε B)

foldr-∙-preserves-∙ : (A : PropDecTotalOrder) (B : OrderedCommutativeMonoid) (f : Carrier A → Carrier B)
                    → (xs ys : SortedList (proof A)) (p : Acc _<ℕ_ (length xs + length ys))
                    → foldr-∙ A B f (union (proof A) xs ys p)
                    ≡ (_∙_ B) (foldr-∙ A B f xs) (foldr-∙ A B f ys)
foldr-∙-preserves-∙ A B f [] ys (acc p) = sym $ identityˡ (proof B) _
foldr-∙-preserves-∙ A B f (cons x xs x#xs) [] (acc p) = sym $ identityʳ (proof B) _
foldr-∙-preserves-∙ A B f (cons x xs x#xs) (cons y ys y#ys) (acc p) with total (proof A) x y
... | inj₁ _ =
  begin
    (f x) ∙' (foldr A (λ a as → f a ∙' as) (ε B) (union (proof A) xs (cons y ys y#ys) (p (length xs + (suc $ length ys)) (s≤s (≤-reflexive refl)))))
  ≡⟨ cong (f x ∙'_) (foldr-∙-preserves-∙ A B f xs (cons y ys y#ys) _) ⟩
    (f x) ∙' (fxs ∙' ((f y) ∙' fys))
  ≡⟨ sym $ assoc (proof B) _ _ _ ⟩
    ((f x) ∙' fxs) ∙' ((f y) ∙' fys)
  ∎ where
    open ≡-Reasoning
    _∙'_ = _∙_ B
    fxs = foldr A (λ a as → f a ∙' as) (ε B) xs
    fys = foldr A (λ a as → f a ∙' as) (ε B) ys
... | inj₂ _ =
  begin
    (f y) ∙' (foldr A (λ a as → f a ∙' as) (ε B) (union (proof A) (cons x xs x#xs) ys (p (length (cons x xs x#xs) + length ys) (s≤s (≤-reflexive (sym (+-suc (length xs) (length ys))))))))
  ≡⟨ cong (f y ∙'_) (foldr-∙-preserves-∙ A B f (cons x xs x#xs) ys _) ⟩
    (f y ∙' (((f x) ∙' fxs) ∙' fys))
  ≡⟨ sym $ assoc (proof B) _ _ _ ⟩
    ((f y ∙' ((f x) ∙' fxs)) ∙' fys)
  ≡⟨ cong (_∙' fys) (comm (proof B) _ _) ⟩
    (((f x) ∙' fxs) ∙' (f y)) ∙' fys
  ≡⟨ assoc (proof B) _ _ _ ⟩
    ((f x) ∙' fxs) ∙' ((f y) ∙' fys)
  ∎ where
    open ≡-Reasoning
    _∙'_ = _∙_ B
    fxs = foldr A (λ a as → f a ∙' as) (ε B) xs
    fys = foldr A (λ a as → f a ∙' as) (ε B) ys

SL-Adjunction : SORTEDLIST ⊣ FORGET
to SL-Adjunction f x = fun f (cons x [] [])
from SL-Adjunction {A} {B} f = MkOcmMorphism (foldr-∙ A B f) refl (λ xs ys → foldr-∙-preserves-∙ A B f xs ys _)
left-inverse-of SL-Adjunction {A} {B} h = eqOcmMorphism (ext $ foldr-universal A
  (fun h)
  (λ x → B ∙ fun h (cons x [] []))
  (ε B)
  (preserves-ε h)
  (λ x xs x#xs → trans (cong (fun h) (sym $ insert≡cons (proof A) x#xs _)) (preserves-∙ h (cons x [] []) xs)))
right-inverse-of SL-Adjunction {A} {B} k = ext (λ x → identityʳ (proof B) (k x) )
to-natural SL-Adjunction {A} {B} f g = ext (λ _ → refl)



-- PART 2. Show that:
  -- (1) DTO and STO are equivalent
  -- (2) DTO/STO being equivalent to Set would imply LEM. This is obvious, since trichotomy implies dec eq, and dec eq is explicity included in DTO.
  --     Other direction is interesting though - is LEM enough to linearly order any set, or do you need some choice principle?
  -- (3) OCM and OICM are not equivalent. Trivial. [a,a] is an obj in OCM but not OICM. Also not really interesting.

-- The category of sets with decidable equality.
DecSet : Category
Category.Obj DecSet = Σ[ X ∈ Set ] Decidable (_≡_ {A = X})
Category.Hom DecSet (A , _) (B , _) = A → B
Category.id DecSet = id
Category.comp DecSet f g = g ∘ f
Category.assoc DecSet = refl
Category.identityˡ DecSet = refl
Category.identityʳ DecSet = refl

-- TODO : prove DecSet is a subcat of Set, but that they aren't equivalent.
-- We can get this for cheap without talking about morphisms at all;
-- it's enough that the inclusion functor DecSet->Set is not full.

-- Clearly PDTO and STO are not equivalent to Set - their objects have decidable equality, but not all sets do.
-- So what about DecSet? Totality and antisymmetry foil the obvious attempts at free orders. Empty order and diagonal order are not total, and the complete order is not antisymmetric.

-- "There exists a set that can't be linearly ordered" is equivalent to the negation of the axiom of choice (according to unsourced internet, at least. need to verify)
-- (Is the constructively weaker "¬ (all sets can be linearly ordered)" also anti-choice?)
-- Agda obviously doesn't validate full-fat choice, but I think it also doesn't it refute it? (I know that countable choice is a theorem)
-- So we shouldn't be able to show that such a non-linearly-orderable set does not exist.
-- But, this statement may still require classical logic, even if it is anti-choice.
-- So we may be able to show that it implies LEM?

-- Foundational questions :
--
-- 1) DecSet is clearly a strict category. Is Set? Not constructively, right? Does strict constructively mean exactly "has decidable equality on objects"?
-- 2)
