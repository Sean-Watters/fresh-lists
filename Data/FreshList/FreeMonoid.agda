{-# OPTIONS --without-K --safe #-}
open import Algebra.Definitions
open import Algebra.Structures
open import Algebra.Structure.Monoid

open import Data.FreshList.InductiveInductive
open import Data.Unit
open import Data.Product

open import Function

open import Relation.Const
open import Relation.Binary.PropositionalEquality

module Data.FreshList.FreeMonoid where

open Monoid
open MonoidMorphism

List : Set → Set
List X = List# {A = X} R⊤

tt# : ∀ {X} {x : X} {xs : List X} → x # xs
tt# {x = x} {[]} = []
tt# {x = x} {cons y ys y#ys} = tt ∷ tt# {x = x} {ys}

_++_ : ∀ {X} → List X → List X → List X
[] ++ ys = ys
(cons x xs _) ++ ys = cons x (xs ++ ys) tt#
infixl 1 _++_

++-assoc : ∀ {X} → Associative _≡_ (_++_ {X})
++-assoc [] y z = refl
++-assoc (cons x xs x#xs) y z = cong (λ z → cons x z tt#) (++-assoc xs y z)

++-idR : ∀ {X} → RightIdentity _≡_ [] (_++_ {X})
++-idR [] = refl
++-idR {X} (cons x xs x#xs) = trans
  (cong (λ z → cons x z tt#) (++-idR xs))
  (cong (cons x xs) (WithIrr.#-irrelevant R⊤ (λ {a} {b} → R⊤-irr {X} {a} {b}) _ _))

++-id : ∀ {X} → Identity _≡_ [] (_++_ {X})
proj₁ ++-id xs = refl
proj₂ ++-id xs = ++-idR xs

ListMonoid : ∀ {X} → IsMonoid {A = List X} _≡_ _++_ []
IsMagma.isEquivalence (IsSemigroup.isMagma (IsMonoid.isSemigroup ListMonoid)) = isEquivalence
IsMagma.∙-cong (IsSemigroup.isMagma (IsMonoid.isSemigroup ListMonoid)) refl refl = refl
IsSemigroup.assoc (IsMonoid.isSemigroup ListMonoid) = ++-assoc
IsMonoid.identity ListMonoid = ++-id

List' : Set → Monoid
Carrier (List' X) = List X
_∙_ (List' X) = _++_
ε (List' X) = []
proof (List' X) = ListMonoid

map-list-fun : ∀ {X Y} → (X → Y) → List X → List Y
map-list-fun f []  = []
map-list-fun f (cons x xs x#xs) = cons (f x) (map-list-fun f xs) tt#

map-list-preserves-∙ : ∀ {X} {Y} (f : X → Y)
                         (xs : Carrier (List' X)) (ys : Carrier (List' X)) →
                        map-list-fun f ((List' X ∙ xs) ys) ≡
                        (List' Y ∙ map-list-fun f xs) (map-list-fun f ys)
map-list-preserves-∙ f [] ys = refl
map-list-preserves-∙ f (cons x xs x#xs) ys = cong (λ z → cons (f x) z tt#) (map-list-preserves-∙ f xs ys)

map-list : ∀ {X Y} → (X → Y) → MonoidMorphism (List' X) (List' Y)
fun (map-list f) xs = map-list-fun f xs
preserves-ε (map-list f) = refl
preserves-∙ (map-list f) xs ys = map-list-preserves-∙ f xs ys

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr f e [] = e
foldr f e (cons x xs x#xs) = f x (foldr f e xs)

fold-∙ : {A : Set} (B : Monoid) → (A → Carrier B) → List A → Carrier B
fold-∙ {A} B f = foldr {A} {Carrier B} (λ a b → _∙_ B (f a) b) (ε B)

fold-∙-preserves-∙ : {X : Set} (B : Monoid) (f : X → Carrier B) (x y : List X)
                   → fold-∙ B f ((List' X ∙ x) y) ≡ (B ∙ fold-∙ B f x) (fold-∙ B f y)
fold-∙-preserves-∙ (Mon _ _ _ p) f [] y = sym $ proj₁ (IsMonoid.identity p) _
fold-∙-preserves-∙ B f (cons x xs x#xs) y = trans (cong (_∙_ B (f x)) (fold-∙-preserves-∙ B f xs y)) (sym $ (IsSemigroup.assoc $ IsMonoid.isSemigroup $ proof B) (f x) (fold-∙ B f xs) (fold-∙ B f y))

foldr-universal : ∀ {A B : Set} (h : List A → B) (f : A → B → B) (e : B) → (h [] ≡ e) →
                  (∀ x xs → h (cons x xs tt#) ≡ f x (h xs)) →
                  h ≗ foldr f e
foldr-universal h f e base step [] = base
foldr-universal h f e base step (cons x xs _) =
  begin
    h (cons x xs _)
  ≡⟨ cong (λ p → h (cons x xs p)) (WithIrr.#-irrelevant R⊤ (λ {tt tt → refl}) _ _) ⟩
    h (x ∷# xs)
  ≡⟨ step x xs ⟩
    f x (h xs)
  ≡⟨ cong (f x) (foldr-universal h f e base step xs) ⟩
    f x (foldr f e xs)
  ∎ where open ≡-Reasoning
