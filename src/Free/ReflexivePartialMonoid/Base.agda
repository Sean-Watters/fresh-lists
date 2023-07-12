{-# OPTIONS --safe --without-K #-}

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Free.ReflexivePartialMonoid.Base
  (A : Set)
  (A-set : Irrelevant (_≡_ {A = A}))
  where

open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Unit

open import Data.FreshList.InductiveInductive

ℕ⁺ : Set
ℕ⁺ = Σ[ n ∈ ℕ ] NonZero n

FreeRPMon : Set
FreeRPMon = List# {A = A} _≡_

mutual
  repeat : A → ℕ → FreeRPMon
  repeat a zero = []
  repeat a (suc n) = cons a (repeat a n) (repeat-equal a n)

  repeat-equal : (a : A) → (n : ℕ) → a # repeat a n
  repeat-equal a zero = []
  repeat-equal a (suc n) = refl ∷ repeat-equal a n

length-repeat : (a : A) → (n : ℕ) → length (repeat a n) ≡ n
length-repeat a zero = refl
length-repeat a (suc n) = cong suc (length-repeat a n)

to-alt : FreeRPMon → ⊤ ⊎ (A × ℕ⁺)
to-alt [] = inj₁ tt
to-alt (cons x xs x#xs) = inj₂ (x , (suc (length xs) , _))

from-alt : ⊤ ⊎ (A × ℕ⁺) → FreeRPMon
from-alt (inj₁ _) = []
from-alt (inj₂ (a , (n , _))) = repeat a n

mutual
  double : FreeRPMon → FreeRPMon
  double [] = []
  double (cons x xs x#xs) = cons x (cons x (double xs) (double-fresh x#xs)) (refl ∷ (double-fresh x#xs))

  double-fresh : {x : A} {xs : FreeRPMon} → x # xs → x # (double xs)
  double-fresh [] = []
  double-fresh (px ∷ pxs) = px ∷ (px ∷ double-fresh pxs)

-- Double, except with a type that looks more like refl pmon multiplication
double' : {x y : FreeRPMon} → x ≡ y → FreeRPMon
double' {x} refl = double x
