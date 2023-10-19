module Data.PosNat where

open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality

open import Axiom.UniquenessOfIdentityProofs
open import Axiom.UniquenessOfIdentityProofs.Properties

ℕ⁺ : Set
ℕ⁺ = Σ[ n ∈ ℕ ] NonZero n

ℕ⁺-cong : {n m : ℕ} {p : NonZero n} {q : NonZero m} → n ≡ m → (n , p) ≡ (m , q)
ℕ⁺-cong {suc _} {suc _} {record { nonZero = tt }} {record { nonZero = tt }} refl = refl

suc-lem : ∀ {n m} (p : suc n ≡ suc m) → p ≡ cong suc (suc-injective p)
suc-lem refl = refl

UIP-ℕ : UIP ℕ
UIP-ℕ {zero} {zero} refl refl = refl
UIP-ℕ {suc n} {suc m} p q = trans (trans (suc-lem p) (cong (cong suc) (UIP-ℕ {n} {m} (suc-injective p) (suc-injective q)))) (sym (suc-lem q))

to-ℕ : ℕ⁺ → ℕ
to-ℕ = proj₁

pred⁺ : ℕ⁺ → ℕ
pred⁺ (suc n , p) = n

suc⁺ : ℕ → ℕ⁺
suc⁺ n = (suc n , nonZero)

UIP-ℕ⁺ : UIP ℕ⁺
UIP-ℕ⁺ = UIP-Retract suc⁺ pred⁺ (λ { (suc n , p) → refl }) UIP-ℕ


succ⁺ : ℕ⁺ → ℕ⁺
succ⁺ (n , p) = suc n , nonZero

NonZero-+suc : ∀ x y → NonZero (x + suc y)
NonZero-+suc x y rewrite +-suc x y = record { nonZero = tt }

_⁺+⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
(suc n , p) ⁺+⁺ (m , q) = (suc n + m , nonZero)

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

double⁺ : ℕ⁺ → ℕ⁺
double⁺ (suc n , _) = suc (suc (double n)) , nonZero
