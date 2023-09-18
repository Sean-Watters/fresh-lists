module Data.FreshList.Sigma where

open import Level hiding (zero; suc)
open import Data.Unit.Polymorphic
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Isomorphism
open import Data.List
open import Data.List.Relation.Unary.All as L using ()

open import Data.FreshList.InductiveInductive

module _
    {n m : Level}
    {X : Set n}
    {R : X → X → Set m}
    where

    -- We can externalise freshness in the following way:
    -- We define All-fresh recursively on lists, as the predicate witnessing that
    -- an ordinary list is a fresh list for R:
    All-fresh : List X → Set (n ⊔ m)
    All-fresh [] = ⊤
    All-fresh (x ∷ xs) = L.All (R x) xs × All-fresh xs

    -- Then List#-ext is the type of fresh lists with the proof data externalised.
    -- That is, pairs of ordinary lists and freshness proofs.
    List#-ext : Set (n ⊔ m)
    List#-ext = Σ[ xs ∈ List X ] All-fresh xs

    -- This is isomorphic to our inductive-inductive definition.

    externalise : (xs : List# R) → All-fresh (toList xs)
    externalise [] = tt
    externalise (cons x xs x#xs) = (toListAll (fresh→all x#xs) , externalise xs)

    -- from internal to external
    to : List# R → List#-ext
    to xs = (toList xs , externalise xs)

    -- from external to internal
    from : (xs : List X) → All-fresh xs → List# R
    -- we simultaneously prove that from preserves freshness
    internalise : {x : X} {xs : List X} → L.All (R x) xs → (pxs : All-fresh xs) → x # from xs pxs

    from []  pxs = []
    from (x ∷ xs) (rxxs , pxs) = cons x (from xs pxs) (internalise rxxs pxs)

    internalise {y} {[]} rxxs pxs = []
    internalise (ryx L.∷ ryxs) (_ , pxs) = ryx ∷ internalise ryxs pxs


    -- first roundtrip
    from-to : (xs : List# R) → xs ≡ uncurry from (to xs)
    internalise-externalise : ∀ {x} xs x#xs →
                                subst (x #_) (from-to xs) x#xs ≡ uncurry internalise (externalise (cons x xs x#xs))

    from-to [] = refl
    from-to (cons x xs x#xs) = dcong₂ (cons x) (from-to xs) (internalise-externalise xs x#xs)

    internalise-externalise [] [] = refl
    internalise-externalise {x = x} (cons y ys y#ys) (rxy ∷ x#ys) =
      trans (subst-∷ (from-to ys) (internalise-externalise ys y#ys) rxy x#ys)
            (cong (rxy ∷_) (internalise-externalise ys x#ys))
      where
        subst-∷ : {xs ys : List# R}{y#xs : y # xs}{y#ys : y # ys} →
                  (eq₀ : xs ≡ ys)(eq₁ : subst (y #_) eq₀ y#xs ≡ y#ys) →
                  (u : R x y)(v : x # xs) →
                  subst (x #_) (dcong₂ (cons y) eq₀ eq₁) (u ∷ v) ≡ u ∷ subst (x #_) eq₀ v
        subst-∷ refl refl u v = refl

    -- second roundtrip
    toList-from : (xs : List X) → (p : All-fresh xs) → xs ≡ toList (from xs p)
    toList-from [] pxs = refl
    toList-from (x ∷ xs) (rxxs , pxs) = cong (x ∷_) (toList-from xs pxs)

    externalise-from : ∀ xs pxs → subst All-fresh (toList-from xs pxs) pxs ≡ externalise (from xs pxs)
    externalise-from [] pxs = refl
    externalise-from (x ∷ xs) (rxxs , pxs) = trans (sym (subst-∘ (toList-from xs pxs)))
                                                   (trans (subst-× {P = L.All (R x)} (toList-from xs pxs))
                                                          (cong₂ _,_ (lem₀ xs pxs rxxs) (externalise-from xs pxs)))
      where
        subst-× : ∀ {a b c}{A : Set a} → {P : A → Set b}{Q : A → Set c} → {x y : A} → (eq : x ≡ y) → {u : P x}{v : Q x} →
                  subst (λ z → P z × Q z) eq (u , v) ≡ (subst P eq u , subst Q eq v)
        subst-× refl = refl
        subst-∷ : ∀ {a b}{A : Set a} → {P : A → Set b} → {y : A}{xs ys : List A} → (eq : xs ≡ ys) → {u : P y}{v : L.All P xs} →
                  subst (λ z → L.All P (y ∷ z)) eq (u L.∷ v) ≡ (u L.∷ subst (L.All P) eq v)
        subst-∷ refl = refl
        lem₀ : ∀ {x} xs pxs rxxs → subst (L.All (R x)) (toList-from xs pxs) rxxs ≡ toListAll (fresh→all (internalise rxxs pxs))
        lem₀ [] pxs L.[] = refl
        lem₀ (x ∷ xs) (rxxs , pxs) (ryx L.∷ pxxs) = trans (sym (subst-∘ (toList-from xs pxs)))
                                                          (trans (subst-∷ (toList-from xs pxs)) (cong (ryx L.∷_) (lem₀ xs pxs pxxs)))

    to-from : ∀ xs → xs ≡ to (uncurry from xs)
    to-from (xs , pxs) = dcong₂ _,_ (toList-from xs pxs) (externalise-from xs pxs)


    -- All in all, we have an isomorphism
    List#-ext-iso : List# R ≃ List#-ext
    List#-ext-iso = MkIso to (uncurry from) from-to to-from
