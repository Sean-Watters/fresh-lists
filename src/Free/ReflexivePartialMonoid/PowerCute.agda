{-# OPTIONS --safe --without-K #-}

open import Algebra.Structure.PartialMonoid
open import Relation.Binary.PropositionalEquality

module Free.ReflexivePartialMonoid.PowerCute
  {X : Set}
  {_R_ : X → X → Set}
  {op : (x y : X) → x R y → X}
  {ε : X}
  (X-RPMon : IsReflexivePartialMonoid _≡_ _R_ op ε)
  where

-- Theorem : Exponentiation is defined for any reflexive partial monoid.
--
-- Proof Sketch :
---- (1) By reflexivity, x^(2^n) is trivially defined for all (x : X) and (n : ℕ).
---- (2) To produce x^k, we:
-------- (a) Choose n such that (2^n)>k.
-------- (b) Re-write x^(2^n) to be right-bracketed using associativity.
-------- (c) Chop off outer x's until we have k many x's in term. This is now x^k.
--
-- We can make this easier by talking about "cute lists", thanks to conor. More at 6

open import Data.Unit
open import Data.Empty
open import Data.List as List
open import Data.List.Properties
open import Data.List.NonEmpty
open import Data.Nat
open import Data.Nat.Properties
open import Data.PosNat
open import Data.Product hiding (assocˡ; assocʳ)
open import Data.Product.Properties using (,-injectiveˡ)
open import Function

open IsReflexivePartialMonoid X-RPMon


cong-op : ∀ {a b x y} → a ≡ x → b ≡ y → (p : a R b) → (q : x R y) → op a b p ≡ op x y q
cong-op {a} {b} refl refl p q = cong (op a b) (R-prop p q)

{-

-- Warmup: the sort of induction principle we need for lists.
data Chop (xs : List⁺ X) : Set where
  chop : ((ys zs : List⁺ X) → xs ≡ ys ⁺++⁺ zs → (Chop ys) × (Chop zs))
       → Chop xs

chop-singleton : ∀ x → Chop (x ∷ [])
chop-singleton x = chop f where
  f : (ys zs : List⁺ X) → x ∷ [] ≡ ys ⁺++⁺ zs → Chop ys × Chop zs
  f (y ∷ []) zs ()
  f (y ∷ y' ∷ ys) zs ()

chop-cons : ∀ x xs → Chop xs → Chop (x ∷⁺ xs)
chop-cons x xs (chop f) = chop g where
  g : (ys zs : List⁺ X) → x ∷⁺ xs ≡ ys ⁺++⁺ zs → Chop ys × Chop zs
  g (.x ∷ []) .xs refl = chop-singleton x , (chop f)
  g (.x ∷ y ∷ ys) zs refl = let (cyys , czs) = f (y ∷ ys) zs refl
                            in chop-cons x (y ∷ ys) cyys , czs

-- The key insight from Conor -- we represent monomials in the monoid as
-- nonempty lists which satisfy a predicate which encodes the partiality.
-- That is, elements of the list can be multiplied according to any choice
-- of bracketing. Thus, such lists support a "crush" operation which multiplies
-- everything together.
mutual
  -- The predicate - a list is "cute" if it can be cut everywhere such that the
  -- pieces are compatible.
  data Cute (xs : List⁺ X) : Set where
    cute : ((ys zs : List⁺ X) → xs ≡ ys ⁺++⁺ zs    -- If all ways of cutting up xs into two non-empty partitions ys and zs
           → Σ[ cys ∈ Cute ys ] Σ[ czs ∈ Cute zs ] -- ...result in ys and zs being cute
             ⟦ cys ⟧ R ⟦ czs ⟧)                    -- ...and their crushes being compatible,
         → Cute xs                                 -- then xs is cute.

  -- Pronounced "crush" due to Conor McBride; that is, this
  -- tells us how to crush on cute things. Always with the puns.
  ⟦_⟧ : ∀ {xs} → Cute xs → X
  ⟦_⟧ {x ∷ []} (cute f) = x
  ⟦_⟧ {x ∷ (y ∷ ys)} (cute f) = let (c , d , cRd) = f (x ∷ []) (y ∷ ys) refl
                                in op ⟦ c ⟧ ⟦ d ⟧ cRd


-- Crushing cute lists gives the same result if the underlying lists were equal
crush-cute-unique : ∀ {xs ys} → (cx : Cute xs) (cy : Cute ys) → xs ≡ ys → ⟦ cx ⟧ ≡ ⟦ cy ⟧
crush-cute-unique {x ∷ []} (cute p) (cute q) refl = refl
crush-cute-unique {x ∷ y ∷ t} (cute p) (cute q) refl = cong-op (crush-cute-unique (proj₁ (p (x ∷ []) (y ∷ t) refl)) (proj₁ (q (x ∷ []) (y ∷ t) refl)) refl)
                                                               (crush-cute-unique (proj₁ (proj₂ (p (x ∷ []) (y ∷ t) refl))) (proj₁ (proj₂ (q (x ∷ []) (y ∷ t) refl))) refl)
                                                               (proj₂ (proj₂ (p (x ∷ []) (y ∷ t) refl))) (proj₂ (proj₂ (q (x ∷ []) (y ∷ t) refl)))

cute-singleton : ∀ x → Cute (x ∷ [])
cute-singleton x = cute f where
  f : (ys zs : List⁺ X) → x ∷ [] ≡ ys ⁺++⁺ zs
    → Σ[ cys ∈ (Cute ys) ] Σ[ czs ∈ (Cute zs) ] (⟦ cys ⟧ R ⟦ czs ⟧)
  f (_ ∷ []) _ ()
  f (_ ∷ _ ∷ _) _ ()

crush-cute-singleton : ∀ {x} → (cx : Cute (x ∷ [])) → ⟦ cx ⟧ ≡ x
crush-cute-singleton (cute _) = refl

-- Concatenating then crushing is the same as crushing then muliplying.
cute-unique : ∀ {x y} (cx : Cute x) (cy : Cute y) (cxy : Cute (x ⁺++⁺ y)) → (p : ⟦ cx ⟧ R ⟦ cy ⟧) → ⟦ cxy ⟧ ≡ op ⟦ cx ⟧ ⟦ cy ⟧ p
cute-unique {x ∷ []} {y ∷ ys} (cute cx) (cute cy) (cute cxy) p = cong-op (crush-cute-singleton $ proj₁ $ cxy (x ∷ []) (y ∷ ys) refl)
                                                                         (crush-cute-unique (proj₁ $ proj₂ $ cxy (x ∷ []) (y ∷ ys) refl) (cute cy) refl )
                                                                         (proj₂ $ proj₂ $ cxy (x ∷ []) (y ∷ ys) refl) p
cute-unique {x1 ∷ x2 ∷ xs} {y ∷ ys} (cute cx) (cute cy) (cute cxy) q =
  begin
    ⟦ cute cxy ⟧
  ≡⟨⟩
    op ⟦ proj₁ (cxy (x1 ∷ []) (x2 ∷ xs ++ y ∷ ys) refl) ⟧
       ⟦ proj₁ (proj₂ (cxy (x1 ∷ []) (x2 ∷ xs ++ y ∷ ys) refl)) ⟧
       (proj₂ (proj₂ (cxy (x1 ∷ []) (x2 ∷ xs ++ y ∷ ys) refl)))
  ≡⟨ cong-op (crush-cute-unique (proj₁ (cxy (x1 ∷ []) (x2 ∷ xs ++ y ∷ ys) refl)) (proj₁ (cx (x1 ∷ []) (x2 ∷ xs) refl)) refl)
             (cute-unique (proj₁ (proj₂ (cx (x1 ∷ []) (x2 ∷ xs) refl))) (cute cy) (proj₁ (proj₂ (cxy (x1 ∷ []) (x2 ∷ xs ++ y ∷ ys) refl))) (proj₁ assoc-uvw))
             (proj₂ (proj₂ (cxy (x1 ∷ []) (x2 ∷ xs ++ y ∷ ys) refl))) (proj₁ (proj₂ assoc-uvw)) ⟩
    op u (op v w (proj₁ assoc-uvw)) (proj₁ (proj₂ assoc-uvw))
  ≡⟨ (sym $ proj₂ (proj₂ assoc-uvw)) ⟩
    op (op u v p) w q
  ≡⟨⟩
    op ⟦ cute cx ⟧ ⟦ cute cy ⟧ q
  ∎ where
    open ≡-Reasoning
    u : X
    u = ⟦ proj₁ (cx (x1 ∷ []) (x2 ∷ xs) refl) ⟧

    v : X
    v = ⟦ proj₁ (proj₂ (cx (x1 ∷ []) (x2 ∷ xs) refl)) ⟧

    w : X
    w = ⟦ cute cy ⟧

    p : u R v
    p = proj₂ (proj₂ (cx (x1 ∷ []) (x2 ∷ xs) refl))

    assoc-uvw : Σ[ p' ∈ v R w ] Σ[ q' ∈ u R (op v w p') ] ((op (op u v p) w q) ≡ (op u (op v w p') q'))
    assoc-uvw = assocʳ p q


cute-cons : ∀ x xs → (cxs : Cute xs) → x R ⟦ cxs ⟧ → Cute (x ∷⁺ xs)
cute-cons x xs (cute f) xRxs = cute (g x xs (cute f) xRxs) where
  cute-cons-lem :  ∀ x xs → (cxs : Cute xs) → (p : x R ⟦ cxs ⟧) → op x ⟦ cxs ⟧ p ≡ ⟦ cute-cons x xs cxs p ⟧
  cute-cons-lem x xs (cute _) p = {!!}

  g : ∀ x xs (cxs : Cute xs) → x R ⟦ cxs ⟧
    → (ys zs : List⁺ X) → x ∷⁺ xs ≡ ys ⁺++⁺ zs
    → Σ[ cys ∈ (Cute ys) ] Σ[ czs ∈ (Cute zs) ] (⟦ cys ⟧ R ⟦ czs ⟧)
  g x xs (cute f) xRxs (.x ∷ []) .xs refl = cute-singleton x , cute f , xRxs
  g x xs (cute f) xRxs (.x ∷ y ∷ ys) zs refl
    = let (cyys , czs , yysRzs) = f (y ∷ ys) zs refl
          (xRyys , xyysRzs) = assocL1 {x} {⟦ cyys ⟧} {⟦ czs ⟧} yysRzs (subst (x R_) (cute-unique cyys czs (cute f) yysRzs) xRxs)
      in cute-cons x (y ∷ ys) cyys xRyys , czs , subst (_R ⟦ czs ⟧ ) (cute-cons-lem x (y ∷ ys) cyys xRyys) xyysRzs

cute-cons-inv : ∀ {x xs} → Cute (x ∷⁺ xs) → Cute xs
cute-cons-inv {x} {y ∷ ys} (cute f) = proj₁ $ proj₂ $ f (x ∷ []) (y ∷ ys) refl

cute-++ : ∀ {xs ys} → (cxs : Cute xs) → (cys : Cute ys) → ⟦ cxs ⟧ R ⟦ cys ⟧ → Cute (xs ⁺++⁺ ys)
cute-++ {xs} {ys} cxs cys xsRys = cute (g xs ys cxs cys xsRys) where
  g : ∀ xs ys (cxs : Cute xs) (cys : Cute ys) → ⟦ cxs ⟧ R ⟦ cys ⟧
    → (u v : List⁺ X) → xs ⁺++⁺ ys ≡ u ⁺++⁺ v
    → Σ[ cu ∈ Cute u ] Σ[ cv ∈ Cute v ] (⟦ cu ⟧ R ⟦ cv ⟧)
  g (x ∷ []) (y ∷ ys) (cute cxs) (cute cys) r (.x ∷ []) (.y ∷ .ys) refl = cute-singleton x , (cute cys) , r
  g (x ∷ []) (y ∷ .(us ++ v ∷ vs)) (cute cxs) (cute cys) r (.x ∷ .y ∷ us) (v ∷ vs) refl
    = let (cyus , cvvs , yusRvvs) = cys (y ∷ us) (v ∷ vs) refl
      in cute-cons x (y ∷ us) cyus {!r!} , cvvs , {!!}
  g (x1 ∷ x2 ∷ xs) (y ∷ ys) (cute cxs) (cute cys) r (.x1 ∷ []) (.x2 ∷ .(xs ++ y ∷ ys)) refl
    = cute-singleton x1 , cute-++ (cute-cons-inv (cute cxs)) {!(cute cys)!} {!!} , {!!}
  g (x1 ∷ x2 ∷ xs) (y ∷ ys) (cute cxs) (cute cys) r (u1 ∷ u2 ∷ us) (v ∷ vs) eq = {!!}


-- In particular, thanks to reflexivity of R, doubling is a primitive thing we can do
-- to cute lists.

double⁺ : List⁺ X → List⁺ X
double⁺ xs = xs ⁺++⁺ xs

cute-double : {xs : List⁺ X} → Cute xs → Cute (double⁺ xs)
cute-double cxs = cute-++ cxs cxs reflexive

-- Repeat gives us lists whih we hope represent monomials xⁿ.
-- If we can show that repeat is cute, then our dreams come true and
-- power will be its crush.
-- EXCEPT: that's probably very hard. So let's go another way;
-- We also define an alternate version of repeat via doubling and
-- taking a prefix. Doubled lists are always cute,
-- so we get that this version of repeat is cute for free.

-- Here's your granny's repeat:
repeat⁺ : X → ℕ⁺ → List⁺ X
repeat⁺ x (suc zero , _) = x ∷ []
repeat⁺ x (suc (suc n) , _) = x ∷⁺ (repeat⁺ x (suc n , record {nonZero = tt}))

-- And here's the powers-of-two flavoured version.

-- We need a slightly different version of take to make it go through
take⁺ : ℕ⁺ → List⁺ X → List⁺ X
take⁺ (suc zero , p) xs = xs
take⁺ (suc (suc n) , p) (x ∷ []) = x ∷ []
take⁺ (suc (suc n) , record {nonZero = _}) (x1 ∷ x2 ∷ xs) = x1 ∷⁺ (take⁺ (suc n , record {nonZero = _}) (x2 ∷ xs))

repeat⁺-alt : X → ℕ⁺ → List⁺ X
repeat⁺-alt x (suc zero , _) = x ∷ []
repeat⁺-alt x (suc (suc n) , record {nonZero = _}) = take⁺ (suc (suc n) , record {nonZero = _}) (double⁺ $ repeat⁺-alt x (suc n , record {nonZero = _}))

⁺++-identityʳ : (xs : List⁺ X) → xs ⁺++ [] ≡ xs
⁺++-identityʳ (x ∷ xs) rewrite ++-identityʳ xs = refl

-- take actually gives a prefix
take-is-prefix : ∀ n xs → Σ[ ys ∈ List X ] (take⁺ n xs ⁺++ ys ≡ xs)
take-is-prefix (suc zero , p) xs = [] , ⁺++-identityʳ xs
take-is-prefix (suc (suc n) , p) (x ∷ []) = [] , ⁺++-identityʳ (x ∷ [])
take-is-prefix (suc (suc n) , record {nonZero = tt}) (x1 ∷ x2 ∷ xs)
  = let (ys , p) = take-is-prefix (suc n , record {nonZero = tt}) (x2 ∷ xs)
    in ys , (cong (x1 ∷⁺_) p)

-- The two notions of repeat agree:
repeat-eq : ∀ x n → repeat⁺-alt x n ≡ repeat⁺ x n
repeat-eq = {!take!}

-- take always produces a prefix, and prefixes are always cute.
cute-take-gen : ∀ n xs → Cute xs → (ys : List X) → take⁺ n xs ⁺++ ys ≡ xs → Cute (take⁺ n xs)
cute-take-gen n xs cxs [] p = subst Cute (trans (sym p) (⁺++-identityʳ (take⁺ n xs))) cxs
cute-take-gen n xs (cute cxs) (y ∷ ys) p = proj₁ $ cxs (take⁺ n xs) (y ∷ ys) (sym p)

cute-take : ∀ n xs → Cute xs → Cute (take⁺ n xs)
cute-take n xs cxs = let (ys , p) = take-is-prefix n xs
                     in cute-take-gen n xs cxs ys p

-- Therefore the powers-of-two flavoured version of repeat is cute.
repeat-alt-cute : ∀ x n → Cute (repeat⁺-alt x n)
repeat-alt-cute = {!!}

-- And so the usual implementation of repeat is also cute.
repeat-cute : ∀ x n → Cute (repeat⁺ x n)
repeat-cute x n = subst Cute (repeat-eq x n) (repeat-alt-cute x n)

-}

--- ATTEMPT NUMBER 2: Our cute lists are all repetitions of the same element, so instead of lists, let's
--- do "cute" natural numbers

mutual
  data Powable (n : ℕ⁺) (x : X) : Set where
    powable : ((a b : ℕ⁺) → n ≡ a ⁺+⁺ b
               → Σ[ pa ∈ Powable a x ] Σ[ pb ∈ Powable b x ] ((pow pa) R (pow pb)))
            → Powable n x

  pow : {n : ℕ⁺} {x : X} → Powable n x → X
  pow {suc zero , p} {x} (powable f) = x
  pow {suc (suc n) , p} {x} (powable f) = let (c , d , r) = f (suc 0 , nonZero) (suc n , nonZero) refl
                                          in op (pow c) (pow d) r


pow-1 : ∀ x {p} → Powable (1 , p) x
pow-1 x = powable f where
  f : (a b : ℕ⁺) → (1 , record {nonZero = tt}) ≡ a ⁺+⁺ b
    → Σ[ pa ∈ Powable a x ] Σ[ pb ∈ Powable b x ] ((pow pa) R (pow pb))
  f (suc zero , p) (suc m , q) ()
  f (suc (suc n) , p) (suc m , q) ()

x¹≡x : ∀ x {z} (p : Powable (1 , z) x) → pow p ≡ x
x¹≡x x (powable _) = refl

-- For all n, x, pow {n} {x} is a constant function.
-- In other words, xⁿ is uniquely defined.
pow-unique : ∀ {n x} → (p q : Powable n x) → pow p ≡ pow q
pow-unique {suc zero , _} {x} (powable p) (powable q) = refl
pow-unique {suc (suc n) , _} {x} (powable p) (powable q)
  = let (a , b , r) = p (1 , nonZero) (suc n , nonZero) refl
        (c , d , s) = q (1 , nonZero) (suc n , nonZero) refl
    in cong-op (pow-unique a c) (pow-unique b d) r s

-- Oh hey, looks like we need an indices law. Neat.
pow-mult : ∀ x {n m} → (xⁿ⁺ᵐ : Powable (n ⁺+⁺ m) x) (xⁿ : Powable n x) (xᵐ : Powable m x) (r : pow xⁿ R pow xᵐ)
         → pow xⁿ⁺ᵐ ≡ op (pow xⁿ) (pow xᵐ) r
pow-mult x {(suc zero , record {nonZero = tt})} {(suc b , record {nonZero = tt})} (powable f) (powable p1) (powable g) r
  = cong-op (x¹≡x x (proj₁ (f (1 , nonZero) (suc b , nonZero) refl)))
            (pow-unique (proj₁ $ proj₂ $ f (1 , nonZero) (suc b , nonZero) refl) (powable g))
            (proj₂ (proj₂ (f (1 , nonZero) (suc b , nonZero) refl))) r
pow-mult x {(suc (suc n) , _)} {(suc m , _)} (powable xⁿ⁺ᵐ) (powable xⁿ) (powable xᵐ) r
  = trans (cong-op (pow-unique x1 x1')
                   (pow-mult x xnm xn xm (proj₁ p))
                   (proj₂ (proj₂ (xⁿ⁺ᵐ (1 , nonZero) (suc (n + suc m) , nonZero) refl)))
                   (proj₁ (proj₂ p)))
          (sym $ proj₂ $ proj₂ p) where

  x1 : Powable (1 , record { nonZero = tt }) x
  x1 = proj₁ (xⁿ⁺ᵐ (1 , nonZero) (suc (n + suc m) , nonZero) refl)

  xnm : Powable (suc n + suc m , record { nonZero = tt }) x
  xnm = proj₁ (proj₂ (xⁿ⁺ᵐ (1 , nonZero) (suc n + suc m , nonZero) refl))

  x1' : Powable (1 , record { nonZero = tt }) x
  x1' = proj₁ (xⁿ (1 , nonZero) (suc n , nonZero) refl)

  xn : Powable (suc n , record { nonZero = tt }) x
  xn = proj₁ (proj₂ (xⁿ (1 , nonZero) (suc n , nonZero) refl))

  xm : Powable (suc m , record { nonZero = tt }) x
  xm = powable xᵐ

  p : Σ[ xnRxm ∈ pow xn R pow xm ]
      Σ[ xRxnxm ∈ pow x1' R op (pow xn) (pow xm) xnRxm ]
        op (op (pow x1') (pow xn) (proj₂ (proj₂ (xⁿ (1 , nonZero) (suc n , nonZero) refl)))) (pow xm) r
      ≡ op (pow x1') (op (pow xn) (pow xm) xnRxm) xRxnxm
  p = assocʳ (proj₂ (proj₂ (xⁿ (1 , nonZero) (suc n , nonZero) refl))) r

pow-suc-lem : ∀ {n x} (p : Powable n x) (p+ : Powable (succ⁺ n) x) (r : x R pow p) → op x (pow p) r ≡ pow p+
pow-suc-lem {suc n , _} {x} (powable f) (powable g) r
  = cong-op (sym $ x¹≡x x (proj₁ (g (1 , nonZero) (suc n , nonZero) refl)))
            (pow-unique (powable f) (proj₁ (proj₂ (g (1 , record { nonZero = tt }) (suc n , record { nonZero = tt }) refl))))
            r
            (proj₂ (proj₂ (g (1 , nonZero) (suc n , nonZero) refl)))

pow-suc : ∀ x {n} → (xⁿ : Powable n x) → x R (pow xⁿ) → Powable (succ⁺ n) x
pow-suc x {u} (powable f) xRxˢⁿ⁺ˢᵐ = powable g where
  g : (a b : ℕ⁺) → succ⁺ u ≡ a ⁺+⁺ b
    → Σ[ pa ∈ Powable a x ] Σ[ pb ∈ Powable b x ] ((pow pa) R (pow pb))
  g (suc zero , record { nonZero = tt }) (suc m , record { nonZero = tt }) refl = pow-1 x , powable f , xRxˢⁿ⁺ˢᵐ
  g (suc (suc n) , record { nonZero = tt }) (suc m , record { nonZero = tt }) refl
    = let (xˢⁿ , xˢᵐ , xˢⁿRxˢᵐ) = f (suc⁺ n) (suc⁺ m) refl
          (xRxˢⁿ , xxˢⁿRxˢᵐ) = assocL1 xˢⁿRxˢᵐ (subst (x R_) (pow-mult x (powable f) xˢⁿ xˢᵐ xˢⁿRxˢᵐ ) xRxˢⁿ⁺ˢᵐ)
      in pow-suc x {suc n , _} xˢⁿ xRxˢⁿ , xˢᵐ , subst (_R pow xˢᵐ) (pow-suc-lem xˢⁿ (pow-suc x xˢⁿ xRxˢⁿ) xRxˢⁿ) xxˢⁿRxˢᵐ

pow-+ : ∀ x {n m} → (p : Powable n x) → (q : Powable m x) → pow p R pow q → Powable (n ⁺+⁺ m) x
pow-+ x {suc zero , _} {suc m , _} (powable f) q r = pow-suc x q r
pow-+ x {suc (suc n) , _} {suc m , _} (powable f) q r = powable g where
  g : (a b : ℕ⁺) → suc⁺ (suc n + suc m) ≡ a ⁺+⁺ b
    → Σ[ pa ∈ Powable a x ] Σ[ pb ∈ Powable b x ] ((pow pa) R (pow pb))
  g = {!!}

-- The trick : We define doubling as (n+n) rather than by induction, so that we can
-- deploy reflexivity to get our proof of xⁿRxⁿ for free.
pow-double : ∀ {x n} → Powable n x → Powable (n ⁺+⁺ n) x
pow-double {x} p = pow-+ x p p reflexive

-- So now to show that xⁿ is defined in general, we double and take a
-- powable prefix.
pow-all : ∀ x n → Powable n x
pow-all x (suc zero , _) = pow-1 x
pow-all x (suc (suc zero) , _) = pow-double (pow-1 x)
pow-all x (suc m@(suc (suc n)) , _) with pow-double (pow-all x (m , _))
... | powable f = proj₁ (f (suc m , _) (suc n , _) (lemma (suc n , _))) where
  -- 2n=(1+n)+(n-1).
  -- Since we force both args of + to be nonzero, this is only valid for n≥2.
  lemma : (n : ℕ⁺) → (succ⁺ n) ⁺+⁺ (succ⁺ n) ≡ (succ⁺ (succ⁺ n)) ⁺+⁺ n
  lemma n = ℕ⁺-cong (cong suc (+-suc (proj₁ n) (proj₁ n)))

power : ℕ → X → X
power zero x = ε
power (suc n) x = pow (pow-all x (suc n , nonZero))
