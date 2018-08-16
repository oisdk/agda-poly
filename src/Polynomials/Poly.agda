{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Level using (_⊔_; Lift; lift; lower)
open import Data.Empty
open import Data.Unit using (⊤; tt)

module Polynomials.Poly
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open CommutativeSemiring commutativeSemiring hiding (zero)

open import Data.List as List using (_∷_; []; foldr; List)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product

-- Either a constant carrier
record Coeff (i : ℕ) : Set (a ⊔ ℓ)

Coeffs : ℕ → Set (a ⊔ ℓ)
Coeffs n = List (Coeff n × ℕ)

Poly : ℕ → Set (a ⊔ ℓ)
Poly zero = Lift ℓ Carrier
Poly (suc n) = Coeffs n

Zero : ∀ n → Poly n → Set ℓ
Zero zero (lift x) = x ≈ 0#
Zero (suc n) [] = Lift ℓ ⊤
Zero (suc n) (x ∷ xs) = Lift ℓ ⊥

zero? : ∀ {n} → (p : Poly n) → Dec (Zero n p)
zero? {zero} (lift x) = x ≟C 0#
zero? {suc n} [] = yes (lift tt)
zero? {suc n} (x ∷ xs) = no lower

NonConst : ∀ n → Poly n → Set
NonConst zero _ = ⊤
NonConst (suc _) [] = ⊤
NonConst (suc _) ((_ , zero) ∷ []) = ⊥
NonConst (suc _) ((_ , zero) ∷ _ ∷ _) = ⊤
NonConst (suc _) ((_ , suc _) ∷ _) = ⊤

record Coeff i where
  constructor coeff-nz
  inductive
  field
    inj   : ℕ
    coeff : Poly inj
    .coeff≠0 : ¬ Zero inj coeff
    .coeff≠κ : NonConst inj coeff
    inj≤i : inj ℕ.≤′ i
open Coeff

infixr 8 _^_
_^_ : Carrier → ℕ → Carrier
x ^ zero = 1#
x ^ suc n = x * x ^ n


infixr 8 _⍓_
_⍓_ : ∀ {n} → Coeffs n → ℕ → Coeffs n
[] ⍓ i = []
((x , j) ∷ xs) ⍓ i = (x , j ℕ.+ i) ∷ xs

≤′-trans : ∀ {x y z} → x ℕ.≤′ y → y ℕ.≤′ z → x ℕ.≤′ z
≤′-trans xy ℕ.≤′-refl = xy
≤′-trans xy (ℕ.≤′-step yz) = ℕ.≤′-step (≤′-trans xy yz)

coeff↓ : ∀ {n m} → (p : Poly n) → n ℕ.≤′ m → .(¬ Zero n p) → Coeff m
coeff↓ {zero} p n≤m p≠0 = coeff-nz zero p p≠0 tt n≤m
coeff↓ {suc n} [] n≤m p≠0 = coeff-nz (suc n) [] p≠0 tt n≤m
coeff↓ {suc n} ((coeff-nz i x x≠0 x≠κ i≤m , zero) ∷ []) n≤m p≠0 = coeff-nz i x (λ z → p≠0 (lift (x≠0 z))) x≠κ (≤′-trans (ℕ.≤′-step i≤m) n≤m)
coeff↓ {suc n} ((x₁ , zero) ∷ x₂ ∷ xs) n≤m p≠0 = coeff-nz (suc n) ((x₁ , zero) ∷ x₂ ∷ xs) p≠0 tt n≤m
coeff↓ {suc n} ((x , suc i) ∷ xs) n≤m p≠0 = coeff-nz (suc n) ((x , suc i) ∷ xs) p≠0 tt n≤m

infixr 5 _∷↓_
_∷↓_ : ∀ {n m} → (Poly n × n ℕ.≤′ m × ℕ) → Coeffs m → Coeffs m
_∷↓_ (x , n≤m , i) xs with zero? x
... | yes p = xs ⍓ suc i
... | no ¬p = (coeff↓ x n≤m ¬p , i) ∷ xs

open import Data.Vec as Vec using (Vec; _∷_; [])

⟦_⟧ : ∀ {n} → Poly n → Vec Carrier n → Carrier
⟦_⟧ {zero} (lift x) [] = x
⟦_⟧ {suc n} x (y ∷ ρ) = List.foldr coeff-eval 0# x
  where
  ⟦_⟧-vec : ∀ {n} → Poly n → ∀ {m} → n ℕ.≤′ m → Vec Carrier m → Carrier
  ⟦ c ⟧-vec ℕ.≤′-refl ρ = ⟦ c ⟧ ρ
  ⟦ c ⟧-vec (ℕ.≤′-step n≤m) (x ∷ ρ) = ⟦ c ⟧-vec n≤m ρ

  coeff-eval : Coeff n × ℕ → Carrier → Carrier
  coeff-eval (coeff-nz i c _ _ i≤n , p) xs = (⟦ c ⟧-vec i≤n ρ + xs * y) * y ^ p

-- infixl 6 _⊞_
-- _⊞_ : ∀ {n} → Poly n → Poly n → Poly n
-- ⊞-coeffs : ∀ {n} → Coeffs n → Coeffs n → Coeffs n

-- ⊞-ne : ∀ {p q n}
--      → ℕ.Ordering p q
--      → (x : Coeff n)
--      → Coeffs n
--      → (y : Coeff n)
--      → Coeffs n
--      → Coeffs n

-- _⊞_ {zero} (lift x) (lift y) = lift (x + y)
-- _⊞_ {suc n} xs ys = ⊞-coeffs xs ys

-- ⊞-coeffs [] ys = ys
-- ⊞-coeffs (x ∷ xs) [] = x ∷ xs
-- ⊞-coeffs ((x , p) ∷ xs) ((y , q) ∷ ys) = ⊞-ne (ℕ.compare p q) x xs y ys

-- ⊞-ne-l : ∀ {n} → ℕ → Coeffs n → (y : Coeff n) → Coeffs n → Coeffs n
-- ⊞-ne-r : ∀ {n} → ℕ → (x : Coeff n) → Coeffs n → Coeffs n → Coeffs n

-- ⊞-ne (ℕ.less    i k) x xs y ys = (x , i) ∷ ⊞-ne-l k xs y ys
-- ⊞-ne (ℕ.greater j k) x xs y ys = (y , j) ∷ ⊞-ne-r k x xs ys
-- ⊞-ne (ℕ.equal   i  ) x xs y ys = (coeff x ⊞ coeff y , i) ∷↓ (⊞-coeffs xs ys)

-- ⊞-ne-l k [] y ys = (y , k) ∷ ys
-- ⊞-ne-l k ((x , i) ∷ xs) y ys = ⊞-ne (ℕ.compare i k) x xs y ys

-- ⊞-ne-r k x xs [] = (x , k) ∷ xs
-- ⊞-ne-r k x xs ((y , j) ∷ ys) = ⊞-ne (ℕ.compare k j) x xs y ys

-- infixl 7 _⋊_
-- infixl 7 _⊠_
-- _⊠_ : ∀ {n} → Poly n → Poly n → Poly n
-- ⊠-coeffs : ∀ {n} → Coeffs n → Coeffs n → Coeffs n

-- _⋊_ : ∀ {n} → Poly n → Coeffs n → Coeffs n

-- _⊠_ {zero} (lift x) (lift y) = lift (x * y)
-- _⊠_ {suc n} xs ys = ⊠-coeffs xs ys

-- ⊠-coeffs [] ys = []
-- ⊠-coeffs (x ∷ xs) [] = []
-- ⊠-coeffs ((x , i) ∷ xs) ((y , j) ∷ ys) =
--   (coeff x ⊠ coeff y , i ℕ.+ j) ∷↓ (coeff x ⋊ ys ⊞ ⊠-coeffs xs ((y , 0) ∷ ys))

-- x ⋊ ((y , j) ∷ ys) = (x ⊠ coeff y , j) ∷↓ x ⋊ ys
-- x ⋊ [] = []


-- κ : ∀ {n} → Carrier → Poly n
-- κ {zero} x = lift x
-- κ {suc n} x = (κ x , 0) ∷↓ []

-- open import Data.Fin as Fin using (Fin)

-- ι : ∀ {n} → Fin n → Poly n
-- ι Fin.zero = (κ 1# , 1) ∷↓ []
-- ι (Fin.suc x) = (ι x , 0) ∷↓ []
