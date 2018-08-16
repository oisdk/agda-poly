{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Level using (_⊔_; Lift; lift; lower)
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.List as List using (_∷_; []; foldr; List)
open import Data.Vec as Vec using (_∷_; []; Vec)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product
open import Polynomials.Irrelevant.Product
open import Function

-- Multivariate polynomials.
module Polynomials.Multi
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open CommutativeSemiring commutativeSemiring hiding (zero)

----------------------------------------------------------------------
-- Definitions
----------------------------------------------------------------------

mutual
  -- A Polynomial is indexed by the number of variables it contains.
  Poly : ℕ → Set (a ⊔ ℓ)
  Poly zero = Lift ℓ Carrier
  Poly (suc n) = Coeffs n

  -- A list of coefficients, paired with the exponent *gap* from the
  -- preceding coefficient. In other words, to represent the
  -- polynomial:
  --
  --   3 + 2x² + 4x⁵ + 2x⁷
  --
  -- We write:
  --
  --   [(3,0),(2,1),(4,2),(2,1)]
  --
  -- Which can be thought of as a representation of the expression:
  --
  --   x⁰ * (3 + x * x¹ * (2 + x * x² * (4 + x * x¹ * (2 + x * 0))))
  --
  -- This is sparse Horner normal form.
  Coeffs : ℕ → Set (a ⊔ ℓ)
  Coeffs n = List (Coeff n × ℕ)

  -- We disallow zeroes in the coefficient list. This condition alone
  -- is enough to ensure a unique representation for any polynomial.
  Coeff : ℕ → Set (a ⊔ ℓ)
  Coeff i = Σ~[ x ∈ Poly i ] ¬ Zero i x

  Zero : ∀ n → Poly n → Set ℓ
  Zero zero (lift x) = x ≈ 0#
  Zero (suc n) [] = Lift ℓ ⊤
  Zero (suc n) (x ∷ xs) = Lift ℓ ⊥

----------------------------------------------------------------------
-- Construction
--
-- Because the polynomial is stored in a canonical form, we use a
-- normalising cons operator to construct the coefficient lists.
----------------------------------------------------------------------

-- Decision procedure for Zero
zero? : ∀ {n} → (p : Poly n) → Dec (Zero n p)
zero? {zero} (lift x) = x ≟C 0#
zero? {suc n} [] = yes (lift tt)
zero? {suc n} (x ∷ xs) = no lower

-- Polynomial exponentiation
infixr 8 _⍓_
_⍓_ : ∀ {n} → Coeffs n → ℕ → Coeffs n
[] ⍓ i = []
((x , j) ∷ xs) ⍓ i = (x , j ℕ.+ i) ∷ xs

-- Normalising cons
infixr 5 _∷↓_
_∷↓_ : ∀ {n} → (Poly n × ℕ) → Coeffs n → Coeffs n
(x , i) ∷↓ xs with zero? x
... | yes p = xs ⍓ suc i
... | no ¬p = (x ,~ ¬p , i) ∷ xs

----------------------------------------------------------------------
-- Arithmetic
----------------------------------------------------------------------

module Addition where
  -- The reason the following code is so verbose is termination
  -- checking. For instance, in the third case for ⊞-coeffs, we call a
  -- helper function. Instead, you could conceivably use a with-block
  -- (on ℕ.compare p q):
  --

  infixl 6 _⊞_
  _⊞_ : ∀ {n} → Poly n → Poly n → Poly n
  ⊞-coeffs : ∀ {n} → Coeffs n → Coeffs n → Coeffs n

  ⊞-ne : ∀ {p q n}
      → ℕ.Ordering p q
      → (x : Coeff n)
      → Coeffs n
      → (y : Coeff n)
      → Coeffs n
      → Coeffs n

  _⊞_ {zero} (lift x) (lift y) = lift (x + y)
  _⊞_ {suc n} xs ys = ⊞-coeffs xs ys

  ⊞-coeffs [] ys = ys
  ⊞-coeffs (x ∷ xs) [] = x ∷ xs
  ⊞-coeffs ((x , p) ∷ xs) ((y , q) ∷ ys) = ⊞-ne (ℕ.compare p q) x xs y ys

  ⊞-ne-l : ∀ {n} → ℕ → Coeffs n → (y : Coeff n) → Coeffs n → Coeffs n
  ⊞-ne-r : ∀ {n} → ℕ → (x : Coeff n) → Coeffs n → Coeffs n → Coeffs n

  ⊞-ne (ℕ.less    i k) x xs y ys = (x , i) ∷ ⊞-ne-l k xs y ys
  ⊞-ne (ℕ.greater j k) x xs y ys = (y , j) ∷ ⊞-ne-r k x xs ys
  ⊞-ne (ℕ.equal   i  ) x xs y ys = (fst~ x ⊞ fst~ y , i) ∷↓ (⊞-coeffs xs ys)

  ⊞-ne-l k [] y ys = (y , k) ∷ ys
  ⊞-ne-l k ((x , i) ∷ xs) y ys = ⊞-ne (ℕ.compare i k) x xs y ys

  ⊞-ne-r k x xs [] = (x , k) ∷ xs
  ⊞-ne-r k x xs ((y , j) ∷ ys) = ⊞-ne (ℕ.compare k j) x xs y ys

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
--   (fst~ x ⊠ fst~ y , i ℕ.+ j) ∷↓ (fst~ x ⋊ ys ⊞ ⊠-coeffs xs ((y , 0) ∷ ys))

-- x ⋊ ((y , j) ∷ ys) = (x ⊠ fst~ y , j) ∷↓ x ⋊ ys
-- x ⋊ [] = []

-- infixr 8 _^_
-- _^_ : Carrier → ℕ → Carrier
-- x ^ zero = 1#
-- x ^ suc n = x * x ^ n
-- ⟦_⟧ : ∀ {n} → Poly n → Vec Carrier n → Carrier
-- ⟦_⟧ {zero} (lift x) [] = x
-- ⟦_⟧ {suc n} x (y ∷ ρ) = List.foldr coeff-eval 0# x
--   where
--   coeff-eval : Coeff n × ℕ → Carrier → Carrier
--   coeff-eval (c ,~ _ , p) xs = (⟦ c ⟧ ρ + xs * y) * y ^ p

-- κ : ∀ {n} → Carrier → Poly n
-- κ {zero} x = lift x
-- κ {suc n} x = (κ x , 0) ∷↓ []

-- open import Data.Fin as Fin using (Fin)

-- ι : ∀ {n} → Fin n → Poly n
-- ι Fin.zero = (κ 1# , 1) ∷↓ []
-- ι (Fin.suc x) = (ι x , 0) ∷↓ []
