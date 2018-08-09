{-# OPTIONS --without-K --exact-split #-}

-- Polynomials in Horner normal form. The representation here is
-- dense, which is quite inefficient. In particular, something like
-- 1 + x⁴ would be represented as:
--
--     1 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ []
--
-- The zeroes in the middle could conceivably be collapsed.

open import Algebra using (CommutativeSemiring)

module Polynomials.Monomial.Dense
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  where

open CommutativeSemiring commutativeSemiring

----------------------------------------------------------------------
-- Definitions
----------------------------------------------------------------------
open import Data.List as List using ([]; _∷_; foldr)

-- A polynomial is a coefficient with an optional addition of terms
-- to a higher power. For instance, the term
--
--    1 + 2x + 5x^2
--
-- could be represented as:
--
--    1 ∷ 2 ∷ 5 ∷ []
Poly : Set a
Poly = List.List Carrier


-- Square points towards poly; circle towards terms. The multiple
-- definitions provide maximum information to the caller: for
-- instance, if the right argument to ⊕ isn't ⟨⟩, the result is
-- immediately wrapped in ⟨_⟩, without examining the left argument.
infixl 6 _⊞_
_⊞_ : Poly → Poly → Poly
[] ⊞ ys = ys
(x ∷ xs) ⊞ [] = x ∷ xs
(x ∷ xs) ⊞ (y ∷ ys) = x + y ∷ xs ⊞ ys

-- Multiply two polynomials. This function is careful to not add
-- any trailing zeroes.
infixl 7 _⊠_ _⋊_
_⋊_ : Carrier → Poly → Poly
_⋊_ x = List.map (x *_)

_⊠_ : Poly → Poly → Poly
[] ⊠ _ = []
(x ∷ xs) ⊠ [] = []
(x ∷ xs) ⊠ (y ∷ ys) = x * y ∷ x ⋊ ys ⊞ xs ⊠ (y ∷ ys)

----------------------------------------------------------------------
-- Evaluation
----------------------------------------------------------------------
-- We "run" the polynomial on some input with Horner's method.
⟦_⟧ : Poly → Carrier → Carrier
⟦ xs ⟧ ρ = foldr (λ x xs → x + xs * ρ) 0# xs
