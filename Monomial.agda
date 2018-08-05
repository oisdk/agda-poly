{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
import Level
open import Data.Product
open import Function
open import Relation.Binary

{-
Monomial representations of polynomials. They're stored
least-significant-figure-first, to make for efficient arithmetic.
-}

module Monomial
  (commutativeSemiring : CommutativeSemiring Level.zero Level.zero)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open CommutativeSemiring commutativeSemiring

----------------------------------------------------------------------
-- Definitions
----------------------------------------------------------------------
open import Data.Maybe

Terms : Set
-- A polynomial is a coefficient with an optional addition of terms
-- to a higher power. For instance, the term
--
--    1 + 2x + 5x^2
--
-- could be represented as:
--
--    1 , ⟨ 2 , ⟨ 5 , ⟨⟩ ⟩ ⟩
record Poly : Set where
  constructor _,_
  inductive
  field
    c : Carrier
    Δ : Terms
open Poly public

Terms = Maybe Poly
pattern ⟨⟩ = nothing
pattern ⟨_⟩ x = just x

----------------------------------------------------------------------
-- Arithmetic
----------------------------------------------------------------------

-- Square points towards poly; circle towards terms. The multiple
-- definitions provide maximum information to the caller: for
-- instance, if the right argument to ⊕ isn't ⟨⟩, the result is
-- immediately wrapped in ⟨_⟩, without examining the left argument.
infixl 6 _⊞_ _⊕_ _⊕]_
_⊞_ : Poly → Poly → Poly
_⊕_ : Terms → Terms → Terms
_⊕]_ : Terms → Poly → Poly
(x , xs) ⊞ (y , ys) = x + y , (xs ⊕ ys)
xs ⊕ ⟨⟩ = xs
xs ⊕ ⟨ ys ⟩ = ⟨ xs ⊕] ys ⟩
⟨⟩ ⊕] ys = ys
⟨ xs ⟩ ⊕] ys = xs ⊞ ys

-- Multiply a polynomial by a constant factor
infixl 7 _⨵_
_⨵_ : Carrier → Terms → Terms
x ⨵ ⟨⟩ = ⟨⟩
x ⨵ ⟨ y , ys ⟩ = ⟨ x * y , x ⨵ ys ⟩

-- Multiply two polynomials. This function is careful to not add
-- any trailing zeroes.
infixl 7 _⊠_
_⊠_ : Poly → Poly → Poly
_⊗]_ : Terms → Poly → Terms
(x , xs) ⊠ ys = x * c ys , (x ⨵ Δ ys ⊕ xs ⊗] ys)
⟨⟩ ⊗] _ = ⟨⟩
⟨ xs ⟩ ⊗] ys = ⟨ xs ⊠ ys ⟩

----------------------------------------------------------------------
-- Evaluation
----------------------------------------------------------------------
-- We "run" the polynomial on some input with Horner's method.
⟦_⟧ : Poly → Carrier → Carrier
⟦ x , ⟨⟩ ⟧ ρ = x
⟦ x , ⟨ xs ⟩ ⟧ ρ = x + ⟦ xs ⟧ ρ * ρ
