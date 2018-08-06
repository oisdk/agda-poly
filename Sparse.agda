{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
import Level
open import Function
open import Relation.Binary

module Sparse
  (commutativeSemiring : CommutativeSemiring Level.zero Level.zero)
  where

open CommutativeSemiring commutativeSemiring

open import Data.Maybe
open import Data.Nat as ℕ using (suc; ℕ) renaming (zero to zer)

Terms : Set
infixr 5 _,_,_
record Poly : Set where
  constructor _,_,_
  inductive
  field
    o : ℕ
    c : Carrier
    Δ : Terms
open Poly public

Terms = Maybe Poly
pattern ⟨⟩ = nothing
pattern ⟨_⟩ x = just x


module Arithmetic where
  pow-suc : Poly → Poly
  pow-suc (i , x , xs) = (suc i , x , xs)
  -- Square points towards poly; circle towards terms. The multiple
  -- definitions provide maximum information to the caller: for
  -- instance, if the right argument to ⊕ isn't ⟨⟩, the result is
  -- immediately wrapped in ⟨_⟩, without examining the left argument.
  infixl 6 _⊞_ _⊕_ _⊕]_ _[⊕_
  _⊞_ : Poly → Poly → Poly
  _⊕_ : Terms → Terms → Terms
  _⊕]_ : Terms → Poly → Poly
  _[⊕_ : Poly → Terms → Poly

  (zer , x , xs) ⊞ (zer , y , ys) = (zer , x + y , xs ⊕ ys)
  (zer , x , xs) ⊞ (suc j , y , ys) = (zer , x , ⟨ xs ⊕] (j , y , ys) ⟩)
  (suc i , x , xs) ⊞ (zer , y , ys) = (zer , y , ⟨ (i , x , xs) [⊕ ys ⟩)
  (suc i , x , xs) ⊞ (suc j , y , ys) = pow-suc ((i , x , xs) ⊞ (j , y , ys))
  xs ⊕ ⟨⟩ = xs
  xs ⊕ ⟨ ys ⟩ = ⟨ xs ⊕] ys ⟩
  ⟨⟩ ⊕] ys = ys
  ⟨ xs ⟩ ⊕] ys = xs ⊞ ys
  xs [⊕ ⟨⟩ = xs
  xs [⊕ ⟨ ys ⟩ = xs ⊞ ys

  -- Multiply a polynomial by a constant factor
  infixl 7 _⨵_
  _⨵_ : Carrier → Terms → Terms
  x ⨵ ⟨⟩ = ⟨⟩
  x ⨵ ⟨ i , y , ys ⟩ = ⟨ i , x * y , x ⨵ ys ⟩

  infixl 7 _⊠_ _⊗]_
  _⊠_ : Poly → Poly → Poly
  _⊗]_ : Terms → Poly → Terms
  (i , x , xs) ⊠ ys = i ℕ.+ o ys , x * c ys , (x ⨵ Δ ys ⊕ xs ⊗] ys)
  ⟨⟩ ⊗] _ = ⟨⟩
  ⟨ xs ⟩ ⊗] ys = ⟨ xs ⊠ ys ⟩

open Arithmetic using (_⊞_; _⊠_; _⨵_) public

----------------------------------------------------------------------
-- Evaluation
----------------------------------------------------------------------
-- We "run" the polynomial on some input with Horner's method.

infixr 8 _^_
_^_ : Carrier → ℕ → Carrier
x ^ zer = 1#
x ^ suc n = x ^ n * x

⟪_⟫ : Terms → Carrier → Carrier
⟦_⟧ : Poly → Carrier → Carrier
⟪ ⟨⟩ ⟫ _ = 0#
⟪ ⟨ xs ⟩ ⟫ ρ = ⟦ xs ⟧ ρ
⟦ i , x , xs ⟧ ρ = (x + ⟪ xs ⟫ ρ * ρ) * ρ ^ i
