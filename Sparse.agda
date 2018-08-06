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
open import Data.List as List using (List; _∷_; []; foldr) public
open import Data.Product

Poly : Set
Poly = List (ℕ × Carrier)

module Arithmetic where

  infixl 6 _⊞_
  _⊞_ : Poly → Poly → Poly

  add-match : ∀ {i j} → ℕ.Ordering i j → Carrier → Poly → Carrier → Poly → Poly
  [] ⊞ ys = ys
  (x ∷ xs) ⊞ [] = x ∷ xs
  ((i , x) ∷ xs) ⊞ ((j , y) ∷ ys) = add-match (ℕ.compare i j) x xs y ys

  add-match (ℕ.less    i k) x [] y ys = (i , x) ∷ ((k , y) ∷ ys)
  add-match (ℕ.less    i k) x ((i′ , x′) ∷ xs) y ys = (i , x) ∷ add-match (ℕ.compare i′ k) x′ xs y ys
  add-match (ℕ.equal   i  ) x xs y ys = (i , x + y) ∷ (xs ⊞ ys)
  add-match (ℕ.greater j k) x xs y [] = (j , y) ∷ (k , x) ∷ xs
  add-match (ℕ.greater j k) x xs y ((j′ , y′) ∷ ys) = (j , y) ∷ add-match (ℕ.compare k j′) x xs y′ ys

--   -- Multiply a polynomial by a constant factor
--   infixl 7 _⨵_
--   _⨵_ : Carrier → Terms → Terms
--   x ⨵ ⟨⟩ = ⟨⟩
--   x ⨵ ⟨ i , y , ys ⟩ = ⟨ i , x * y , x ⨵ ys ⟩

--   infixl 7 _⊠_ _⊗]_
--   _⊠_ : Poly → Poly → Poly
--   _⊗]_ : Terms → Poly → Terms
--   (i , x , xs) ⊠ ys = i ℕ.+ o ys , x * c ys , (x ⨵ Δ ys ⊕ xs ⊗] ys)
--   ⟨⟩ ⊗] _ = ⟨⟩
--   ⟨ xs ⟩ ⊗] ys = ⟨ xs ⊠ ys ⟩

open Arithmetic using (_⊞_; add-match) public

----------------------------------------------------------------------
-- Evaluation
----------------------------------------------------------------------
-- We "run" the polynomial on some input with Horner's method.

infixr 8 _^_
_^_ : Carrier → ℕ → Carrier
x ^ zer = 1#
x ^ suc n = x ^ n * x

_↦_^*_ : Carrier → (ℕ × Carrier) → Carrier → Carrier
ρ ↦ (i , x) ^* xs = (x + xs * ρ) * ρ ^ i

⟦_⟧ : Poly → Carrier → Carrier
⟦ xs′ ⟧ ρ = List.foldr (ρ ↦_^*_) 0# xs′
