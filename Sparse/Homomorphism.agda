{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
import Level
open import Function
open import Relation.Binary

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Sparse.Homomorphism
  (commutativeSemiring : CommutativeSemiring Level.zero Level.zero)
  where

open CommutativeSemiring commutativeSemiring hiding (zero)
open import Sparse commutativeSemiring
open import SemiringReasoning commutativeSemiring
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product


-- +-hom : ∀ xs ys ρ → ⟦ xs ⟧ ρ + ⟦ ys ⟧ ρ ≈ ⟦ xs ⊞ ys ⟧ ρ
-- +-hom [] ys ρ = +-identityˡ (⟦ ys ⟧ ρ)
-- +-hom (x ∷ xs) [] ρ = +-identityʳ (⟦ x ∷ xs ⟧ ρ)
-- +-hom ((i , x) ∷ xs) ((j , y) ∷ ys) ρ with ℕ.compare i j
-- +-hom ((i , x) ∷ xs) ((.(suc (i ℕ.+ k)) , y) ∷ ys) ρ | ℕ.less    .i k = {!!}
-- +-hom ((.(suc (j ℕ.+ k)) , x) ∷ xs) ((j , y) ∷ ys) ρ | ℕ.greater .j k = {!!}
-- +-hom ((i , x) ∷ xs) ((.i , y) ∷ ys) ρ               | ℕ.equal   .i   =
--   begin
--     ⟦ (i , x) ∷ xs ⟧ ρ + ⟦ (i , y) ∷ ys ⟧ ρ
--   ≡⟨⟩
--     ρ ↦ (i , x) ^* ⟦ xs ⟧ ρ + ρ ↦ (i , y) ^* ⟦ ys ⟧ ρ
--   ≡⟨⟩
--     (x + ⟦ xs ⟧ ρ * ρ) * ρ ^ i + (y + ⟦ ys ⟧ ρ * ρ) * ρ ^ i
--   ≈⟨ sym (distribʳ (ρ ^ i) _ _) ⟩
--     ((x + ⟦ xs ⟧ ρ * ρ) + (y + ⟦ ys ⟧ ρ * ρ)) * ρ ^ i
--   ≅⟨ ⟨_⟩*⋯ ⟩
--     ((x + ⟦ xs ⟧ ρ * ρ) + (y + ⟦ ys ⟧ ρ * ρ))
--   ≈⟨ sym (+-assoc _ _ _) ⟩
--   ((x + ⟦ xs ⟧ ρ * ρ) + y) + ⟦ ys ⟧ ρ * ρ
--   ≈⟨ ⟨ +-assoc x _ y ︔ ⋯+⟨ +-comm _ y ⟩ ︔ sym (+-assoc x y _) ⟩+⋯ ⟩
--   ((x + y) + ⟦ xs ⟧ ρ * ρ) + ⟦ ys ⟧ ρ * ρ
--   ≈⟨ +-assoc (x + y) _ _ ⟩
--   (x + y) + (⟦ xs ⟧ ρ * ρ + ⟦ ys ⟧ ρ * ρ)
--   ≈⟨ sym ⋯+⟨ distribʳ ρ _ _ ⟩ ⟩
--   (x + y) + (⟦ xs ⟧ ρ + ⟦ ys ⟧ ρ) * ρ
--   ≈⟨ ⋯+⟨ ⟨ +-hom xs ys ρ ⟩*⋯ ⟩ ⟩
--     (x + y) + ⟦ xs ⊞ ys ⟧ ρ * ρ
--   ∎
