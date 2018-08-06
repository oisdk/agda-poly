{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
import Level
open import Data.Product
open import Function
open import Relation.Binary

----------------------------------------------------------------------
-- Truncation
----------------------------------------------------------------------
module Monomial.Truncation
  (commutativeSemiring : CommutativeSemiring Level.zero Level.zero)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open CommutativeSemiring commutativeSemiring
open import Monomial commutativeSemiring
open import SemiringReasoning commutativeSemiring
open import Relation.Nullary

trunc-cons : Carrier → Poly → Poly
trunc-cons x (y ∷ ys) = x ∷ y ∷ ys
trunc-cons x [] with x ≟C 0#
trunc-cons x [] | yes p = []
trunc-cons x [] | no ¬p = x ∷ []

trunc-cons-hom : ∀ x xs ρ → ⟦ x ∷ xs ⟧ ρ ≈ ⟦ trunc-cons x xs ⟧ ρ
trunc-cons-hom x (y ∷ ys) ρ = refl
trunc-cons-hom x [] ρ with x ≟C 0#
trunc-cons-hom x [] ρ | no ¬p = refl
trunc-cons-hom x [] ρ | yes p =
  begin
    x + 0# * ρ
  ≈⟨ +-cong p (zeroˡ ρ) ⟩
    0# + 0#
  ≈⟨ +-identityˡ 0# ⟩
    0#
  ∎

trunc : Poly → Poly
trunc = foldr trunc-cons []

trunc-hom : ∀ xs ρ → ⟦ xs ⟧ ρ ≈ ⟦ trunc xs ⟧ ρ
trunc-hom [] ρ = refl
trunc-hom (x ∷ xs) ρ =
  begin
    ⟦ x ∷ xs ⟧ ρ
  ≈⟨ ⋯+⟨ ⟨ trunc-hom xs ρ ⟩*⋯ ⟩ ⟩
    ⟦ x ∷ trunc xs ⟧ ρ
  ≈⟨ trunc-cons-hom x (trunc xs) ρ ⟩
    ⟦ trunc-cons x (trunc xs) ⟧ ρ
  ∎
