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

trunc-cons : Carrier → Terms → Terms
trunc-cons x ⟨ xs ⟩ = ⟨ x , ⟨ xs ⟩ ⟩
trunc-cons x ⟨⟩ with x ≟C 0#
trunc-cons x ⟨⟩ | yes p = ⟨⟩
trunc-cons x ⟨⟩ | no ¬p = ⟨ x , ⟨⟩ ⟩

trunc-cons-hom : ∀ z x xs ρ → ⟦ z , ⟨ x , xs ⟩ ⟧ ρ ≈ ⟦ z , trunc-cons x xs ⟧ ρ
trunc-cons-hom z x ⟨ xs ⟩ ρ = refl
trunc-cons-hom z x ⟨⟩ ρ with x ≟C 0#
trunc-cons-hom z x ⟨⟩ ρ | no ¬p = refl
trunc-cons-hom z x ⟨⟩ ρ | yes p =
  begin
    z + x * ρ
  ≈⟨ ⋯+⟨ ⟨ p ⟩*⋯ ⟩ ⟩
    z + 0# * ρ
  ≈⟨ ⋯+⟨ zeroˡ ρ ⟩ ⟩
    z + 0#
  ≈⟨ +-identityʳ z ⟩
    z
  ∎
