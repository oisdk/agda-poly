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
open Arithmetic using (_⊕]_)
open import SemiringReasoning commutativeSemiring
open import Data.Nat as ℕ using (ℕ; suc; zero)


+-hom : ∀ xs ys ρ → ⟦ xs ⟧ ρ + ⟦ ys ⟧ ρ ≈ ⟦ xs ⊞ ys ⟧ ρ
+-hom (zero , x , xs) (zero , y , ys) ρ = {!!}
+-hom (zero , x , xs) (suc j , y , ys) ρ =
  begin
    ⟦ 0  , x , xs ⟧ ρ + ⟦ suc j , y , ys ⟧ ρ
  ≈⟨ {!!} ⟩
    x + ⟦ xs ⊕] (j , y , ys) ⟧ ρ * ρ
  ≈⟨ sym (*-identityʳ _) ⟩
    (x + ⟦ xs ⊕] (j , y , ys) ⟧ ρ * ρ) * 1#
  ∎
+-hom (suc i , x , xs) (zero , y , ys) ρ = {!!}
+-hom (suc i , x , xs) (suc j , y , ys) ρ = {!!}
