{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
open import Relation.Binary

module Polynomials.Mono.Truncated
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open import Polynomials.Mono commutativeSemiring _≟C_
open import Data.List as List using ([]; _∷_; foldr)
open import Relation.Binary.PropositionalEquality using (_≡_)

record Poly↓ : Set a where
  field
    ⟦_⟧↑ : Poly
    .{↕} : ⟦_⟧↑ ≡ foldr _∷↓_ [] ⟦_⟧↑


-- Define operators, instances on this type
