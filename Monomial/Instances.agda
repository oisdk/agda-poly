{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
import Level
open import Data.Product
open import Function
open import Relation.Binary

module Monomial.Instances
  (commutativeSemiring : CommutativeSemiring Level.zero Level.zero)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open import Monomial commutativeSemiring
open import Monomial.Equality commutativeSemiring _≟C_
open CommutativeSemiring commutativeSemiring

open import Algebra.Structures _≈P_



-- poly-IsCommutativeSemiring : IsCommutativeSemiring _⊞_ _⊠_ (0# , ⟨⟩) (1# , ⟨⟩)
-- poly-IsCommutativeSemiring = {!!}
