{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
import Level
open import Data.Product
open import Function
open import Relation.Binary

module Monomial.Instances
  (commutativeSemiring : CommutativeSemiring Level.zero Level.zero)
  where

open import Monomial commutativeSemiring
open import Monomial.Equality commutativeSemiring
open Propositional

open CommutativeSemiring commutativeSemiring using (refl)

open import Algebra.Structures _≈P_
open Poly

-- poly-IsCommutativeSemiring : IsCommutativeSemiring _⊞_ _⊠_ (0# , ⟨⟩) (1# , ⟨⟩)
-- poly-IsCommutativeSemiring = {!!}
