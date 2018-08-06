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

open CommutativeSemiring commutativeSemiring

-- open import Algebra.Structures _≈P_
-- open Poly

-- ⊞-comm : ∀ xs ys → xs ⊞ ys ≈P ys ⊞ xs
-- ⊞-comm (x , ⟨⟩)     (y , ⟨⟩)     = +-comm x y , ⟨⟩-≈
-- ⊞-comm (x , ⟨⟩)     (y , ⟨ ys ⟩) = +-comm x y , {!!}
-- ⊞-comm (x , ⟨ xs ⟩) (y , ⟨⟩)     = +-comm x y , {!!}
-- ⊞-comm (x , ⟨ xs ⟩) (y , ⟨ ys ⟩) = +-comm x y , ⟨ ⊞-comm xs ys ⟩-≈

-- poly-CommutativeSemiring : CommutativeSemiring Level.zero Level.zero
-- poly-CommutativeSemiring = record
--   { Carrier = Poly
--   ; _≈_ = _≈P_
--   ; _+_ = _⊞_
--   ; _*_ = _⊠_
--   ; 0# = 0# , ⟨⟩
--   ; 1# = 1# , ⟨⟩
--   ; isCommutativeSemiring = record
--     { +-isCommutativeMonoid = {!!}
--     ; *-isCommutativeMonoid = {!!} }
--   }
--   where postulate trustMe : _
