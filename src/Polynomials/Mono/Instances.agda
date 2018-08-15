open import Algebra using (CommutativeSemiring)
open import Relation.Binary

module Polynomials.Mono.Instances
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open import Level using (_⊔_)
open import Polynomials.Mono commutativeSemiring _≟C_
open import Polynomials.Mono.Equality commutativeSemiring _≟C_

mono-setoid : Setoid (a ⊔ ℓ) ℓ
mono-setoid = record
  { Carrier = Poly
  ; _≈_ = _≋_
  ; isEquivalence = ≋-isEquivalence
  }

open import Algebra.FunctionProperties _≋_
open import Data.List as List using ([]; _∷_)

+-cong : Congruent₂ _⊞_
+-cong []≋ yp = yp
+-cong (xp ∷≋ xps) []≋ = xp ∷≋ xps
+-cong (_∷≋_ {n = i} xp xps) (_∷≋_ {n = j} yp yps) = {!!}
