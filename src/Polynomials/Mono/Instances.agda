open import Algebra using (CommutativeSemiring)
open import Relation.Binary

module Polynomials.Mono.Instances
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open import Polynomials.Mono commutativeSemiring _≟C_
open import Polynomials.Mono.Equality commutativeSemiring _≟C_
open import Polynomials.Mono.Homomorphism commutativeSemiring _≟C_
open import Data.List using ([]; _∷_)
open import Relation.Binary
open import Level using (_⊔_)

mono-setoid : Setoid (a ⊔ ℓ) ℓ
mono-setoid = record
  { Carrier = Poly
  ; _≈_ = _≋_
  ; isEquivalence = ≋-isEquivalence
  }
