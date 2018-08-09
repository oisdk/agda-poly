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

mono-setoid : Setoid a ℓ
mono-setoid = record
  { Carrier = Poly
  ; _≈_ = _≋_
  ; isEquivalence = ≋-equivalence
  }

open import Polynomials.SemiringReasoning mono-setoid _⊞_ _⊠_ {!!} {!!}

+-comm : ∀ xs ys → xs ⊞ ys ≋ ys ⊞ xs
+-comm [] [] = []≋
+-comm [] (x ∷ ys) = {!!}
+-comm (x ∷ xs) ys = {!!}
