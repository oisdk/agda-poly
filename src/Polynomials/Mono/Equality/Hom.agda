open import Algebra using (CommutativeSemiring)
open import Relation.Binary

module Polynomials.Mono.Equality.Hom
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open import Polynomials.Mono commutativeSemiring _≟C_
open CommutativeSemiring commutativeSemiring
open import Level using (_⊔_)
open import Data.List as List using (List; []; _∷_)
open import Relation.Nullary

_≋_ : Poly → Poly → Set (a ⊔ ℓ)
xs ≋ ys = ∀ ρ → ⟦ xs ⟧ ρ ≈ ⟦ ys ⟧ ρ

≋-refl : Reflexive _≋_
≋-refl ρ = refl

≋-sym : Symmetric _≋_
≋-sym x ρ = sym (x ρ)

≋-trans : Transitive _≋_
≋-trans x y ρ = trans (x ρ) (y ρ)


-- Can't do this because of the no case. (I think)
_≟_ : Decidable _≋_
[] ≟ [] = yes λ ρ → refl
[] ≟ (x ∷ ys) = no {!!}
(x ∷ xs) ≟ [] = no {!!}
(x ∷ xs) ≟ (y ∷ ys) = {!!}
