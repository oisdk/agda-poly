open import Algebra using (CommutativeSemiring)
import Level
open import Data.Product
open import Function
open import Relation.Binary

module Monomial.Redundancy
  (commutativeSemiring : CommutativeSemiring Level.zero Level.zero)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open CommutativeSemiring commutativeSemiring
open import Monomial commutativeSemiring _≟C_
open import SemiringReasoning commutativeSemiring
open import Relation.Nullary

data NoTrailingZeroes : Poly → Set where
  Here : ∀ x → ¬ (x ≈ 0#) → NoTrailingZeroes (x , ⟨⟩)
  There : ∀ x xs → NoTrailingZeroes xs → NoTrailingZeroes (x , ⟨ xs ⟩)

⊞-unique : ∀ {xs ys} → NoTrailingZeroes xs  → NoTrailingZeroes ys → NoTrailingZeroes (xs ⊞ ys)
⊞-unique (Here x xs) (Here y ys) = Here (x + y) {!!}
⊞-unique (Here x x₁) (There x₂ xs ys) = {!!}
⊞-unique (There x xs xs₁) ys = {!!}
