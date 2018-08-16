module Polynomials.Multi.Examples where

open import Data.Nat.Properties using (commutativeSemiring)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Polynomials.Multi.Expr commutativeSemiring ℕ._≟_
open import Algebra using (CommutativeSemiring)
open CommutativeSemiring commutativeSemiring
open import Relation.Binary.PropositionalEquality using (_≡_)

lem5 : (x y z : ℕ) → z + (x + y) ≡ x + 0 + 0 + z + 0 + y
lem5 = solve 3
  (λ x y z → z ⊕ (x ⊕ y) ⊜ x ⊕ Κ 0 ⊕ Κ 0 ⊕ z ⊕ Κ 0 ⊕ y) refl
