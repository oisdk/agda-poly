open import Algebra using (CommutativeSemiring)
open import Relation.Binary

module Polynomials.Monomial.Sparse.Truncation
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open CommutativeSemiring commutativeSemiring

open import Polynomials.Monomial.Sparse commutativeSemiring
open import Data.Product
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.List as List using ([]; _∷_)
open import Relation.Nullary

pow : ℕ → Poly → Poly
pow i [] = []
pow i ((j , x) ∷ xs) = (suc i ℕ.+ j , x) ∷ xs

infixr 5 _∷↓_
_∷↓_ : (ℕ × Carrier) → Poly → Poly
_∷↓_ (i , x) with x ≟C 0#
... | yes p = pow i
... | no ¬p = _∷_ (i , x)

open import Polynomials.SemiringReasoning commutativeSemiring
open import Function
open import Polynomials.Monomial.Sparse.Homomorphism commutativeSemiring using (pow-add)
import Relation.Binary.PropositionalEquality as ≡
import Data.Nat.Properties as ℕ-≡

∷↓-hom : ∀ x xs ρ → ⟦ x ∷ xs ⟧ ρ ≈ ⟦ x ∷↓ xs ⟧ ρ
∷↓-hom (i , x) xs ρ with x ≟C 0#
∷↓-hom (i , x) xs ρ | no ¬p = refl
∷↓-hom (i , x) [] ρ | yes p =
  begin
    (x + 0# * ρ) * ρ ^ i
  ≈⟨ ≪* (p ⟨ +-cong ⟩ zeroˡ ρ) ⟩
    (0# + 0#) * ρ ^ i
  ≈⟨ (≪* +-identityʳ 0#) ⟩
    0# * ρ ^ i
  ≈⟨ zeroˡ (ρ ^ i) ⟩
    0#
  ∎
∷↓-hom (i , x) ((j , y) ∷ xs) ρ | yes p =
  begin
    (x + (y + ⟦ xs ⟧ ρ * ρ) * ρ ^ j * ρ) * ρ ^ i
  ≈⟨ distribʳ (ρ ^ i) x _ ⟩
    x * ρ ^ i + (y + ⟦ xs ⟧ ρ * ρ) * ρ ^ j * ρ * ρ ^ i
  ≈⟨ ≪+ (≪* p ︔ zeroˡ (ρ ^ i)) ⟩
    0# + (y + ⟦ xs ⟧ ρ * ρ) * ρ ^ j * ρ * ρ ^ i
  ≈⟨ +-identityˡ _ ⟩
    (y + ⟦ xs ⟧ ρ * ρ) * ρ ^ j * ρ * ρ ^ i
  ≈⟨ *-assoc _ ρ (ρ ^ i) ⟩
    (y + ⟦ xs ⟧ ρ * ρ) * ρ ^ j * ρ ^ suc i
  ≈⟨  *-assoc _ (ρ ^ j) (ρ ^ suc i) ⟩
    (y + ⟦ xs ⟧ ρ * ρ) * (ρ ^ j * ρ ^ suc i)
  ≈⟨ *≫ pow-add ρ j (suc i) ⟩
    (y + ⟦ xs ⟧ ρ * ρ) * ρ ^ (j ℕ.+ suc i)
  ≡⟨ ≡.cong (λ ij → (y + ⟦ xs ⟧ ρ * ρ) * ρ ^ ij) (ℕ-≡.+-comm j (suc i)) ⟩
    (y + ⟦ xs ⟧ ρ * ρ) * ρ ^ (suc i ℕ.+ j)
  ∎
