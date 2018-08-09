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
pow i ((j , x) ∷ xs) = (j ℕ.+ i , x) ∷ xs

infixr 5 _∷↓_
_∷↓_ : (ℕ × Carrier) → Poly → Poly
_∷↓_ (i , x) with x ≟C 0#
... | yes p = pow (suc i)
... | no ¬p = _∷_ (i , x)

normalise : Poly → Poly
normalise = List.foldr _∷↓_ []

module Homomorphism where
  open import Polynomials.SemiringReasoning commutativeSemiring
  open import Function
  open import Polynomials.Monomial.Sparse.Homomorphism commutativeSemiring
    using (pow-add)
  import Relation.Binary.PropositionalEquality as ≡
  import Data.Nat.Properties as ℕ-≡

  pow-hom : ∀ i xs ρ → ⟦ xs ⟧ ρ * ρ ^ i ≈ ⟦ pow i xs ⟧ ρ
  pow-hom i [] ρ = zeroˡ (ρ ^ i)
  pow-hom i ((j , x) ∷ xs) ρ = *-assoc _ (ρ ^ j) (ρ ^ i) ︔ *≫ pow-add ρ j i

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
    ∎

  normalise-hom : ∀ xs ρ → ⟦ xs ⟧ ρ ≈ ⟦ normalise xs ⟧ ρ
  normalise-hom [] ρ = refl
  normalise-hom ((i , x) ∷ xs) ρ with x ≟C 0#
  ... | no ¬p = ≪* +≫ ≪* normalise-hom xs ρ
  ... | yes p =
    begin
      ⟦ (i , x) ∷ xs ⟧ ρ
    ≡⟨⟩
      (x + ⟦ xs ⟧ ρ * ρ) * ρ ^ i
    ≈⟨ ≪* ≪+ p ⟩
      (0# + ⟦ xs ⟧ ρ * ρ) * ρ ^ i
    ≈⟨ ≪* +-identityˡ _ ⟩
      (⟦ xs ⟧ ρ * ρ) * ρ ^ i
    ≈⟨ ≪* ≪* (normalise-hom xs ρ) ⟩
      ⟦ normalise xs ⟧ ρ * ρ * ρ ^ i
    ≈⟨ *-assoc _ ρ _ ⟩
      ⟦ normalise xs ⟧ ρ * ρ ^ suc i
    ≈⟨ pow-hom (suc i) (normalise xs) ρ ⟩
      ⟦ pow (suc i) (normalise xs) ⟧ ρ
    ∎
