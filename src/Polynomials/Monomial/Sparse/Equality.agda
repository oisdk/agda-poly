open import Algebra using (CommutativeSemiring)

module Polynomials.Monomial.Sparse.Equality
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  where

open CommutativeSemiring commutativeSemiring

open import Polynomials.Monomial.Sparse commutativeSemiring
open import Data.List as List using ([]; _∷_)
open import Data.Product
open import Level using (_⊔_)

infix 4 _≋_
infixr 5 _∷≋_
data _≋_ : Poly → Poly → Set (a ⊔ ℓ) where
  []≋ : [] ≋ []
  _∷≋_ : ∀ {x y n xs ys} → x ≈ y → xs ≋ ys → ((n , x) ∷ xs) ≋ ((n , y) ∷ ys)

open import Polynomials.SemiringReasoning commutativeSemiring
open import Function

⟦_⟧-cong : ∀ {xs ys} → xs ≋ ys → ∀ ρ → ⟦ xs ⟧ ρ ≈ ⟦ ys ⟧ ρ
⟦ []≋ ⟧-cong ρ = refl
⟦ x ∷≋ xs ⟧-cong ρ = ≪* (x ⟨ +-cong ⟩ (≪* ⟦ xs ⟧-cong ρ))

open import Relation.Nullary
open import Relation.Binary

module Decidable
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

  import Data.Nat as ℕ
  import Relation.Binary.PropositionalEquality as ≡

  _≟_ : ∀ xs ys → Dec (xs ≋ ys)
  [] ≟ [] = yes []≋
  [] ≟ (x ∷ ys) = no λ ()
  (x ∷ xs) ≟ [] = no λ ()
  ((i , x) ∷ xs) ≟ ((j , y) ∷ ys) with i ℕ.≟ j
  ... | no ¬p = no λ { (z ∷≋ zs) → ¬p ≡.refl }
  ... | yes ≡.refl with x ≟C y
  ... | no ¬p = no λ { (z ∷≋ zs) → ¬p z }
  ... | yes p with xs ≟ ys
  ... | no ¬p = no λ { (z ∷≋ zs) → ¬p zs }
  ... | yes ps = yes (p ∷≋ ps)
