open import Algebra using (CommutativeSemiring)
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Level using (_⊔_; Lift)
open import Data.Empty
open import Data.Unit using (⊤)

module Polynomials.Poly
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open CommutativeSemiring commutativeSemiring hiding (zero)

open import Data.List as List using (_∷_; []; foldr; List)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product

-- Either a constant carrier
record Coeff (n : ℕ) : Set (a ⊔ ℓ)

data Poly : ℕ → Set (a ⊔ ℓ) where
  Κ : Carrier → Poly 0
  Ι : ∀ {n} → List (Coeff n) → Poly (suc n)

NonZero : ∀ {n} → Poly n → Set ℓ
NonZero (Κ x) = ¬ (x ≈ 0#)
NonZero (Ι []) = Lift ℓ ⊥
NonZero (Ι (x ∷ xs)) = Lift ℓ ⊤

record Coeff (n : ℕ) where
  constructor _^^_⦅_⦆
  inductive
  field
    coeff : Poly n
    expon : ℕ
    .coeff≠0 : NonZero coeff

infixr 8 _^_
_^_ : Carrier → ℕ → Carrier
x ^ zero = 1#
x ^ suc n = x * x ^ n

open import Data.Vec

coeff-eval : ∀ {n} → Vec Carrier (suc n) → Coeff n → Carrier → Carrier

⟦_⟧ : ∀ {n} → Poly n → Vec Carrier n → Carrier
⟦ Κ x ⟧ [] = x
⟦ Ι x ⟧ ρ = List.foldr (coeff-eval ρ) 0# x

coeff-eval (y ∷ ρ) (x ^^ i ⦅ _ ⦆) xs = (⟦ x ⟧ ρ + xs * y) * y ^ i
