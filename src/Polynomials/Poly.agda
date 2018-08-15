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
data Coeff : ℕ → Set (a ⊔ ℓ)

data Poly : ℕ → Set (a ⊔ ℓ) where
  Κ : Carrier → Poly 0
  Ι : ∀ {n} → List (Coeff n) → Poly (suc n)

NonZero : ∀ {n} → Poly n → Set ℓ
NonZero (Κ x) = ¬ (x ≈ 0#)
NonZero (Ι []) = Lift ℓ ⊥
NonZero (Ι (x ∷ xs)) = Lift ℓ ⊤

-- Bit of a misnomer. Avoids constant polys,
-- allows constant (as in Κ).
NonConst : ∀ {n} → Poly n → Set
NonConst (Κ _) = ⊤
NonConst (Ι []) = ⊥
NonConst (Ι (_ ∷ [])) = ⊥
NonConst (Ι (_ ∷ _ ∷ _)) = ⊤

data Coeff where
  coeff : ∀ i {j}
        → (c : Poly j)
        → .(NonZero c)
        → .(NonConst c)
        → ℕ
        → Coeff (i ℕ.+ j)

infixr 8 _^_
_^_ : Carrier → ℕ → Carrier
x ^ zero = 1#
x ^ suc n = x * x ^ n

open import Data.Vec as Vec using (Vec; _∷_; [])

coeff-eval : ∀ {n} → Vec Carrier (suc n) → Coeff n → Carrier → Carrier

⟦_⟧ : ∀ {n} → Poly n → Vec Carrier n → Carrier
⟦ Κ x ⟧ [] = x
⟦ Ι x ⟧ ρ = List.foldr (coeff-eval ρ) 0# x

coeff-eval (y ∷ ρ) (coeff i x _ _ p) xs = (⟦ x ⟧ (Vec.drop i ρ) + xs * y) * y ^ p
