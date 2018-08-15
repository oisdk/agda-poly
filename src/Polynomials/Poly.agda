open import Algebra using (CommutativeSemiring)
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Level using (_⊔_; Lift; lift; lower)
open import Data.Empty
open import Data.Unit using (⊤; tt)

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

Zero : ∀ {n} → Poly n → Set ℓ
Zero (Κ x) = x ≈ 0#
Zero (Ι []) = Lift ℓ ⊤
Zero (Ι (x ∷ xs)) = Lift ℓ ⊥

zero? : ∀ {n} → (p : Poly n) → Dec (Zero p)
zero? (Κ x) = x ≟C 0#
zero? (Ι []) = yes (lift tt)
zero? (Ι (x ∷ xs)) = no lower

-- Bit of a misnomer. Avoids constant polys,
-- allows constant (as in Κ).
NonConst : ∀ {n} → Poly n → Set
NonConst (Κ _) = ⊤
NonConst (Ι []) = ⊥
NonConst (Ι (_ ∷ [])) = ⊥
NonConst (Ι (_ ∷ _ ∷ _)) = ⊤

nonConst? : ∀ {n} → (p : Poly n) → Dec (NonConst p)
nonConst? (Κ x) = yes tt
nonConst? (Ι []) = no (λ z → z)
nonConst? (Ι (_ ∷ [])) = no (λ z → z)
nonConst? (Ι (_ ∷ _ ∷ _)) = yes tt

data Coeff where
  coeff : ∀ i {j}
        → (c : Poly j)
        → .(¬ Zero c)
        → .(NonConst c)
        → ℕ
        → Coeff (i ℕ.+ j)

infixr 8 _^_
_^_ : Carrier → ℕ → Carrier
x ^ zero = 1#
x ^ suc n = x * x ^ n

open import Data.Vec as Vec using (Vec; _∷_; [])

⟦_⟧ : ∀ {n} → Poly n → Vec Carrier n → Carrier
⟦ Κ x ⟧ [] = x
⟦_⟧ {suc n} (Ι x) (y ∷ ρ) = List.foldr coeff-eval 0# x
  where
  ⟦_⟧-vec : ∀ {m} → Poly m → ∀ n → Vec Carrier (n ℕ.+ m) → Carrier
  ⟦ p ⟧-vec zero xs = ⟦ p ⟧ xs
  ⟦ p ⟧-vec (suc n) (_ ∷ xs) = ⟦ p ⟧-vec n xs

  coeff-eval : Coeff n → Carrier → Carrier
  coeff-eval (coeff i c _ _ p) xs = (⟦ c ⟧-vec i ρ + xs * y) * y ^ p

