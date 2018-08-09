open import Algebra using (CommutativeSemiring)

module Polynomials.Monomial.Sparse
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  where

open CommutativeSemiring commutativeSemiring hiding (zero)

open import Data.List as List using (_∷_; []; foldr)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product

Poly : Set a
Poly = List.List (ℕ × Carrier)

infixl 6 _⊞_
_⊞_ : Poly → Poly → Poly
⊞-ne : ∀ {i j} → ℕ.Ordering i j → Carrier → Poly → Carrier → Poly → Poly
⊞-ne-l : ℕ → Poly → Carrier → Poly → Poly
⊞-ne-r : ℕ → Carrier → Poly → Poly → Poly

[] ⊞ ys = ys
(x ∷ xs) ⊞ [] = x ∷ xs
((i , x) ∷ xs) ⊞ ((j , y) ∷ ys) = ⊞-ne (ℕ.compare i j) x xs y ys

⊞-ne (ℕ.less    i k) x xs y ys = (i , x) ∷ ⊞-ne-l k xs y ys
⊞-ne (ℕ.equal   i  ) x xs y ys = (i , x + y) ∷ (xs ⊞ ys)
⊞-ne (ℕ.greater j k) x xs y ys = (j , y) ∷ ⊞-ne-r k x xs ys

⊞-ne-l k [] y ys = (k , y) ∷ ys
⊞-ne-l k ((i , x) ∷ xs) y ys = ⊞-ne (ℕ.compare i k) x xs y ys

⊞-ne-r k x xs [] = (k , x) ∷ xs
⊞-ne-r k x xs ((j , y) ∷ ys) = ⊞-ne (ℕ.compare k j) x xs y ys

-- Multiply a polynomial by a constant factor
infixl 7 _⋊_
_⋊_ : Carrier → Poly → Poly
x ⋊ ys = List.map (map₂ (x *_)) ys

infixl 7 _⊠_
_⊠_ : Poly → Poly → Poly
[] ⊠ _ = []
(x ∷ xs) ⊠ [] = []
((i , x) ∷ xs) ⊠ ((j , y) ∷ ys) = (i ℕ.+ j , x * y) ∷ x ⋊ ys ⊞ xs ⊠ ((0 , y) ∷ ys)

κ : Carrier → Poly
κ x = (zero ,  x) ∷ []

ι : Poly
ι = (suc zero , 1#) ∷ []

----------------------------------------------------------------------
-- Evaluation
----------------------------------------------------------------------
-- We "run" the polynomial on some input with Horner's method.

infixr 8 _^_
_^_ : Carrier → ℕ → Carrier
x ^ zero = 1#
x ^ suc n = x * x ^ n

_↦_^*_ : Carrier → (ℕ × Carrier) → Carrier → Carrier
ρ ↦ (i , x) ^* xs = (x + xs * ρ) * ρ ^ i

⟦_⟧ : Poly → Carrier → Carrier
⟦ xs ⟧ ρ = List.foldr (ρ ↦_^*_) 0# xs