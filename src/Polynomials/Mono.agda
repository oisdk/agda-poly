open import Algebra using (CommutativeSemiring)
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Level using (_⊔_)

module Polynomials.Mono
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open CommutativeSemiring commutativeSemiring hiding (zero)

open import Data.List as List using (_∷_; []; foldr; List)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product

infix 4 _≉_
_≉_ : Carrier → Carrier → Set ℓ
x ≉ y = ¬ (x ≈ y)

infixr 9 _^_⦅_⦆
record Coefficient : Set (a ⊔ ℓ) where
  constructor _^_⦅_⦆
  field
    coeff : Carrier
    expon : ℕ
    .coeff≠0 : coeff ≉ 0#


Poly : Set (a ⊔ ℓ)
Poly = List Coefficient

pow : ℕ → Poly → Poly
pow i [] = []
pow i (x ^ j ⦅ x≠0 ⦆ ∷ xs) = (x ^ j ℕ.+ i ⦅ x≠0 ⦆) ∷ xs

infixr 5 _∷↓_
_∷↓_ : Carrier × ℕ → Poly → Poly
_∷↓_ (x , i) with x ≟C 0#
... | yes p = pow (suc i)
... | no ¬p = x ^ i ⦅ ¬p ⦆ ∷_

infixl 6 _⊞_
_⊞_ : Poly → Poly → Poly
⊞-ne : ∀ {i j} → ℕ.Ordering i j → (x : Carrier) → .(x ≉ 0#) → Poly → (y : Carrier) → .(y ≉ 0#) → Poly → Poly
⊞-ne-l : ℕ → Poly → (y : Carrier) → .(y ≉ 0#) → Poly → Poly
⊞-ne-r : ℕ → (x : Carrier) → .(x ≉ 0#) → Poly → Poly → Poly

[] ⊞ ys = ys
(x ∷ xs) ⊞ [] = x ∷ xs
((x ^ i ⦅ x≠0 ⦆) ∷ xs) ⊞ ((y ^ j ⦅ y≠0 ⦆) ∷ ys) = ⊞-ne (ℕ.compare i j) x x≠0 xs y y≠0 ys

⊞-ne (ℕ.less    i k) x x≠0 xs y y≠0 ys = x ^ i ⦅ x≠0 ⦆ ∷ ⊞-ne-l k xs y y≠0 ys
⊞-ne (ℕ.greater j k) x x≠0 xs y y≠0 ys = y ^ j ⦅ y≠0 ⦆ ∷ ⊞-ne-r k x x≠0 xs ys
⊞-ne (ℕ.equal   i  ) x x≠0 xs y y≠0 ys = (x + y , i) ∷↓ (xs ⊞ ys)

⊞-ne-l k [] y y≠0 ys = (y ^ k ⦅ y≠0 ⦆) ∷ ys
⊞-ne-l k ((x ^ i ⦅ x≠0 ⦆) ∷ xs) y y≠0 ys = ⊞-ne (ℕ.compare i k) x x≠0 xs y y≠0 ys

⊞-ne-r k x x≠0 xs [] = (x ^ k ⦅ x≠0 ⦆) ∷ xs
⊞-ne-r k x x≠0 xs ((y ^ j ⦅ y≠0 ⦆) ∷ ys) = ⊞-ne (ℕ.compare k j) x x≠0 xs y y≠0 ys

-- Multiply a polynomial by a constant factor
infixl 7 _⋊_
_⋊_ : Carrier → Poly → Poly
x ⋊ ((y ^ j ⦅ _ ⦆) ∷ ys) = (x * y , j) ∷↓ x ⋊ ys
x ⋊ [] = []

infixl 7 _⊠_
_⊠_ : Poly → Poly → Poly
[] ⊠ _ = []
(x ∷ xs) ⊠ [] = []
((x ^ i ⦅ _ ⦆) ∷ xs) ⊠ ((y ^ j ⦅ y≠0 ⦆) ∷ ys) = (x * y , i ℕ.+ j) ∷↓ x ⋊ ys ⊞ xs ⊠ (y ^ 0 ⦅ y≠0 ⦆ ∷ ys)

κ : Carrier → Poly
κ x = (x , 0) ∷↓ []

ι : Poly
ι = (1# , 1) ∷↓ []

----------------------------------------------------------------------
-- Evaluation
----------------------------------------------------------------------
-- We "run" the polynomial on some input with Horner's method.

infixr 8 _^_
_^_ : Carrier → ℕ → Carrier
x ^ zero = 1#
x ^ suc n = x * x ^ n

_↦_^*_ : Carrier → Coefficient → Carrier → Carrier
ρ ↦ (x ^ i ⦅ _ ⦆) ^* xs = (x + xs * ρ) * ρ ^ i

⟦_⟧ : Poly → Carrier → Carrier
⟦ xs ⟧ ρ = List.foldr (ρ ↦_^*_) 0# xs
