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
record Coeff (i : ℕ) : Set (a ⊔ ℓ)

Coeffs : ℕ → Set (a ⊔ ℓ)
Coeffs n = List (Coeff n × ℕ)

data Poly : ℕ → Set (a ⊔ ℓ) where
  Κ : Carrier → Poly 0
  Ι : ∀ {n} → Coeffs n → Poly (suc n)

Zero : ∀ {n} → Poly n → Set ℓ
Zero (Κ x) = x ≈ 0#
Zero (Ι []) = Lift ℓ ⊤
Zero (Ι (x ∷ xs)) = Lift ℓ ⊥

zero? : ∀ {n} → (p : Poly n) → Dec (Zero p)
zero? (Κ x) = x ≟C 0#
zero? (Ι []) = yes (lift tt)
zero? (Ι (x ∷ xs)) = no lower

record Coeff i where
  constructor coeff-nz
  inductive
  field
    coeff : Poly i
    .coeff≠0 : ¬ Zero coeff
open Coeff

infixr 8 _^_
_^_ : Carrier → ℕ → Carrier
x ^ zero = 1#
x ^ suc n = x * x ^ n


infixr 8 _⍓_
_⍓_ : ∀ {n} → Coeffs n → ℕ → Coeffs n
[] ⍓ i = []
((x , j) ∷ xs) ⍓ i = (x , j ℕ.+ i) ∷ xs

infixr 5 _∷↓_
_∷↓_ : ∀ {n} → (Poly n × ℕ) → Coeffs n → Coeffs n
(x , i) ∷↓ xs with zero? x
... | yes p = xs ⍓ suc i
... | no ¬p = (coeff-nz x ¬p , i) ∷ xs


infixl 6 _⊞_
_⊞_ : ∀ {n} → Poly n → Poly n → Poly n

⊞-Ι : ∀ {n} → Coeffs n → Coeffs n → Coeffs n
⊞-ne : ∀ {p q n}
     → ℕ.Ordering p q
     → (x : Coeff n)
     → Coeffs n
     → (y : Coeff n)
     → Coeffs n
     → Coeffs n

Κ x ⊞ Κ y = Κ (x + y)
Ι x ⊞ Ι y = Ι (⊞-Ι x y)

⊞-Ι [] ys = ys
⊞-Ι (x ∷ xs) [] = x ∷ xs
⊞-Ι ((x , p) ∷ xs) ((y , q) ∷ ys) = ⊞-ne (ℕ.compare p q) x xs y ys

⊞-ne-l : ∀ {n} → ℕ → Coeffs n → (y : Coeff n) → Coeffs n → Coeffs n
⊞-ne-r : ∀ {n} → ℕ → (x : Coeff n) → Coeffs n → Coeffs n → Coeffs n

⊞-ne (ℕ.less    i k) x xs y ys = (x , i) ∷ ⊞-ne-l k xs y ys
⊞-ne (ℕ.greater j k) x xs y ys = (y , j) ∷ ⊞-ne-r k x xs ys
⊞-ne (ℕ.equal   i  ) x xs y ys = (coeff x ⊞ coeff y , i) ∷↓ (⊞-Ι xs ys)

⊞-ne-l k [] y ys = (y , k) ∷ ys
⊞-ne-l k ((x , i) ∷ xs) y ys = ⊞-ne (ℕ.compare i k) x xs y ys

⊞-ne-r k x xs [] = (x , k) ∷ xs
⊞-ne-r k x xs ((y , j) ∷ ys) = ⊞-ne (ℕ.compare k j) x xs y ys





-- -- ⊞-Ι xs ys = {!!}



open import Data.Vec as Vec using (Vec; _∷_; [])

⟦_⟧ : ∀ {n} → Poly n → Vec Carrier n → Carrier
⟦ Κ x ⟧ [] = x
⟦_⟧ {suc n} (Ι x) (y ∷ ρ) = List.foldr coeff-eval 0# x
  where
  coeff-eval : Coeff n × ℕ → Carrier → Carrier
  coeff-eval (coeff-nz c _ , p) xs = (⟦ c ⟧ ρ + xs * y) * y ^ p
