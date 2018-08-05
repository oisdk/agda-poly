open import Algebra using (CommutativeSemiring)
import Level
open import Data.Product
open import Function

module Horner (commutativeSemiring : CommutativeSemiring Level.zero Level.zero) where

  -- Now, sparse normal form.

  open import Data.Nat as ℕ using (ℕ; suc) renaming (zero to ℕzero; _+_ to _ℕ+_; _*_ to _ℕ*_)
  open import Data.Product
  open CommutativeSemiring commutativeSemiring

  data Terms : Set

  Poly : Set
  Poly = ℕ × (Carrier × Terms)

  data Terms where
    ⟨⟩ : Terms
    ⟨_⟩ : Poly → Terms

  infixl 6 _⊞_ _⊕_ _⊕]_ _[⊕_
  _⊞_ : Poly → Poly → Poly
  _⊕_ : Terms → Terms → Terms
  _⊕]_ : Terms → Poly → Poly
  _[⊕_ : Poly → Terms → Poly

  open import Function

  (ℕzero , x , xs) ⊞ (ℕzero , y , ys) = ℕzero , (x + y) , (xs ⊕ ys)
  (ℕzero , x , xs) ⊞ (suc j , ys) = ℕzero , x , ⟨ xs ⊕] (j , ys) ⟩
  (suc i , xs) ⊞ (ℕzero , y , ys) = ℕzero , y , ⟨ (i , xs) [⊕ ys ⟩
  (suc i , xs) ⊞ (suc j , ys) = map₁ suc ((i , xs) ⊞ (j , ys))

  xs ⊕ ⟨⟩ = xs
  xs ⊕ ⟨ ys ⟩ = ⟨ xs ⊕] ys ⟩

  ⟨⟩ ⊕] ys = ys
  ⟨ xs ⟩ ⊕] ys = xs ⊞ ys

  xs [⊕ ⟨⟩ = xs
  xs [⊕ ⟨ ys ⟩ = xs ⊞ ys


  open import Monomial commutativeSemiring
    using ()
    renaming (Terms to MTerms; Poly to MPoly; ⟨⟩ to m-⟨⟩; ⟨_⟩ to m-⟨_⟩; ⟦_⟧ to ⟦_⟧ₘ; _⊞_ to _M⊞_)

  expand : Poly → MPoly
  expand′ : Terms → MTerms

  expand (ℕzero , x , xs) = x , expand′ xs
  expand (suc i , xs) = 0# , m-⟨ expand (i , xs) ⟩

  expand′ ⟨⟩ = m-⟨⟩
  expand′ ⟨ x ⟩ = m-⟨ expand x ⟩

  infixr 8 _^_
  _^_ : Carrier → ℕ → Carrier
  x ^ ℕzero = 1#
  x ^ suc i = x * x ^ i

  ⟦_⟧ : Poly → Carrier → Carrier
  ⟦ i , x , ⟨⟩ ⟧ ρ = x * ρ ^ i
  ⟦ i , x , ⟨ xs ⟩ ⟧ ρ = (x + ⟦ xs ⟧ ρ * ρ) * ρ ^ i

  +-hom : (xs ys : Poly) → (ρ : Carrier) → ⟦ xs ⊞ ys ⟧ ρ ≈ ⟦ expand xs M⊞ expand ys ⟧ₘ ρ
  +-hom xs ys ρ = {!!}
