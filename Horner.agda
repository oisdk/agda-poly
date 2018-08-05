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

  pow : Poly → Poly
  pow = map₁ suc

  (ℕzero , x , xs) ⊞ (ℕzero , y , ys) = ℕzero , (x + y) , (xs ⊕ ys)
  (ℕzero , x , xs) ⊞ (suc j , ys) = ℕzero , x , ⟨ xs ⊕] (j , ys) ⟩
  (suc i , xs) ⊞ (ℕzero , y , ys) = ℕzero , y , ⟨ (i , xs) [⊕ ys ⟩
  (suc i , xs) ⊞ (suc j , ys) = pow ((i , xs) ⊞ (j , ys))

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
  x ^ suc i = x ^ i * x

  ⟪_⟫ : Terms → Carrier → Carrier
  ⟦_⟧ : Poly → Carrier → Carrier
  ⟪ ⟨⟩ ⟫ ρ = 0#
  ⟪ ⟨ xs ⟩ ⟫ ρ = ⟦ xs ⟧ ρ * ρ
  ⟦ i , x , xs ⟧ ρ = (x + ⟪ xs ⟫ ρ) * ρ ^ i

  open import SemiringReasoning commutativeSemiring

  pow-hom : (xs : Poly) → (ρ : Carrier) → ⟦ pow xs ⟧ ρ ≈ ⟦ xs ⟧ ρ * ρ
  pow-hom (i , x , xs) ρ =
    begin
      ⟦ suc i , x , xs ⟧ ρ
    ≡⟨⟩
      (x + ⟪ xs ⟫ ρ) * ρ ^ suc i
    ≡⟨⟩
      (x + ⟪ xs ⟫ ρ) * (ρ ^ i * ρ)
    ≈⟨ sym (*-assoc _ (ρ ^ i) ρ) ⟩
      (x + ⟪ xs ⟫ ρ) * ρ ^ i * ρ
    ∎

  expand-hom : (xs : Poly) → (ρ : Carrier) → ⟦ xs ⟧ ρ ≈ ⟦ expand xs ⟧ₘ ρ
  expand-hom (ℕzero , x , ⟨⟩) ρ =
    begin
      (x + 0#) * 1#
    ≈⟨ *-identityʳ _ ⟩
      x + 0#
    ≈⟨ +-identityʳ x ⟩
      x
    ∎
  expand-hom (ℕzero , x , ⟨ xs ⟩) ρ =
    begin
      (x + ⟦ xs ⟧ ρ * ρ) * 1#
    ≈⟨ *-identityʳ _ ⟩
      x + ⟦ xs ⟧ ρ * ρ
    ≈⟨ ⋯+⟨ ⟨ expand-hom xs ρ ⟩*⋯ ⟩ ⟩
      x + ⟦ expand xs ⟧ₘ ρ * ρ
    ∎
  expand-hom (suc i , x , xs) ρ =
    begin
      ⟦ suc i , x , xs ⟧ ρ
    ≈⟨ pow-hom (i , x , xs) ρ ⟩
      ⟦ i , x , xs ⟧ ρ * ρ
    ≅⟨ sym ⟩
      0# + ⟦ expand (i , x , xs) ⟧ₘ ρ * ρ
    ≈⟨ +-identityˡ _ ⟩
      ⟦ expand (i , x , xs) ⟧ₘ ρ * ρ
    ≅⟨ ⟨_⟩*⋯ ⟩
      ⟦ expand (i , x , xs) ⟧ₘ ρ
    ≈⟨ sym (expand-hom (i , x , xs) ρ ) ⟩
      ⟦ i , x , xs ⟧ ρ
    ∎

  +-hom : (xs ys : Poly) → (ρ : Carrier) → ⟦ xs ⊞ ys ⟧ ρ ≈ ⟦ expand xs M⊞ expand ys ⟧ₘ ρ
  +-hom (ℕzero , x , ⟨⟩) (ℕzero , y , ⟨⟩) ρ =
    begin
      ((x + y) + 0#) * 1#
    ≈⟨ *-identityʳ _ ⟩
      x + y + 0#
    ≈⟨ +-identityʳ _ ⟩
      x + y
    ∎
  +-hom (ℕzero , x , ⟨⟩) (ℕzero , y , ⟨ ys ⟩) ρ = {!!}
  +-hom (ℕzero , x , ⟨⟩) (suc j , y , ys) ρ = {!!}
  +-hom (ℕzero , x , ⟨ xs ⟩) (j , y , ys) ρ = {!!}
  +-hom (suc i , x , xs) (j , y , ys) ρ = {!!}
