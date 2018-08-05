{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
import Level
open import Data.Product
open import Function
open import Relation.Binary

module Expr
  (commutativeSemiring : CommutativeSemiring Level.zero Level.zero)
  where

open CommutativeSemiring commutativeSemiring

infixl 7 _⊗_
infixl 6 _⊕_
data Expr : Set where
  ι : Expr
  κ : Carrier → Expr
  _⊕_ : Expr → Expr → Expr
  _⊗_ : Expr → Expr → Expr

⟦_⟧ : Expr → Carrier → Carrier
⟦ ι ⟧ ρ = ρ
⟦ κ x ⟧ ρ = x
⟦ expₗ ⊕ expᵣ ⟧ ρ = ⟦ expₗ ⟧ ρ + ⟦ expᵣ ⟧ ρ
⟦ expₗ ⊗ expᵣ ⟧ ρ = ⟦ expₗ ⟧ ρ * ⟦ expᵣ ⟧ ρ

open import Monomial commutativeSemiring
  renaming (⟦_⟧ to ⟦_⟧ₚ)

⟦_⟧↓ : Expr → Poly
⟦ ι ⟧↓ = ( 0# , ⟨ 1# , ⟨⟩  ⟩ )
⟦ κ x ⟧↓ = x , ⟨⟩
⟦ expₗ ⊕ expᵣ ⟧↓ = ⟦ expₗ ⟧↓ ⊞ ⟦ expᵣ ⟧↓
⟦ expₗ ⊗ expᵣ ⟧↓ = ⟦ expₗ ⟧↓ ⊠ ⟦ expᵣ ⟧↓

open import SemiringReasoning commutativeSemiring
open import Monomial.Homomorphism commutativeSemiring

norm-hom : ∀ xs ρ → ⟦ ⟦ xs ⟧↓ ⟧ₚ ρ ≈ ⟦ xs ⟧ ρ
norm-hom ι ρ =
  begin
    0# + 1# * ρ
  ≈⟨ +-identityˡ (1# * ρ) ⟩
    1# * ρ
  ≈⟨ *-identityˡ ρ ⟩
    ρ
  ∎
norm-hom (κ x) ρ = refl
norm-hom (xs ⊕ ys) ρ =
  begin
    ⟦ ⟦ xs ⟧↓ ⊞ ⟦ ys ⟧↓ ⟧ₚ ρ
  ≈⟨ sym (+-hom ⟦ xs ⟧↓ ⟦ ys ⟧↓ ρ) ⟩
    ⟦ ⟦ xs ⟧↓ ⟧ₚ ρ + ⟦ ⟦ ys ⟧↓ ⟧ₚ ρ
  ≈⟨ +-cong (norm-hom xs ρ) (norm-hom ys ρ) ⟩
    ⟦ xs ⟧ ρ + ⟦ ys ⟧ ρ
  ∎
norm-hom (xs ⊗ ys) ρ =
  begin
    ⟦ ⟦ xs ⟧↓ ⊠ ⟦ ys ⟧↓ ⟧ₚ ρ
  ≈⟨ sym (*-hom ⟦ xs ⟧↓ ⟦ ys ⟧↓ ρ) ⟩
    ⟦ ⟦ xs ⟧↓ ⟧ₚ ρ * ⟦ ⟦ ys ⟧↓ ⟧ₚ ρ
  ≈⟨ *-cong (norm-hom xs ρ) (norm-hom ys ρ) ⟩
    ⟦ xs ⟧ ρ * ⟦ ys ⟧ ρ
  ∎
