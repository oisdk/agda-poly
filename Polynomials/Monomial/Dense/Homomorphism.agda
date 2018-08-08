{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Polynomials.Monomial.Dense.Homomorphism
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  where

open CommutativeSemiring commutativeSemiring
open import Polynomials.Monomial.Dense commutativeSemiring
open import Polynomials.SemiringReasoning commutativeSemiring

open import Function
open import Data.List as List using ([]; _∷_)


-- The ring of polynomials forms a homomorphism. Here, we prove that.
-- First, addition:
+-hom : ∀ xs ys ρ → ⟦ xs ⟧ ρ + ⟦ ys ⟧ ρ ≈ ⟦ xs ⊞ ys ⟧ ρ
+-hom [] [] ρ = +-identityˡ 0#
+-hom [] (y ∷ ys) ρ = +-identityˡ (⟦ y ∷ ys ⟧ ρ)
+-hom (x ∷ xs) [] ρ = +-identityʳ (⟦ x ∷ xs ⟧ ρ)
+-hom (x ∷ xs) (y ∷ ys) ρ =
  begin
    ⟦ x ∷ xs ⟧ ρ + ⟦ y ∷ ys ⟧ ρ
  ≡⟨⟩
    (x + ⟦ xs ⟧ ρ * ρ) + (y + ⟦ ys ⟧ ρ * ρ)
  ≈⟨ sym (+-assoc _ _ _) ⟩
    ((x + ⟦ xs ⟧ ρ * ρ) + y) + ⟦ ys ⟧ ρ * ρ
  ≈⟨ ≪+ (+-assoc x _ y ︔ +≫ +-comm _ y ︔ sym (+-assoc x y _)) ⟩
    ((x + y) + ⟦ xs ⟧ ρ * ρ) + ⟦ ys ⟧ ρ * ρ
  ≈⟨ +-assoc (x + y) _ _ ⟩
    (x + y) + (⟦ xs ⟧ ρ * ρ + ⟦ ys ⟧ ρ * ρ)
  ≈⟨ sym (+≫ distribʳ ρ _ _) ⟩
    (x + y) + (⟦ xs ⟧ ρ + ⟦ ys ⟧ ρ) * ρ
  ≈⟨ +≫ ≪* +-hom xs ys ρ ⟩
    (x + y) + ⟦ xs ⊞ ys ⟧ ρ * ρ
  ≡⟨⟩
    ⟦ x + y ∷ xs ⊞ ys ⟧ ρ
  ≡⟨⟩
    ⟦ (x ∷ xs) ⊞ (y ∷ ys) ⟧ ρ
  ∎

-- for multiplication, we will first prove this smaller lemma.
⋊-hom : ∀ x ys ρ → x * ⟦ ys ⟧ ρ ≈ ⟦ x ⋊ ys ⟧ ρ
⋊-hom x [] ρ = zeroʳ x
⋊-hom x (y ∷ ys) ρ =
  begin
    x * (y + ⟦ ys ⟧ ρ * ρ)
  ≈⟨ distribˡ x y _ ⟩
    x * y + x * (⟦ ys ⟧ ρ * ρ)
  ≈⟨ +≫ sym (*-assoc x _ ρ) ⟩
    x * y + x * ⟦ ys ⟧ ρ * ρ
  ≈⟨ +≫ ≪* ⋊-hom x ys ρ ⟩
    x * y + ⟦ x ⋊ ys ⟧ ρ * ρ
  ∎

-- Then the full lemma itself.
*-hom : ∀ xs ys ρ → ⟦ xs ⟧ ρ * ⟦ ys ⟧ ρ ≈ ⟦ xs ⊠ ys ⟧ ρ
*-hom [] [] ρ = zeroˡ 0#
*-hom [] (y ∷ ys) ρ = zeroˡ (⟦ y ∷ ys ⟧ ρ)
*-hom (x ∷ xs) [] ρ = zeroʳ (⟦ x ∷ xs ⟧ ρ)
*-hom (x ∷ xs) (y ∷ ys) ρ =
  begin
    (x + ⟦ xs ⟧ ρ * ρ) * (y + ⟦ ys ⟧ ρ * ρ)
  ≈⟨ distribˡ _ y _ ⟩
    (x + ⟦ xs ⟧ ρ * ρ) * y + (x + ⟦ xs ⟧ ρ * ρ) * (⟦ ys ⟧ ρ * ρ)
  ≈⟨ ≪+ distribʳ y x _ ⟩
    x * y + (⟦ xs ⟧ ρ * ρ) * y + (x + ⟦ xs ⟧ ρ * ρ) * (⟦ ys ⟧ ρ * ρ)
  ≈⟨ +-assoc (x * y) _ _ ⟩
    x * y + (⟦ xs ⟧ ρ * ρ * y + (x + ⟦ xs ⟧ ρ * ρ) * (⟦ ys ⟧ ρ * ρ))
  ≅⟨ +≫_ ⟩
    ⟦ xs ⟧ ρ * ρ * y + (x + ⟦ xs ⟧ ρ * ρ) * (⟦ ys ⟧ ρ * ρ)
  ≈⟨ +≫ sym (*-assoc _ (⟦ ys ⟧ ρ) ρ) ⟩
    ⟦ xs ⟧ ρ * ρ * y + (x + ⟦ xs ⟧ ρ * ρ) * ⟦ ys ⟧ ρ * ρ
  ≈⟨ ≪+ ( *-assoc (⟦ xs ⟧ ρ) ρ y ︔ *≫ *-comm ρ y ︔ sym (*-assoc (⟦ xs ⟧ ρ) y ρ) ) ⟩
    ⟦ xs ⟧ ρ * y * ρ + (x + ⟦ xs ⟧ ρ * ρ) * ⟦ ys ⟧ ρ * ρ
  ≈⟨ sym (distribʳ ρ _ _) ⟩
    (⟦ xs ⟧ ρ * y + (x + ⟦ xs ⟧ ρ * ρ) * ⟦ ys ⟧ ρ) * ρ
  ≅⟨ ≪*_ ⟩
    ⟦ xs ⟧ ρ * y + (x + ⟦ xs ⟧ ρ * ρ) * ⟦ ys ⟧ ρ
  ≅⟨ sym ⟩
    ⟦ (x ⋊ ys) ⊞ xs ⊠ (y ∷ ys) ⟧ ρ
  ≈⟨ sym (+-hom (x ⋊ ys) (xs ⊠ (y ∷ ys)) ρ) ⟩
    ⟦ (x ⋊ ys) ⟧ ρ + ⟦ xs ⊠ (y ∷ ys) ⟧ ρ
  ≈⟨ +≫ sym ( *-hom xs _ ρ ) ⟩
    ⟦ (x ⋊ ys) ⟧ ρ + ⟦ xs ⟧ ρ * (y + ⟦ ys ⟧ ρ * ρ)
  ≈⟨ ≪+ sym (⋊-hom x ys ρ) ⟩
    x * ⟦ ys ⟧ ρ + ⟦ xs ⟧ ρ * (y + ⟦ ys ⟧ ρ * ρ)
  ≈⟨ +≫ (distribˡ (⟦ xs ⟧ ρ) y _) ⟩
    x * ⟦ ys ⟧ ρ + (⟦ xs ⟧ ρ * y + ⟦ xs ⟧ ρ * (⟦ ys ⟧ ρ * ρ))
  ≈⟨ sym (+-assoc (x * ⟦ ys ⟧ ρ) _ _) ⟩
    x * ⟦ ys ⟧ ρ + ⟦ xs ⟧ ρ * y + ⟦ xs ⟧ ρ * (⟦ ys ⟧ ρ * ρ)
  ≈⟨ ≪+ +-comm (x * ⟦ ys ⟧ ρ) _ ⟩
    ⟦ xs ⟧ ρ * y + x * ⟦ ys ⟧ ρ + ⟦ xs ⟧ ρ * (⟦ ys ⟧ ρ * ρ)
  ≈⟨ +-assoc _ _ _ ⟩
    ⟦ xs ⟧ ρ * y + (x * ⟦ ys ⟧ ρ + ⟦ xs ⟧ ρ * (⟦ ys ⟧ ρ * ρ))
  ≅⟨ +≫_ ⟩
    x * ⟦ ys ⟧ ρ + ⟦ xs ⟧ ρ * (⟦ ys ⟧ ρ * ρ)
  ≈⟨ +≫ *≫ *-comm _ ρ ⟩
    x * ⟦ ys ⟧ ρ + ⟦ xs ⟧ ρ * (ρ * ⟦ ys ⟧ ρ)
  ≈⟨ +≫ sym (*-assoc _ ρ _) ⟩
    x * ⟦ ys ⟧ ρ + ⟦ xs ⟧ ρ * ρ * ⟦ ys ⟧ ρ
  ≈⟨ sym (distribʳ (⟦ ys ⟧ ρ) x _) ⟩
    (x + ⟦ xs ⟧ ρ * ρ) * ⟦ ys ⟧ ρ
  ∎