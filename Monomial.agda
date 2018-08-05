open import Algebra using (CommutativeSemiring)
import Level
open import Data.Product
open import Function

module Monomial (commutativeSemiring : CommutativeSemiring Level.zero Level.zero) where

  -- We start with the inefficient, but easy-to-prove, monomial case

  open CommutativeSemiring commutativeSemiring

  data Terms : Set
  Poly : Set
  Poly = Carrier × Terms

  data Terms where
    ⟨⟩  : Terms
    ⟨_⟩ : Poly → Terms

  c : Poly → Carrier
  c = proj₁

  Δ : Poly → Terms
  Δ = proj₂

  -- Square points towards poly; circle towards terms.
  infixl 6 _⊞_ _⊕_ _⊕]_
  _⊞_ : Poly → Poly → Poly
  _⊕_ : Terms → Terms → Terms
  _⊕]_ : Terms → Poly → Poly

  (x , xs) ⊞ (y , ys) = x + y , (xs ⊕ ys)

  xs ⊕ ⟨⟩ = xs
  xs ⊕ ⟨ ys ⟩ = ⟨ xs ⊕] ys ⟩

  ⟨⟩ ⊕] ys = ys
  ⟨ xs ⟩ ⊕] ys = xs ⊞ ys

  infixl 7 _⨵_
  _⨵_ : Carrier → Terms → Terms
  x ⨵ ⟨⟩ = ⟨⟩
  x ⨵ ⟨ y , ys ⟩ = ⟨ x * y , x ⨵ ys ⟩

  infixl 7 _⊠_
  _⊠_ : Poly → Poly → Poly
  _⊗]_ : Terms → Poly → Terms

  (x , xs) ⊠ ys = x * c ys , (x ⨵ Δ ys ⊕ xs ⊗] ys)

  ⟨⟩ ⊗] _ = ⟨⟩
  ⟨ xs ⟩ ⊗] ys = ⟨ xs ⊠ ys ⟩

  ⟦_⟧ : Poly → Carrier → Carrier
  ⟦ x , ⟨⟩ ⟧ ρ = x
  ⟦ x , ⟨ xs ⟩ ⟧ ρ = x + ⟦ xs ⟧ ρ * ρ

  open import SemiringReasoning commutativeSemiring

  +-hom : (xs ys : Poly) → (ρ : Carrier) → ⟦ xs ⟧ ρ + ⟦ ys ⟧ ρ ≈ ⟦ xs ⊞ ys ⟧ ρ
  +-hom (x , ⟨⟩) (y , ⟨⟩) ρ = refl
  +-hom (x , ⟨⟩) (y , ⟨ ys ⟩) ρ =
    begin
      x + (y + ⟦ ys ⟧ ρ * ρ)
    ≈⟨ sym (+-assoc x y _) ⟩
      x + y + ⟦ ys ⟧ ρ * ρ
    ∎
  +-hom (x , ⟨ xs ⟩) (y , ⟨⟩) ρ =
    begin
      x + ⟦ xs ⟧ ρ * ρ + y
    ≈⟨ +-assoc x _ y ⟩
      x + (⟦ xs ⟧ ρ * ρ + y)
    ≈⟨ ⋯+⟨ +-comm _ y ⟩  ⟩
      x + (y + ⟦ xs ⟧ ρ * ρ)
    ≈⟨ sym (+-assoc x y _) ⟩
      x + y + ⟦ xs ⟧ ρ * ρ
    ∎
  +-hom (x , ⟨ xs ⟩) (y , ⟨ ys ⟩) ρ = begin
      (x + ⟦ xs ⟧ ρ * ρ) + (y + ⟦ ys ⟧ ρ * ρ)
    ≈⟨ sym (+-assoc _ y _) ⟩
      ((x + ⟦ xs ⟧ ρ * ρ) + y) + (⟦ ys ⟧ ρ * ρ)
    ≈⟨ ⟨ +-assoc x _ y ︔ ⋯+⟨ +-comm _ y ⟩ ︔ sym (+-assoc x y _) ⟩+⋯ ⟩
      ((x + y) + ⟦ xs ⟧ ρ * ρ) + (⟦ ys ⟧ ρ * ρ)
    ≈⟨ +-assoc (x + y) _ _ ⟩
      (x + y) + (⟦ xs ⟧ ρ * ρ + ⟦ ys ⟧ ρ * ρ)
    ≅⟨ ⋯+⟨_⟩ ⟩
      ⟦ xs ⟧ ρ * ρ + ⟦ ys ⟧ ρ * ρ
    ≈⟨ sym (distribʳ ρ _ _) ⟩
      (⟦ xs ⟧ ρ + ⟦ ys ⟧ ρ) * ρ
    ≈⟨ ⟨ +-hom xs ys ρ ⟩*⋯ ⟩
      ⟦ xs ⊞ ys ⟧ ρ * ρ
    ∎

  ⨵-hom : (x : Carrier) → (ys : Poly) → (ρ : Carrier) → x * ⟦ ys ⟧ ρ ≈ ⟦ x * c ys , x ⨵ Δ ys ⟧ ρ
  ⨵-hom x (y , ⟨⟩) ρ = refl
  ⨵-hom x (y , ⟨ ys ⟩) ρ =
    begin
      x * (y + ⟦ ys ⟧ ρ * ρ)
    ≈⟨ distribˡ x y _ ⟩
      x * y + x * (⟦ ys ⟧ ρ * ρ)
    ≅⟨ ⋯+⟨_⟩ ⟩
      x * (⟦ ys ⟧ ρ * ρ)
    ≈⟨ sym (*-assoc x _ ρ) ⟩
      x * ⟦ ys ⟧ ρ * ρ
    ≈⟨ ⟨ ⨵-hom x ys ρ ⟩*⋯  ⟩
      ⟦ x * c ys , x ⨵ Δ ys ⟧ ρ * ρ
    ∎

  *-hom : (x y : Poly) → (ρ : Carrier) → ⟦ x ⟧ ρ * ⟦ y ⟧ ρ ≈ ⟦ x ⊠ y ⟧ ρ
  *-hom (x , ⟨⟩) (y , ⟨⟩) ρ = refl
  *-hom (x , ⟨⟩) (y , ⟨ ys ⟩) ρ =
    begin
      x * (y + ⟦ ys ⟧ ρ * ρ)
    ≈⟨ distribˡ x y _ ⟩
      x * y + x * (⟦ ys ⟧ ρ * ρ)
    ≅⟨ ⋯+⟨_⟩ ⟩
      x * (⟦ ys ⟧ ρ * ρ)
    ≈⟨ sym (*-assoc x _ ρ) ⟩
      (x * ⟦ ys ⟧ ρ) * ρ
    ≈⟨ ⟨ ⨵-hom x ys ρ ⟩*⋯ ⟩
      ⟦ x * c ys , x ⨵ Δ ys ⟧ ρ * ρ
    ∎
  *-hom (x , ⟨ xs ⟩) (y , ⟨⟩) ρ =
    begin
      (x + ⟦ xs ⟧ ρ * ρ) * y
    ≈⟨ distribʳ y x _ ⟩
      x * y + (⟦ xs ⟧ ρ * ρ) * y
    ≅⟨ ⋯+⟨_⟩ ⟩
      (⟦ xs ⟧ ρ * ρ) * y
    ≅⟨ sym ⟩
      ⟦ xs ⊠ (y , ⟨⟩) ⟧ ρ * ρ
    ≈⟨ ⟨ sym (*-hom xs _ ρ) ⟩*⋯ ⟩
      ⟦ xs ⟧ ρ * y * ρ
    ≈⟨ *-assoc _ y ρ ⟩
      ⟦ xs ⟧ ρ * (y * ρ)
    ≈⟨ ⋯*⟨ *-comm y ρ ⟩ ⟩
      ⟦ xs ⟧ ρ * (ρ * y)
    ≈⟨ sym (*-assoc _ ρ y) ⟩
      ⟦ xs ⟧ ρ * ρ * y
    ∎
  *-hom (x , ⟨ xs ⟩) (y , ⟨ ys ⟩) ρ =
    begin
      (x + ⟦ xs ⟧ ρ * ρ) * (y + ⟦ ys ⟧ ρ * ρ)
    ≈⟨ distribˡ _ y _ ⟩
      (x + ⟦ xs ⟧ ρ * ρ) * y + (x + ⟦ xs ⟧ ρ * ρ) * (⟦ ys ⟧ ρ * ρ)
    ≈⟨ ⟨ distribʳ y x _ ⟩+⋯ ⟩
      x * y + (⟦ xs ⟧ ρ * ρ) * y + (x + ⟦ xs ⟧ ρ * ρ) * (⟦ ys ⟧ ρ * ρ)
    ≈⟨ +-assoc (x * y) _ _ ⟩
      x * y + (⟦ xs ⟧ ρ * ρ * y + (x + ⟦ xs ⟧ ρ * ρ) * (⟦ ys ⟧ ρ * ρ))
    ≅⟨ ⋯+⟨_⟩ ⟩
      ⟦ xs ⟧ ρ * ρ * y + (x + ⟦ xs ⟧ ρ * ρ) * (⟦ ys ⟧ ρ * ρ)
    ≈⟨ sym ⋯+⟨ *-assoc _ (⟦ ys ⟧ ρ) ρ ⟩ ⟩
      ⟦ xs ⟧ ρ * ρ * y + (x + ⟦ xs ⟧ ρ * ρ) * ⟦ ys ⟧ ρ * ρ
    ≈⟨ ⟨ *-assoc (⟦ xs ⟧ ρ) ρ y ︔ ⋯*⟨ *-comm ρ y ⟩ ︔ sym (*-assoc (⟦ xs ⟧ ρ) y ρ) ⟩+⋯ ⟩
      ⟦ xs ⟧ ρ * y * ρ + (x + ⟦ xs ⟧ ρ * ρ) * ⟦ ys ⟧ ρ * ρ
    ≈⟨ sym (distribʳ ρ _ _) ⟩
      (⟦ xs ⟧ ρ * y + (x + ⟦ xs ⟧ ρ * ρ) * ⟦ ys ⟧ ρ) * ρ
    ≅⟨ ⟨_⟩*⋯ ⟩
      ⟦ xs ⟧ ρ * y + (x + ⟦ xs ⟧ ρ * ρ) * ⟦ ys ⟧ ρ
    ≅⟨ sym ⟩
      ⟦ (x * c ys , x ⨵ Δ ys) ⊞ xs ⊠ (y , ⟨ ys ⟩) ⟧ ρ
    ≈⟨ sym (+-hom (x * c ys , x ⨵ Δ ys) (xs ⊠ (y , ⟨ ys ⟩)) ρ) ⟩
      ⟦ (x * c ys , x ⨵ Δ ys) ⟧ ρ + ⟦ xs ⊠ (y , ⟨ ys ⟩) ⟧ ρ
    ≈⟨ sym ⋯+⟨ *-hom xs _ ρ ⟩ ⟩
      ⟦ (x * c ys , x ⨵ Δ ys) ⟧ ρ + ⟦ xs ⟧ ρ * (y + ⟦ ys ⟧ ρ * ρ)
    ≈⟨ sym ⟨ ⨵-hom x ys ρ ⟩+⋯ ⟩
      x * ⟦ ys ⟧ ρ + ⟦ xs ⟧ ρ * (y + ⟦ ys ⟧ ρ * ρ)
    ≈⟨ ⋯+⟨ distribˡ (⟦ xs ⟧ ρ) y _ ⟩ ⟩
      x * ⟦ ys ⟧ ρ + (⟦ xs ⟧ ρ * y + ⟦ xs ⟧ ρ * (⟦ ys ⟧ ρ * ρ))
    ≈⟨ sym (+-assoc (x * ⟦ ys ⟧ ρ) _ _) ⟩
      x * ⟦ ys ⟧ ρ + ⟦ xs ⟧ ρ * y + ⟦ xs ⟧ ρ * (⟦ ys ⟧ ρ * ρ)
    ≈⟨ ⟨ +-comm (x * ⟦ ys ⟧ ρ) _ ⟩+⋯ ⟩
      ⟦ xs ⟧ ρ * y + x * ⟦ ys ⟧ ρ + ⟦ xs ⟧ ρ * (⟦ ys ⟧ ρ * ρ)
    ≈⟨ +-assoc _ _ _ ⟩
      ⟦ xs ⟧ ρ * y + (x * ⟦ ys ⟧ ρ + ⟦ xs ⟧ ρ * (⟦ ys ⟧ ρ * ρ))
    ≅⟨ ⋯+⟨_⟩ ⟩
      x * ⟦ ys ⟧ ρ + ⟦ xs ⟧ ρ * (⟦ ys ⟧ ρ * ρ)
    ≈⟨ ⋯+⟨ ⋯*⟨ *-comm _ ρ ⟩ ⟩ ⟩
      x * ⟦ ys ⟧ ρ + ⟦ xs ⟧ ρ * (ρ * ⟦ ys ⟧ ρ)
    ≈⟨ sym ⋯+⟨ *-assoc _ ρ _ ⟩ ⟩
      x * ⟦ ys ⟧ ρ + ⟦ xs ⟧ ρ * ρ * ⟦ ys ⟧ ρ
    ≈⟨ sym (distribʳ (⟦ ys ⟧ ρ) x _) ⟩
      (x + ⟦ xs ⟧ ρ * ρ) * ⟦ ys ⟧ ρ
    ∎
