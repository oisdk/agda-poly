{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
import Level
open import Data.Product
open import Function
open import Relation.Binary

module Monomial
  (commutativeSemiring : CommutativeSemiring Level.zero Level.zero)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))

  where

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

  _≈P_ : Poly → Poly → Set
  data _≈T_ : Terms → Terms → Set where
    ⟨⟩-≈ : ⟨⟩ ≈T ⟨⟩
    ⟨_⟩-≈ : ∀ {xs ys} → xs ≈P ys → ⟨ xs ⟩ ≈T ⟨ ys ⟩
  (x , xs) ≈P (y , ys) = (x ≈ y) × (xs ≈T ys)

  open import Relation.Nullary

  _≟_ : (xs ys : Poly) → Dec (xs ≈P ys)
  _≟T_ : (xs ys : Terms) → Dec (xs ≈T ys)
  ⟨⟩ ≟T ⟨⟩ = yes ⟨⟩-≈
  ⟨⟩ ≟T ⟨ ys ⟩ = no (λ ())
  ⟨ xs ⟩ ≟T ⟨⟩ = no (λ ())
  ⟨ xs ⟩ ≟T ⟨ ys ⟩ with xs ≟ ys
  (⟨ xs ⟩ ≟T ⟨ ys ⟩) | yes p = yes ⟨ p ⟩-≈
  (⟨ xs ⟩ ≟T ⟨ ys ⟩) | no ¬p = no λ { ⟨ prf ⟩-≈ → ¬p prf }
  (x , xs) ≟ (y , ys) with x ≟C y
  ((x , xs) ≟ (y , ys)) | yes p with xs ≟T ys
  ((x , xs) ≟ (y , ys)) | yes p | yes ps = yes (p , ps)
  ((x , xs) ≟ (y , ys)) | yes p | no ¬p = no (¬p ∘ proj₂)
  ((x , xs) ≟ (y , ys)) | no ¬p = no (¬p ∘ proj₁)

  ⟦_⟧-cong : ∀ {xs ys} → xs ≈P ys → ∀ ρ → ⟦ xs ⟧ ρ ≈ ⟦ ys ⟧ ρ
  ⟦ x , ⟨⟩-≈ ⟧-cong ρ = x
  ⟦ x , ⟨ xs ⟩-≈ ⟧-cong ρ = +-cong x (*-cong (⟦ xs ⟧-cong ρ) refl)

  cons-normalising : Carrier → Terms → Terms
  cons-normalising x xs with x ≟C 0#
  cons-normalising x ⟨⟩ | yes p = ⟨⟩
  cons-normalising x ⟨ xs ⟩ | yes p = ⟨ x , ⟨ xs ⟩ ⟩
  cons-normalising x xs | no ¬p = ⟨ x , xs ⟩

  open import SemiringReasoning commutativeSemiring

  cons-normalising-hom : ∀ z x xs ρ → ⟦ z , ⟨ x , xs ⟩ ⟧ ρ ≈ ⟦ z , cons-normalising x xs ⟧ ρ
  cons-normalising-hom z x xs ρ with x ≟C 0#
  cons-normalising-hom z x ⟨⟩ ρ | yes p =
    begin
      z + x * ρ
    ≈⟨ ⋯+⟨ ⟨ p ⟩*⋯ ⟩ ⟩
      z + 0# * ρ
    ≈⟨ ⋯+⟨ zeroˡ ρ ⟩ ⟩
      z + 0#
    ≈⟨ +-identityʳ z ⟩
      z
    ∎
  cons-normalising-hom z x ⟨ xs ⟩ ρ | yes p = refl
  cons-normalising-hom z x xs ρ | no ¬p = refl

  normalise-T : Terms → Terms
  normalise-T ⟨⟩ = ⟨⟩
  normalise-T ⟨ x , xs ⟩ = cons-normalising x (normalise-T xs)

  normalise : Poly → Poly
  normalise (x , xs) = x , normalise-T xs

  normalise-hom-T : ∀ z xs ρ → ⟦ z , xs ⟧ ρ ≈ ⟦ z , normalise-T xs ⟧ ρ
  normalise-hom-T z ⟨⟩ ρ = refl
  normalise-hom-T z ⟨ x , xs ⟩ ρ =
    begin
      z + ⟦ x , xs ⟧ ρ * ρ
    ≅⟨ sym ⟩
      ⟦ z , cons-normalising x (normalise-T xs) ⟧ ρ
    ≈⟨ sym (cons-normalising-hom z x (normalise-T xs) ρ) ⟩
      ⟦ z , ⟨ x , normalise-T xs ⟩ ⟧ ρ
    ≈⟨ ⋯+⟨ ⟨ sym (normalise-hom-T x xs ρ) ⟩*⋯ ⟩ ⟩
      ⟦ z , ⟨ x , xs ⟩ ⟧ ρ
    ∎

  normalise-hom : (xs : Poly) → (ρ : Carrier) → ⟦ xs ⟧ ρ ≈ ⟦ normalise xs ⟧ ρ
  normalise-hom (x , xs) ρ = normalise-hom-T x xs ρ

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

