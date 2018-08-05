{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
import Level
open import Data.Product
open import Function
open import Relation.Binary

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Monomial.Equality
  (commutativeSemiring : CommutativeSemiring Level.zero Level.zero)
  where

open CommutativeSemiring commutativeSemiring
open import Monomial commutativeSemiring
open import SemiringReasoning commutativeSemiring
open import Relation.Nullary

module Truncating where
  data 0≈ : Terms → Set where
    ⟨⟩≈0 : 0≈ ⟨⟩
    ⟨_,_⟩≈0 : ∀ {x xs} → x ≈ 0# → 0≈ xs → 0≈ ⟨ x , xs ⟩

  -- Equality relations. These are normalising.
  _≈P_ : Poly → Poly → Set
  data _≈T_ : Terms → Terms → Set where
    ⟨_⟩≈0≈⟨_⟩ : ∀ {xs ys} →  0≈ xs → 0≈ ys → xs ≈T ys
    ⟨_⟩-≈ : ∀ {xs ys} → xs ≈P ys → ⟨ xs ⟩ ≈T ⟨ ys ⟩
  (x , xs) ≈P (y , ys) = (x ≈ y) × (xs ≈T ys)

  0-is-0 : ∀ x xs → 0≈ xs → ∀ ρ → ⟦ x , xs ⟧ ρ ≈ x
  0-is-0 x ⟨ y , ys ⟩ ⟨ p , ps ⟩≈0 ρ =
    begin
      x + ⟦ y , ys ⟧ ρ * ρ
    ≈⟨ ⋯+⟨ ⟨ 0-is-0 y ys ps ρ ⟩*⋯ ⟩ ⟩
      x + y * ρ
    ≈⟨ ⋯+⟨ ⟨ p ⟩*⋯ ⟩ ⟩
      x + 0# * ρ
    ≈⟨ ⋯+⟨ zeroˡ ρ ⟩ ⟩
      x + 0#
    ≈⟨ +-identityʳ x ⟩
      x
    ∎
  0-is-0 x ⟨⟩ prf ρ = refl

  ⟦_⟧-cong : ∀ {xs ys} → xs ≈P ys → ∀ ρ → ⟦ xs ⟧ ρ ≈ ⟦ ys ⟧ ρ
  ⟦ x , ⟨ xs ⟩≈0≈⟨ ys ⟩ ⟧-cong ρ = 0-is-0 _ _ xs ρ ︔ x ︔ sym (0-is-0 _ _ ys ρ)
  ⟦ x , ⟨ xs ⟩-≈ ⟧-cong ρ = +-cong x (*-cong (⟦ xs ⟧-cong ρ) refl)

  module Decidable
    (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
    where
    _≈0? : ∀ xs → Dec (0≈ xs)
    ⟨ x , xs ⟩ ≈0? with x ≟C 0#
    ⟨ x , xs ⟩ ≈0? | yes p with xs ≈0?
    ⟨ x , xs ⟩ ≈0? | yes p | yes ps = yes ⟨ p , ps ⟩≈0
    ⟨ x , xs ⟩ ≈0? | yes p | no ¬ps = no λ { ⟨ y , ys ⟩≈0 → ¬ps ys }
    ⟨ x , xs ⟩ ≈0? | no ¬p = no λ { ⟨ y , ys ⟩≈0 → ¬p y }
    ⟨⟩ ≈0? = yes ⟨⟩≈0

    _≟_ : ∀ xs ys → Dec (xs ≈P ys)
    _≟T_ : ∀ xs ys → Dec (xs ≈T ys)
    (x , xs) ≟ (y , ys) with x ≟C y
    (x , xs) ≟ (y , ys) | no ¬p = no (¬p ∘ proj₁)
    (x , xs) ≟ (y , ys) | yes p with xs ≟T ys
    (x , xs) ≟ (y , ys) | yes p | yes ps = yes (p , ps)
    (x , xs) ≟ (y , ys) | yes p | no ¬ps = no (¬ps ∘ proj₂)

    ⟨ xs ⟩ ≟T ⟨ ys ⟩ with xs ≟ ys
    ⟨ xs ⟩ ≟T ⟨ ys ⟩ | yes p = yes ⟨ p ⟩-≈
    ⟨ xs ⟩ ≟T ⟨ ys ⟩ | no ¬p = no
      λ { ⟨ p ⟩-≈ → ¬p p
        ; ⟨ ⟨ x , xz ⟩≈0 ⟩≈0≈⟨ ⟨ y , yz ⟩≈0 ⟩ → ¬p (trans x (sym y) , ⟨ xz ⟩≈0≈⟨ yz ⟩)
        }
    ⟨ xs ⟩ ≟T ⟨⟩ with ⟨ xs ⟩ ≈0?
    ⟨ xs ⟩ ≟T ⟨⟩ | yes p = yes ⟨ p ⟩≈0≈⟨ ⟨⟩≈0 ⟩
    ⟨ xs ⟩ ≟T ⟨⟩ | no ¬p = no λ { ⟨ xsz ⟩≈0≈⟨ _ ⟩ → ¬p xsz }
    ⟨⟩ ≟T ⟨ ys ⟩ with ⟨ ys ⟩ ≈0?
    ⟨⟩ ≟T ⟨ ys ⟩ | yes p = yes ⟨ ⟨⟩≈0 ⟩≈0≈⟨ p ⟩
    ⟨⟩ ≟T ⟨ ys ⟩ | no ¬p = no λ { ⟨ _ ⟩≈0≈⟨ ysz ⟩ → ¬p ysz }
    ⟨⟩ ≟T ⟨⟩ = yes ⟨ ⟨⟩≈0 ⟩≈0≈⟨ ⟨⟩≈0 ⟩

module Propositional where
  infix 4 _≈P_ _≈T_
  _≈P_ : Poly → Poly → Set
  data _≈T_ : Terms → Terms → Set where
    ⟨⟩-≈  : ⟨⟩ ≈T ⟨⟩
    ⟨_⟩-≈ : ∀ {xs ys} → xs ≈P ys → ⟨ xs ⟩ ≈T ⟨ ys ⟩
  (x , xs) ≈P (y , ys) = (x ≈ y) × (xs ≈T ys)

  ⟦_⟧-cong : ∀ {xs ys} → xs ≈P ys → ∀ ρ → ⟦ xs ⟧ ρ ≈ ⟦ ys ⟧ ρ
  ⟦ x , ⟨⟩-≈ ⟧-cong ρ = x
  ⟦ x , ⟨ xs ⟩-≈ ⟧-cong ρ = +-cong x (*-cong (⟦ xs ⟧-cong ρ) refl)

  module Decidable
    (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
    where
    _≟_ : ∀ xs ys → Dec (xs ≈P ys)
    _≟T_ : ∀ xs ys → Dec (xs ≈T ys)
    (x , xs) ≟ (y , ys) with x ≟C y
    (x , xs) ≟ (y , ys) | no ¬p = no (¬p ∘ proj₁)
    (x , xs) ≟ (y , ys) | yes p with xs ≟T ys
    (x , xs) ≟ (y , ys) | yes p | yes ps = yes (p , ps)
    (x , xs) ≟ (y , ys) | yes p | no ¬ps = no (¬ps ∘ proj₂)

    ⟨ xs ⟩ ≟T ⟨ ys ⟩ with xs ≟ ys
    ⟨ xs ⟩ ≟T ⟨ ys ⟩ | yes p = yes ⟨ p ⟩-≈
    ⟨ xs ⟩ ≟T ⟨ ys ⟩ | no ¬p = no λ { ⟨ p ⟩-≈ → ¬p p }
    ⟨ xs ⟩ ≟T ⟨⟩ = no λ ()
    ⟨⟩ ≟T ⟨ ys ⟩ = no λ ()
    ⟨⟩ ≟T ⟨⟩ = yes ⟨⟩-≈
