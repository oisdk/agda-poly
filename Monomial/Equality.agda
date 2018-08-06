{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
import Level
open import Data.Product
open import Function
open import Relation.Binary

----------------------------------------------------------------------
-- Equality
----------------------------------------------------------------------
module Monomial.Equality
  (commutativeSemiring : CommutativeSemiring Level.zero Level.zero)
  where

open CommutativeSemiring commutativeSemiring
open import Monomial commutativeSemiring
open import SemiringReasoning commutativeSemiring
open import Relation.Nullary

module Truncating where
  data _≈0 : Poly → Set where
    []≈0 : [] ≈0
    ⟨_,_⟩≈0 : ∀ {x xs} → x ≈ 0# → xs ≈0 → (x ∷ xs) ≈0

  -- Equality relations. These are normalising.
  data _≈P_ : Poly → Poly → Set where
    ⟨_⟩≈0≈⟨_⟩ : ∀ {xs ys} → xs ≈0 → ys ≈0 → xs ≈P ys
    ⟨_,_⟩-≈ : ∀ {x y xs ys} → x ≈ y → xs ≈P ys → (x ∷ xs) ≈P (y ∷ ys)

  0-is-0 : ∀ xs → xs ≈0 → ∀ ρ → ⟦ xs ⟧ ρ ≈ 0#
  0-is-0 [] []≈0 ρ = refl
  0-is-0 (x ∷ xs) ⟨ p , ps ⟩≈0 ρ =
    begin
      ⟦ x ∷ xs ⟧ ρ
    ≡⟨⟩
      x + ⟦ xs ⟧ ρ * ρ
    ≈⟨ ⟨ p ⟩+⋯ ⟩
      0# + ⟦ xs ⟧ ρ * ρ
    ≈⟨ +-identityˡ _ ⟩
      ⟦ xs ⟧ ρ * ρ
    ≈⟨ ⟨ 0-is-0 xs ps ρ ⟩*⋯ ⟩
      0# * ρ
    ≈⟨ zeroˡ ρ ⟩
      0#
    ∎

  ⟦_⟧-cong : ∀ {xs ys} → xs ≈P ys → ∀ ρ → ⟦ xs ⟧ ρ ≈ ⟦ ys ⟧ ρ
  ⟦ ⟨ xs ⟩≈0≈⟨ ys ⟩ ⟧-cong ρ = 0-is-0 _ xs ρ ︔ sym (0-is-0 _ ys ρ)
  ⟦ ⟨ x , xs ⟩-≈ ⟧-cong ρ = +-cong x (*-cong (⟦ xs ⟧-cong ρ) refl)

  module Decidable
    (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
    where
    _≈0? : ∀ xs → Dec (xs ≈0)
    (x ∷ xs) ≈0? with x ≟C 0#
    (x ∷ xs) ≈0? | yes p with xs ≈0?
    (x ∷ xs) ≈0? | yes p | yes ps = yes ⟨ p , ps ⟩≈0
    (x ∷ xs) ≈0? | yes p | no ¬ps = no λ { ⟨ y , ys ⟩≈0 → ¬ps ys }
    (x ∷ xs) ≈0? | no ¬p = no λ { ⟨ y , ys ⟩≈0 → ¬p y }
    [] ≈0? = yes []≈0

    _≟_ : ∀ xs ys → Dec (xs ≈P ys)
    [] ≟ ys with ys ≈0?
    [] ≟ ys | yes p = yes ⟨ []≈0 ⟩≈0≈⟨ p ⟩
    [] ≟ ys | no ¬p = no λ { ⟨ _ ⟩≈0≈⟨ p ⟩ → ¬p p }
    (x ∷ xs) ≟ [] with (x ∷ xs) ≈0?
    (x ∷ xs) ≟ [] | yes p = yes ⟨ p ⟩≈0≈⟨ []≈0 ⟩
    (x ∷ xs) ≟ [] | no ¬p = no λ { ⟨ p ⟩≈0≈⟨ _ ⟩ → ¬p p }
    (x ∷ xs) ≟ (y ∷ ys) with x ≟C y
    (x ∷ xs) ≟ (y ∷ ys) | yes p with xs ≟ ys
    (x ∷ xs) ≟ (y ∷ ys) | yes p | yes ps = yes ⟨ p , ps ⟩-≈
    (x ∷ xs) ≟ (y ∷ ys) | yes p | no ¬ps = no
      λ { ⟨ ⟨ xz , xsz ⟩≈0 ⟩≈0≈⟨ ⟨ yz , ysz ⟩≈0 ⟩ → ¬ps ⟨ xsz ⟩≈0≈⟨ ysz ⟩
        ; ⟨ e , es ⟩-≈ → ¬ps es }
    (x ∷ xs) ≟ (y ∷ ys) | no ¬p = no
      λ { ⟨ e , es ⟩-≈ → ¬p e
        ; ⟨ ⟨ xz , xsz ⟩≈0 ⟩≈0≈⟨ ⟨ yz , ysz ⟩≈0 ⟩ → ¬p (xz ︔ sym yz)
        }

-- module Propositional where
--   ----------------------------------------------------------------------
--   -- Non-normalising equality relations. (Are these called
--   -- "propositional?")
--   ----------------------------------------------------------------------
--   data _≈P_ : Poly → Poly → Set where
--     []-≈  : [] ≈P []
--     ⟨_⟩-≈ : ∀ {xs ys} → xs ≈P ys → ⟨ xs ⟩ ≈P ⟨ ys ⟩
--   (x , xs) ≈P (y , ys) = (x ≈ y) × (xs ≈P ys)

--   ⟦_⟧-cong : ∀ {xs ys} → xs ≈P ys → ∀ ρ → ⟦ xs ⟧ ρ ≈ ⟦ ys ⟧ ρ
--   ⟦ x , []-≈ ⟧-cong ρ = x
--   ⟦ x , ⟨ xs ⟩-≈ ⟧-cong ρ = +-cong x (*-cong (⟦ xs ⟧-cong ρ) refl)

--   module Decidable
--     (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
--     where
--     _≟_ : ∀ xs ys → Dec (xs ≈P ys)
--     _≟_ : ∀ xs ys → Dec (xs ≈P ys)
--     (x , xs) ≟ (y , ys) with x ≟C y
--     (x , xs) ≟ (y , ys) | no ¬p = no (¬p ∘ proj₁)
--     (x , xs) ≟ (y , ys) | yes p with xs ≟ ys
--     (x , xs) ≟ (y , ys) | yes p | yes ps = yes (p , ps)
--     (x , xs) ≟ (y , ys) | yes p | no ¬ps = no (¬ps ∘ proj₂)

--     ⟨ xs ⟩ ≟ ⟨ ys ⟩ with xs ≟ ys
--     ⟨ xs ⟩ ≟ ⟨ ys ⟩ | yes p = yes ⟨ p ⟩-≈
--     ⟨ xs ⟩ ≟ ⟨ ys ⟩ | no ¬p = no λ { ⟨ p ⟩-≈ → ¬p p }
--     ⟨ xs ⟩ ≟ [] = no λ ()
--     [] ≟ ⟨ ys ⟩ = no λ ()
--     [] ≟ [] = yes []-≈
