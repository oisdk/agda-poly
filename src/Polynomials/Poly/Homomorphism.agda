{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
open import Relation.Binary

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Polynomials.Poly.Homomorphism
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open CommutativeSemiring commutativeSemiring
open import Polynomials.SemiringReasoning setoid _+_ _*_ +-cong *-cong
open import Polynomials.Poly commutativeSemiring _≟C_

open import Relation.Nullary
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product
import Data.Nat.Properties as ℕ-≡
import Relation.Binary.PropositionalEquality as ≡
open import Function
open import Data.List as List using (_∷_; [])
import Data.Vec as Vec

pow-add : ∀ x i j → x ^ i * x ^ j ≈ x ^ (i ℕ.+ j)
pow-add x zero j = *-identityˡ (x ^ j)
pow-add x (suc i) j =
  begin
    x ^ suc i * x ^ j
  ≡⟨⟩
    (x * x ^ i) * x ^ j
  ≈⟨ *-assoc x _ _ ⟩
    x * (x ^ i * x ^ j)
  ≈⟨ *≫ pow-add x i j ⟩
    x * x ^ (i ℕ.+ j)
  ≡⟨⟩
    x ^ suc (i ℕ.+ j)
  ∎

-- pow-hom : ∀ n i (xs : Poly n) ρ → ⟦ xs ⟧ ρ * Vec.map (λ x → x ^ i) ρ ≈ ⟦ xs ⍓ i ⟧ ρ
-- pow-hom i [] ρ = zeroˡ (ρ ^ i)
-- pow-hom i ((x , j) ∷ xs) ρ = *-assoc _ (ρ ^ j) (ρ ^ i) ︔ *≫ pow-add ρ j i

-- ∷↓-hom : ∀ x i xs ρ → ⟦ (x , i) ∷↓ xs ⟧ ρ ≈ (x + ⟦ xs ⟧ ρ * ρ) * ρ ^ i
-- ∷↓-hom x i xs ρ with x ≟C 0#
-- ∷↓-hom x i xs ρ | no ¬p = refl
-- ∷↓-hom x i xs ρ | yes p =
--   begin
--     ⟦ xs ⍓ suc i ⟧ ρ
--   ≈⟨ sym (pow-hom _ xs ρ) ⟩
--     ⟦ xs ⟧ ρ * ρ ^ (suc i)
--   ≈⟨ sym (*-assoc _ ρ _) ⟩
--     ⟦ xs ⟧ ρ * ρ * ρ ^ i
--   ≈⟨ ≪* (sym (+-identityˡ _) ︔ ≪+ sym p) ⟩
--     (x + ⟦ xs ⟧ ρ * ρ) * ρ ^ i
--   ∎

-- ⊞-hom : ∀ xs ys ρ → ⟦ xs ⊞ ys ⟧ ρ ≈ ⟦ xs ⟧ ρ + ⟦ ys ⟧ ρ

-- ⊞-ne-hom : ∀ {i j}
--          → (c : ℕ.Ordering i j)
--          → ∀ x → .(x≠0 : x ≉0) → ∀ xs y → .(y≠0 : y ≉0) → ∀ ys ρ
--          → ⟦ ⊞-ne c x x≠0 xs y y≠0 ys ⟧ ρ ≈ ⟦ ((x ^^ i ⦅ x≠0 ⦆) ∷ xs) ⟧ ρ + ⟦ (y ^^ j ⦅ y≠0 ⦆) ∷ ys ⟧ ρ
-- ⊞-ne-l-hom : ∀ k xs y → .(y≠0 : y ≉0) → ∀ ys ρ → ⟦ ⊞-ne-l k xs y y≠0 ys ⟧ ρ ≈ ⟦ xs ⟧ ρ + ⟦ (y ^^ k ⦅ y≠0 ⦆) ∷ ys ⟧ ρ
-- ⊞-ne-r-hom : ∀ k x → .(x≠0 : x ≉0) → ∀ xs ys ρ → ⟦ ⊞-ne-r k x x≠0 xs ys ⟧ ρ ≈ ⟦ (x ^^ k ⦅ x≠0 ⦆) ∷ xs ⟧ ρ + ⟦ ys ⟧ ρ

-- ⊞-ne-l-hom k [] y y≠0 ys ρ = sym (+-identityˡ _)
-- ⊞-ne-l-hom k ((x ^^ i ⦅ x≠0 ⦆) ∷ xs) y y≠0 ys ρ = ⊞-ne-hom (ℕ.compare i k) x x≠0 xs y y≠0 ys ρ

-- ⊞-ne-r-hom k x x≠0 xs [] ρ = sym (+-identityʳ _)
-- ⊞-ne-r-hom k x x≠0 xs ((y ^^ j ⦅ y≠0 ⦆) ∷ ys) ρ = ⊞-ne-hom (ℕ.compare k j) x x≠0 xs y y≠0 ys ρ

-- ⊞-ne-hom (ℕ.equal i) x x≠0 xs y y≠0 ys ρ =
--   begin
--     ⟦ (x + y , i) ∷↓ xs ⊞ ys ⟧ ρ
--   ≈⟨ (∷↓-hom (x + y) i (xs ⊞ ys) ρ) ⟩
--     ((x + y) + ⟦ xs ⊞ ys ⟧ ρ * ρ) * ρ ^ i
--   ≈⟨ ≪* begin
--          (x + y) + ⟦ xs ⊞ ys ⟧ ρ * ρ
--        ≈⟨ +≫ ≪* ⊞-hom xs ys ρ ⟩
--          (x + y) + (⟦ xs ⟧ ρ + ⟦ ys ⟧ ρ) * ρ
--        ≈⟨ +≫ distribʳ ρ _ _ ⟩
--          (x + y) + (⟦ xs ⟧ ρ * ρ + ⟦ ys ⟧ ρ * ρ)
--        ≈⟨ +-assoc x y _ ⟩
--          x + (y + (⟦ xs ⟧ ρ * ρ + ⟦ ys ⟧ ρ * ρ))
--        ≈⟨ +≫ sym ( +-assoc y _ _ ) ⟩
--          x + ((y + ⟦ xs ⟧ ρ * ρ) + ⟦ ys ⟧ ρ * ρ)
--        ≈⟨ +≫ ≪+ +-comm y _ ⟩
--          x + ((⟦ xs ⟧ ρ * ρ + y) + ⟦ ys ⟧ ρ * ρ)
--        ≈⟨ +≫ +-assoc _ y _ ⟩
--          x + (⟦ xs ⟧ ρ * ρ + (y + ⟦ ys ⟧ ρ * ρ))
--        ≈⟨ sym (+-assoc x _ _) ⟩
--          (x + ⟦ xs ⟧ ρ * ρ) + (y + ⟦ ys ⟧ ρ * ρ)
--        ∎
--    ⟩
--     ((x + ⟦ xs ⟧ ρ * ρ) + (y + ⟦ ys ⟧ ρ * ρ)) * ρ ^ i
--   ≈⟨ distribʳ (ρ ^ i) _ _ ⟩
--     (x + ⟦ xs ⟧ ρ * ρ) * ρ ^ i + (y + ⟦ ys ⟧ ρ * ρ) * ρ ^ i
--   ∎
-- ⊞-ne-hom (ℕ.less i k) x x≠0 xs y y≠0 ys ρ =
--   begin
--     (x + ⟦ ⊞-ne-l k xs y y≠0 ys ⟧ ρ * ρ) * ρ ^ i
--   ≈⟨ ≪* +≫ ≪* ⊞-ne-l-hom k xs y y≠0 ys ρ ⟩
--     (x + (⟦ xs ⟧ ρ + ⟦ (y ^^ k ⦅ y≠0 ⦆) ∷ ys ⟧ ρ) * ρ) * ρ ^ i
--   ≈⟨ ≪* +≫ distribʳ ρ _ _ ⟩
--     (x + (⟦ xs ⟧ ρ * ρ + ⟦ (y ^^ k ⦅ y≠0 ⦆) ∷ ys ⟧ ρ * ρ)) * ρ ^ i
--   ≈⟨ ≪* sym (+-assoc x _ _) ⟩
--     (x + ⟦ xs ⟧ ρ * ρ + ⟦ (y ^^ k ⦅ y≠0 ⦆) ∷ ys ⟧ ρ * ρ) * ρ ^ i
--   ≈⟨ distribʳ (ρ ^ i) _ _ ⟩
--     ⟦ (x ^^ i ⦅ x≠0 ⦆) ∷ xs ⟧ ρ + ⟦ (y ^^ k ⦅ y≠0 ⦆) ∷ ys ⟧ ρ * ρ * ρ ^ i
--   ≈⟨ +≫ (*-assoc _ ρ (ρ ^ i) ︔ *-assoc _ (ρ ^ k) (ρ ^ suc i) ︔ *≫ pow-add _ k (suc i))⟩
--     ⟦ (x ^^ i ⦅ x≠0 ⦆) ∷ xs ⟧ ρ + ⟦ (y ^^ (k ℕ.+ suc i) ⦅ y≠0 ⦆) ∷ ys ⟧ ρ
--   ≡⟨ ≡.cong (λ ik → ⟦ (x ^^ i ⦅ x≠0 ⦆) ∷ xs ⟧ ρ + ⟦ (y ^^ ik ⦅ y≠0 ⦆) ∷ ys ⟧ ρ) (ℕ-≡.+-comm k (suc i)) ⟩
--     ⟦ (x ^^ i ⦅ x≠0 ⦆) ∷ xs ⟧ ρ + ⟦ (y ^^ suc (i ℕ.+ k) ⦅ y≠0 ⦆) ∷ ys ⟧ ρ
--   ∎
-- ⊞-ne-hom (ℕ.greater j k) x x≠0 xs y y≠0 ys ρ =
--   begin
--     ⟦ (y ^^ j ⦅ y≠0 ⦆) ∷ ⊞-ne-r k x x≠0 xs ys ⟧ ρ
--   ≡⟨⟩
--     (y + ⟦ ⊞-ne-r k x x≠0 xs ys ⟧ ρ * ρ) * ρ ^ j
--   ≈⟨ ≪* +≫ ≪* (⊞-ne-r-hom k x x≠0 xs ys ρ ︔ +-comm _ _) ⟩
--     (y + (⟦ ys ⟧ ρ + ⟦ (x ^^ k ⦅ x≠0 ⦆) ∷ xs ⟧ ρ) * ρ) * ρ ^ j
--   ≈⟨ ≪* +≫ distribʳ ρ _ _ ⟩
--     (y + (⟦ ys ⟧ ρ * ρ + ⟦ (x ^^ k ⦅ x≠0 ⦆) ∷ xs ⟧ ρ * ρ)) * ρ ^ j
--   ≈⟨ ≪* sym (+-assoc _ _ _) ⟩
--     (y + ⟦ ys ⟧ ρ * ρ + ⟦ (x ^^ k ⦅ x≠0 ⦆) ∷ xs ⟧ ρ * ρ) * ρ ^ j
--   ≈⟨ distribʳ (ρ ^ j) _ _ ⟩
--     ⟦ (y ^^ j ⦅ y≠0 ⦆) ∷ ys ⟧ ρ + (⟦ (x ^^ k ⦅ x≠0 ⦆) ∷ xs ⟧ ρ * ρ) * ρ ^ j
--   ≈⟨ +≫ *-assoc _ ρ _ ⟩
--     ⟦ (y ^^ j ⦅ y≠0 ⦆) ∷ ys ⟧ ρ + ⟦ (x ^^ k ⦅ x≠0 ⦆) ∷ xs ⟧ ρ * ρ ^ suc j
--   ≈⟨ +≫ (*-assoc _ _ _ ︔ *≫ pow-add _ k (suc j)) ⟩
--     ⟦ (y ^^ j ⦅ y≠0 ⦆) ∷ ys ⟧ ρ + ⟦ (x ^^ (k ℕ.+ suc j) ⦅ x≠0 ⦆) ∷ xs ⟧ ρ
--   ≈⟨ +-comm _ _ ⟩
--     ⟦ (x ^^ (k ℕ.+ suc j) ⦅ x≠0 ⦆) ∷ xs ⟧ ρ + ⟦ (y ^^ j ⦅ y≠0 ⦆) ∷ ys ⟧ ρ
--   ≡⟨ ≡.cong (λ kj → ⟦ x ^^ kj ⦅ x≠0 ⦆ ∷ xs ⟧ ρ + ⟦ (y ^^ j ⦅ y≠0 ⦆) ∷ ys ⟧ ρ) (ℕ-≡.+-comm k (suc j)) ⟩
--     ⟦ x ^^ suc (j ℕ.+ k) ⦅ x≠0 ⦆ ∷ xs ⟧ ρ + ⟦ (y ^^ j ⦅ y≠0 ⦆) ∷ ys ⟧ ρ
--   ∎

-- ⊞-hom [] ys ρ = sym (+-identityˡ (⟦ ys ⟧ ρ))
-- ⊞-hom (x ∷ xs) [] ρ = sym (+-identityʳ (⟦ x ∷ xs ⟧ ρ))
-- ⊞-hom ((x ^^ i ⦅ x≠0 ⦆) ∷ xs) ((y ^^ j ⦅ y≠0 ⦆) ∷ ys) ρ = ⊞-ne-hom (ℕ.compare i j) x x≠0 xs y y≠0 ys ρ

-- -- for multiplication, we will first prove this smaller lemma.
-- ⋊-hom : ∀ x ys ρ → ⟦ x ⋊ ys ⟧ ρ ≈ x * ⟦ ys ⟧ ρ
-- ⋊-hom x [] ρ = sym (zeroʳ x)
-- ⋊-hom x ((y ^^ j ⦅ y≠0 ⦆) ∷ ys) ρ =
--   begin
--     ⟦ x ⋊ ((y ^^ j ⦅ y≠0 ⦆) ∷ ys) ⟧ ρ
--   ≡⟨⟩
--     ⟦ (x * y , j) ∷↓ x ⋊ ys ⟧ ρ
--   ≈⟨ ∷↓-hom (x * y) j (x ⋊ ys) ρ ⟩
--     (x * y + ⟦ x ⋊ ys ⟧ ρ * ρ) * ρ ^ j
--   ≈⟨ ≪* +≫ ≪* ⋊-hom x ys ρ ⟩
--     (x * y + x * ⟦ ys ⟧ ρ * ρ) * ρ ^ j
--   ≈⟨ ≪* +≫ *-assoc _ _ _ ⟩
--     (x * y + x * (⟦ ys ⟧ ρ * ρ)) * ρ ^ j
--   ≈⟨ ≪* sym (distribˡ x _ _) ⟩
--     x * (y + ⟦ ys ⟧ ρ * ρ) * ρ ^ j
--   ≈⟨ *-assoc _ _ _ ⟩
--     x * ⟦ (y ^^ j ⦅ y≠0 ⦆) ∷ ys ⟧ ρ
--   ∎

-- *-hom : ∀ xs ys ρ → ⟦ xs ⊠ ys ⟧ ρ ≈ ⟦ xs ⟧ ρ * ⟦ ys ⟧ ρ
-- *-hom [] ys ρ = sym (zeroˡ _)
-- *-hom (x ∷ xs) [] ρ = sym (zeroʳ _)
-- *-hom ((x ^^ i ⦅ x≠0 ⦆) ∷ xs) ((y ^^ j ⦅ y≠0 ⦆) ∷ ys) ρ =
--   begin
--     ⟦ ((x ^^ i ⦅ x≠0 ⦆) ∷ xs) ⊠ ((y ^^ j ⦅ y≠0 ⦆) ∷ ys) ⟧ ρ
--   ≡⟨⟩
--     ⟦ (x * y , i ℕ.+ j) ∷↓ x ⋊ ys ⊞ xs ⊠ ((y ^^ 0 ⦅ y≠0 ⦆) ∷ ys) ⟧ ρ
--   ≈⟨ ∷↓-hom _ _ _ ρ ⟩
--     (x * y + ⟦ x ⋊ ys ⊞ xs ⊠ ((y ^^ 0 ⦅ y≠0 ⦆) ∷ ys) ⟧ ρ * ρ) * ρ ^ (i ℕ.+ j)
--   ≈⟨ ≪* +≫ ≪* (⊞-hom (x ⋊ ys) _ ρ  ︔ (⋊-hom x ys ρ ⟨ +-cong ⟩ *-hom xs _ ρ)) ⟩
--     (x * y + (x * ⟦ ys ⟧ ρ + ⟦ xs ⟧ ρ * ⟦ y ^^ 0 ⦅ y≠0 ⦆ ∷ ys ⟧ ρ) * ρ) * ρ ^ (i ℕ.+ j)
--   ≈⟨ ≪* +≫ distribʳ ρ _ _ ⟩
--     (x * y + (x * ⟦ ys ⟧ ρ * ρ + ⟦ xs ⟧ ρ * ⟦ y ^^ 0 ⦅ y≠0 ⦆ ∷ ys ⟧ ρ * ρ)) * ρ ^ (i ℕ.+ j)
--   ≈⟨ ≪* sym (+-assoc (x * y) _ _) ⟩
--     (x * y + x * ⟦ ys ⟧ ρ * ρ + ⟦ xs ⟧ ρ * ⟦ y ^^ 0 ⦅ y≠0 ⦆ ∷ ys ⟧ ρ * ρ) * ρ ^ (i ℕ.+ j)
--   ≈⟨ ≪* ≪+ (+≫ *-assoc x _ ρ ︔ sym (distribˡ x _ _)) ⟩
--     (x * (y + ⟦ ys ⟧ ρ * ρ) + ⟦ xs ⟧ ρ * ⟦ y ^^ 0 ⦅ y≠0 ⦆ ∷ ys ⟧ ρ * ρ) * ρ ^ (i ℕ.+ j)
--   ≡⟨ ≡.cong (λ ij → (x * (y + ⟦ ys ⟧ ρ * ρ) + ⟦ xs ⟧ ρ * ⟦ y ^^ 0 ⦅ y≠0 ⦆ ∷ ys ⟧ ρ * ρ) * ρ ^ ij) (ℕ-≡.+-comm i j) ⟩
--     (x * (y + ⟦ ys ⟧ ρ * ρ) + ⟦ xs ⟧ ρ * ⟦ y ^^ 0 ⦅ y≠0 ⦆ ∷ ys ⟧ ρ * ρ) * ρ ^ (j ℕ.+ i)
--   ≈⟨ *≫ sym (pow-add ρ j i) ⟩
--     (x * (y + ⟦ ys ⟧ ρ * ρ) + ⟦ xs ⟧ ρ * ⟦ y ^^ 0 ⦅ y≠0 ⦆ ∷ ys ⟧ ρ * ρ) * (ρ ^ j * ρ ^ i)
--   ≈⟨ sym (*-assoc _ _ _) ⟩
--     (x * (y + ⟦ ys ⟧ ρ * ρ) + ⟦ xs ⟧ ρ * ⟦ y ^^ 0 ⦅ y≠0 ⦆ ∷ ys ⟧ ρ * ρ) * ρ ^ j * ρ ^ i
--   ≈⟨ ≪* distribʳ (ρ ^ j) _ _ ⟩
--     (x * (y + ⟦ ys ⟧ ρ * ρ) * ρ ^ j + ⟦ xs ⟧ ρ * ⟦ y ^^ 0 ⦅ y≠0 ⦆ ∷ ys ⟧ ρ * ρ * ρ ^ j) * ρ ^ i
--   ≈⟨ ≪* ≪+ (*-assoc x _ _) ⟩
--     (x * ⟦ (y ^^ j ⦅ y≠0 ⦆) ∷ ys ⟧ ρ + ((⟦ xs ⟧ ρ * ⟦ y ^^ 0 ⦅ y≠0 ⦆ ∷ ys ⟧ ρ) * ρ) * ρ ^ j) * ρ ^ i
--   ≈⟨ ≪* +≫ ( ≪* ( *-assoc _ _ ρ ︔ *≫ *-comm _ _ ︔ sym (*-assoc _ _ _) ) ︔ *-assoc _ _ _ ) ⟩
--     (x * ⟦ (y ^^ j ⦅ y≠0 ⦆) ∷ ys ⟧ ρ + (⟦ xs ⟧ ρ * ρ) * (⟦ y ^^ 0 ⦅ y≠0 ⦆ ∷ ys ⟧ ρ * ρ ^ j)) * ρ ^ i
--   ≈⟨ ≪* +≫ *≫ (*-assoc _ _ _ ︔ *≫ *-identityˡ (ρ ^ j))⟩
--     (x * ⟦ (y ^^ j ⦅ y≠0 ⦆) ∷ ys ⟧ ρ + (⟦ xs ⟧ ρ * ρ) * ⟦ (y ^^ j ⦅ y≠0 ⦆) ∷ ys ⟧ ρ) * ρ ^ i
--   ≈⟨ ≪* sym (distribʳ _ x _) ⟩
--     (x + ⟦ xs ⟧ ρ * ρ) * ⟦ (y ^^ j ⦅ y≠0 ⦆) ∷ ys ⟧ ρ * ρ ^ i
--   ≈⟨ *-assoc _ _ (ρ ^ i) ︔ *≫ *-comm _ (ρ ^ i) ︔ sym (*-assoc _ _ _) ⟩
--     (x + ⟦ xs ⟧ ρ * ρ) * ρ ^ i * ⟦ (y ^^ j ⦅ y≠0 ⦆) ∷ ys ⟧ ρ
--   ≡⟨⟩
--     ⟦ ((x ^^ i ⦅ x≠0 ⦆) ∷ xs) ⟧ ρ * ⟦ (y ^^ j ⦅ y≠0 ⦆) ∷ ys ⟧ ρ
--   ∎

-- κ-hom : ∀ x ρ → ⟦ κ x ⟧ ρ ≈ x
-- κ-hom x ρ =
--   begin
--     ⟦ κ x ⟧ ρ
--   ≈⟨ ∷↓-hom _ _ _ ρ ⟩
--     (x + 0# * ρ) * ρ ^ 0
--   ≈⟨ *-identityʳ _ ⟩
--     x + 0# * ρ
--   ≈⟨ +≫ zeroˡ ρ ⟩
--     x + 0#
--   ≈⟨ +-identityʳ x ⟩
--     x
--   ∎

-- ι-hom : ∀ ρ → ⟦ ι ⟧ ρ ≈ ρ
-- ι-hom ρ =
--   begin
--     ⟦ ι ⟧ ρ
--   ≈⟨ ∷↓-hom _ _ _ ρ ⟩
--     (1# + 0# * ρ) * ρ ^ 1
--   ≈⟨ (+≫ zeroˡ ρ ︔ +-identityʳ 1#) ⟨ *-cong ⟩ *-identityʳ ρ ⟩
--     1# * ρ
--   ≈⟨ *-identityˡ ρ ⟩
--     ρ
--   ∎
