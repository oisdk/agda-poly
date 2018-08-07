{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
import Level
open import Function
open import Relation.Binary

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Sparse.Homomorphism
  (commutativeSemiring : CommutativeSemiring Level.zero Level.zero)
  where

open CommutativeSemiring commutativeSemiring hiding (zero)
open import Sparse commutativeSemiring
open import SemiringReasoning commutativeSemiring
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product
import Data.Nat.Properties as ℕ-≡
import Relation.Binary.PropositionalEquality as ≡

pow-add : ∀ x i j → x ^ i * x ^ j ≈ x ^ (i ℕ.+ j)
pow-add x zero j = *-identityˡ (x ^ j)
pow-add x (suc i) j =
  begin
    x ^ suc i * x ^ j
  ≡⟨⟩
    (x * x ^ i) * x ^ j
  ≈⟨ *-assoc x _ _ ⟩
    x * (x ^ i * x ^ j)
  ≈⟨ ⋯*⟨ pow-add x i j ⟩ ⟩
    x * x ^ (i ℕ.+ j)
  ≡⟨⟩
    x ^ suc (i ℕ.+ j)
  ∎

+-hom : ∀ xs ys ρ → ⟦ xs ⊞ ys ⟧ ρ ≈ ⟦ xs ⟧ ρ + ⟦ ys ⟧ ρ
⊞-ne-hom : ∀ {i j} → (c : ℕ.Ordering i j) → ∀ x xs y ys ρ → ⟦ ⊞-ne c x xs y ys ⟧ ρ ≈ ⟦ ((i , x) ∷ xs) ⟧ ρ + ⟦ ((j , y) ∷ ys) ⟧ ρ
⊞-ne-l-hom : ∀ k xs y ys ρ → ⟦ ⊞-ne-l k xs y ys ⟧ ρ ≈ ⟦ xs ⟧ ρ + ⟦ (k , y) ∷ ys ⟧ ρ
⊞-ne-r-hom : ∀ k x xs ys ρ → ⟦ ⊞-ne-r k x xs ys ⟧ ρ ≈ ⟦ (k , x) ∷ xs ⟧ ρ + ⟦ ys ⟧ ρ

⊞-ne-l-hom k [] y ys ρ = sym (+-identityˡ _)
⊞-ne-l-hom k ((i , x) ∷ xs) y ys ρ = ⊞-ne-hom (ℕ.compare i k) x xs y ys ρ

⊞-ne-r-hom k x xs [] ρ = sym (+-identityʳ _)
⊞-ne-r-hom k x xs ((j , y) ∷ ys) ρ = ⊞-ne-hom (ℕ.compare k j) x xs y ys ρ

⊞-ne-hom (ℕ.greater j k) x xs y ys ρ = {!!}
⊞-ne-hom (ℕ.equal i) x xs y ys ρ =
  begin
    ((x + y) + ⟦ xs ⊞ ys ⟧ ρ * ρ) * ρ ^ i
  ≈⟨ ⟨ begin
         (x + y) + ⟦ xs ⊞ ys ⟧ ρ * ρ
       ≈⟨ ⋯+⟨ ⟨ +-hom xs ys ρ ⟩*⋯ ⟩ ⟩
         (x + y) + (⟦ xs ⟧ ρ + ⟦ ys ⟧ ρ) * ρ
       ≈⟨ ⋯+⟨ distribʳ ρ _ _ ⟩ ⟩
         (x + y) + (⟦ xs ⟧ ρ * ρ + ⟦ ys ⟧ ρ * ρ)
       ≈⟨ +-assoc x y _ ⟩
         x + (y + (⟦ xs ⟧ ρ * ρ + ⟦ ys ⟧ ρ * ρ))
       ≈⟨ sym ⋯+⟨ +-assoc y _ _ ⟩ ⟩
         x + ((y + ⟦ xs ⟧ ρ * ρ) + ⟦ ys ⟧ ρ * ρ)
       ≈⟨ ⋯+⟨ ⟨ +-comm y _ ⟩+⋯ ⟩ ⟩
         x + ((⟦ xs ⟧ ρ * ρ + y) + ⟦ ys ⟧ ρ * ρ)
       ≈⟨ ⋯+⟨ +-assoc _ y _ ⟩ ⟩
         x + (⟦ xs ⟧ ρ * ρ + (y + ⟦ ys ⟧ ρ * ρ))
       ≈⟨ sym (+-assoc x _ _) ⟩
         (x + ⟦ xs ⟧ ρ * ρ) + (y + ⟦ ys ⟧ ρ * ρ)
       ∎
  ⟩*⋯ ⟩
    ((x + ⟦ xs ⟧ ρ * ρ) + (y + ⟦ ys ⟧ ρ * ρ)) * ρ ^ i
  ≈⟨ distribʳ (ρ ^ i) _ _ ⟩
    (x + ⟦ xs ⟧ ρ * ρ) * ρ ^ i + (y + ⟦ ys ⟧ ρ * ρ) * ρ ^ i
  ∎
⊞-ne-hom (ℕ.less i k) x xs y ys ρ =
  begin
    ⟦ (i , x) ∷ ⊞-ne-l k xs y ys ⟧ ρ
  ≡⟨⟩
    (x + ⟦ ⊞-ne-l k xs y ys ⟧ ρ * ρ) * ρ ^ i
  ≈⟨ ⟨ ⋯+⟨ ⟨ ⊞-ne-l-hom k xs y ys ρ ⟩*⋯ ⟩ ⟩*⋯ ⟩
    (x + (⟦ xs ⟧ ρ + (y + ⟦ ys ⟧ ρ * ρ) * ρ ^ k) * ρ) * ρ ^ i
  ≈⟨ distribʳ (ρ ^ i) x _ ⟩
    x * ρ ^ i + (⟦ xs ⟧ ρ + (y + ⟦ ys ⟧ ρ * ρ) * ρ ^ k) * ρ * ρ ^ i
  ≈⟨ ⋯+⟨ *-assoc _ ρ _ ⟩ ⟩
    x * ρ ^ i + (⟦ xs ⟧ ρ + (y + ⟦ ys ⟧ ρ * ρ) * ρ ^ k) * ρ ^ suc i
  ≈⟨ ⋯+⟨ distribʳ (ρ ^ suc i) _ _ ⟩ ⟩
    x * ρ ^ i + (⟦ xs ⟧ ρ * ρ ^ suc i + ((y + ⟦ ys ⟧ ρ * ρ) * ρ ^ k) * ρ ^ suc i)
  ≈⟨ sym (+-assoc (x * ρ ^ i) _ _) ⟩
    x * ρ ^ i + ⟦ xs ⟧ ρ * ρ ^ suc i + ((y + ⟦ ys ⟧ ρ * ρ) * ρ ^ k) * ρ ^ suc i
  ≈⟨ ⟨ ⋯+⟨ sym (*-assoc _ ρ _ ) ⟩ ︔ sym (distribʳ (ρ ^ i) _ _ )⟩+⋯ ⟩
    ⟦ (i , x) ∷ xs ⟧ ρ + ((y + ⟦ ys ⟧ ρ * ρ) * ρ ^ k) * ρ ^ suc i
  ≈⟨ ⋯+⟨ *-assoc _ _ _ ⟩ ⟩
    ⟦ (i , x) ∷ xs ⟧ ρ + (y + ⟦ ys ⟧ ρ * ρ) * ((ρ ^ k) * ρ ^ suc i)
  ≈⟨ ⋯+⟨ ⋯*⟨ pow-add ρ k (suc i) ⟩ ⟩ ⟩
    ⟦ (i , x) ∷ xs ⟧ ρ + ⟦ (k ℕ.+ suc i , y) ∷ ys ⟧ ρ
  ≡⟨ ≡.cong (λ ik → ⟦ (i , x) ∷ xs ⟧ ρ + ⟦ (ik , y) ∷ ys ⟧ ρ) (ℕ-≡.+-comm k (suc i)) ⟩
    ⟦ (i , x) ∷ xs ⟧ ρ + ⟦ (suc (i ℕ.+ k) , y) ∷ ys ⟧ ρ
  ∎

+-hom [] ys ρ = sym (+-identityˡ (⟦ ys ⟧ ρ))
+-hom (x ∷ xs) [] ρ = sym (+-identityʳ (⟦ x ∷ xs ⟧ ρ))
+-hom ((i , x) ∷ xs) ((j , y) ∷ ys) ρ = ⊞-ne-hom (ℕ.compare i j) x xs y ys ρ
