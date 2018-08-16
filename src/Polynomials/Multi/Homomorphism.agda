{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
open import Relation.Binary

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Polynomials.Multi.Homomorphism
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open CommutativeSemiring commutativeSemiring
open import Polynomials.SemiringReasoning setoid _+_ _*_ +-cong *-cong
open import Polynomials.Multi commutativeSemiring _≟C_

open import Relation.Nullary
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product
import Data.Nat.Properties as ℕ-≡
import Relation.Binary.PropositionalEquality as ≡
open import Function
open import Data.List as List using (_∷_; [])
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Polynomials.Irrelevant.Product
open import Level using (Lift; lower; lift)

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

pow-hom : ∀ {n} i → (xs : Poly (suc n)) → ∀ ρ → (Ρ : Vec Carrier n) → ⟦ xs ⟧ (ρ ∷ Ρ) * ρ ^ i ≈ ⟦ xs ⍓ i ⟧ (ρ ∷ Ρ)
pow-hom i [] ρ Ρ = zeroˡ (ρ ^ i)
pow-hom i ((x , j) ∷ xs) ρ Ρ = *-assoc _ (ρ ^ j) (ρ ^ i) ︔ *≫ pow-add ρ j i

zero-hom : ∀ {n} (p : Poly n) → Zero n p → (Ρ : Vec Carrier n) → ⟦ p ⟧ Ρ ≈ 0#
zero-hom {zero} (lift p) p=0 [] = p=0
zero-hom {suc n} [] p=0 (x ∷ Ρ) = refl
zero-hom {suc n} (x ∷ p) (lift ()) Ρ

∷↓-hom : ∀ {n}
       → (x : Poly n)
       → (i : ℕ)
       → (xs : Poly (suc n))
       → (ρ : Carrier)
       → (Ρ : Vec Carrier n)
       → ⟦ (x , i) ∷↓ xs ⟧ (ρ ∷ Ρ) ≈ (⟦ x ⟧ Ρ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
∷↓-hom x i xs ρ Ρ with zero? x
∷↓-hom x i xs ρ Ρ | no ¬p = refl
∷↓-hom x i xs ρ Ρ | yes p =
  begin
    ⟦ xs ⍓ suc i ⟧ (ρ ∷ Ρ)
  ≈⟨ sym (pow-hom _ xs ρ Ρ) ⟩
    ⟦ xs ⟧ (ρ ∷ Ρ) * ρ ^ (suc i)
  ≈⟨ sym (*-assoc _ ρ _) ⟩
    ⟦ xs ⟧ (ρ ∷ Ρ) * ρ * ρ ^ i
  ≈⟨ ≪* (sym (+-identityˡ _) ︔ ≪+ sym (zero-hom x p _)) ⟩
    (⟦ x ⟧ Ρ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
  ∎
