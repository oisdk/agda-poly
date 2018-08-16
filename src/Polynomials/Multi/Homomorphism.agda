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

mutual
  ⊞-hom : ∀ {n}
        → (xs : Poly n)
        → (ys : Poly n)
        → (Ρ : Vec Carrier n)
        → ⟦ xs ⊞ ys ⟧ Ρ ≈ ⟦ xs ⟧ Ρ + ⟦ ys ⟧ Ρ
  ⊞-hom {ℕ.zero} xs ys [] = refl
  ⊞-hom {suc n} xs ys Ρ = ⊞-coeffs-hom xs ys Ρ

  ⊞-coeffs-hom : ∀ {n}
              → (xs : Coeffs n)
              → (ys : Coeffs n)
              → (Ρ : Vec Carrier (suc n))
              → ⟦ ⊞-coeffs xs ys ⟧ Ρ ≈ ⟦ xs ⟧ Ρ + ⟦ ys ⟧ Ρ
  ⊞-coeffs-hom [] ys (ρ ∷ Ρ) = sym (+-identityˡ (⟦ ys ⟧ (ρ ∷ Ρ)))
  ⊞-coeffs-hom (x ∷ xs) [] (ρ ∷ Ρ) = sym (+-identityʳ (⟦ x ∷ xs ⟧ (ρ ∷ Ρ)))
  ⊞-coeffs-hom ((x , i) ∷ xs) ((y , j) ∷ ys) Ρ = ⊞-ne-hom (ℕ.compare i j) x xs y ys Ρ

  ⊞-ne-hom : ∀ {n i j}
          → (c : ℕ.Ordering i j)
          → (x : Coeff n)
          → (xs : Coeffs n)
          → (y : Coeff n)
          → (ys : Coeffs n)
          → (Ρ : Vec Carrier (suc n))
          → ⟦ ⊞-ne c x xs y ys ⟧ Ρ ≈ ⟦ (x , i) ∷ xs ⟧ Ρ + ⟦ (y , j) ∷ ys ⟧ Ρ
  ⊞-ne-hom (ℕ.equal i) x xs y ys (ρ ∷ Ρ) =
    begin
      ⟦ (x ⊕ y , i) ∷↓ xs ⊞ ys ⟧ (ρ ∷ Ρ)
    ≈⟨ (∷↓-hom (x ⊕ y) i (xs ⊞ ys) ρ Ρ) ⟩
      (⟦ x ⊕ y ⟧ Ρ + ⟦ xs ⊞ ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
    ≈⟨ ≪* begin
            ⟦ x ⊕ y ⟧ Ρ + ⟦ xs ⊞ ys ⟧ (ρ ∷ Ρ) * ρ
          ≈⟨ +≫ ≪* ⊞-coeffs-hom xs ys (ρ ∷ Ρ) ⟩
            ⟦ x ⊕ y ⟧ Ρ + (⟦ xs ⟧ (ρ ∷ Ρ) + ⟦ ys ⟧ (ρ ∷ Ρ)) * ρ
          ≈⟨ +≫ distribʳ ρ _ _ ⟩
            ⟦ x ⊕ y ⟧ Ρ + (⟦ xs ⟧ (ρ ∷ Ρ) * ρ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ)
          ≈⟨ ≪+ ⊞-hom (fst~ x) (fst~ y) Ρ ⟩
            (⟦ fst~ x ⟧ Ρ + ⟦ fst~ y ⟧ Ρ) + (⟦ xs ⟧ (ρ ∷ Ρ) * ρ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ)
          ≈⟨ +-assoc (⟦ fst~ x ⟧ Ρ) (⟦ fst~ y ⟧ Ρ) _ ⟩
            ⟦ fst~ x ⟧ Ρ + (⟦ fst~ y ⟧ Ρ + (⟦ xs ⟧ (ρ ∷ Ρ) * ρ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ))
          ≈⟨ +≫ sym ( +-assoc (⟦ fst~ y ⟧ Ρ) _ _ ) ⟩
            ⟦ fst~ x ⟧ Ρ + ((⟦ fst~ y ⟧ Ρ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ)
          ≈⟨ +≫ ≪+ +-comm (⟦ fst~ y ⟧ Ρ) _ ⟩
            ⟦ fst~ x ⟧ Ρ + ((⟦ xs ⟧ (ρ ∷ Ρ) * ρ + ⟦ fst~ y ⟧ Ρ) + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ)
          ≈⟨ +≫ +-assoc _ (⟦ fst~ y ⟧ Ρ) _ ⟩
            ⟦ fst~ x ⟧ Ρ + (⟦ xs ⟧ (ρ ∷ Ρ) * ρ + (⟦ fst~ y ⟧ Ρ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ))
          ≈⟨ sym (+-assoc (⟦ fst~ x ⟧ Ρ) _ _) ⟩
            (⟦ fst~ x ⟧ Ρ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) + (⟦ fst~ y ⟧ Ρ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ)
          ∎
    ⟩
      ((⟦ fst~ x ⟧ Ρ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) + (⟦ fst~ y ⟧ Ρ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ)) * ρ ^ i
    ≈⟨ distribʳ (ρ ^ i) _ _ ⟩
      (⟦ fst~ x ⟧ Ρ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i + (⟦ fst~ y ⟧ Ρ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
    ∎
  ⊞-ne-hom (ℕ.less m k) x xs y ys (ρ ∷ Ρ) = {!!}
  ⊞-ne-hom (ℕ.greater m k) x xs y ys (ρ ∷ Ρ) = {!!}

  ⊞-ne-l-hom : ∀ {n} k
            → (xs : Coeffs n)
            → (y : Coeff n)
            → (ys : Coeffs n)
            → (Ρ : Vec Carrier (suc n))
            → ⟦ ⊞-ne-l k xs y ys ⟧ Ρ ≈ ⟦ xs ⟧ Ρ + ⟦ (y , k) ∷ ys ⟧ Ρ
  ⊞-ne-l-hom = {!!}

  ⊞-ne-r-hom : ∀ {n} k
            → (x : Coeff n)
            → (xs : Coeffs n)
            → (ys : Coeffs n)
            → (Ρ : Vec Carrier (suc n))
            → ⟦ ⊞-ne-r k x xs ys ⟧ Ρ ≈ ⟦ (x , k) ∷ xs ⟧ Ρ + ⟦ ys ⟧ Ρ
  ⊞-ne-r-hom = {!!}
