{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
open import Relation.Binary

module Polynomials.Multi.Equality
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open CommutativeSemiring commutativeSemiring
  renaming ( refl to refl-C
           ; sym to sym-C
           ; trans to trans-C
           ; +-cong to +-cong-C
           ; *-cong to *-cong-C
           ; _≈_ to _≈C_ )

open import Polynomials.Multi commutativeSemiring _≟C_
open import Data.List as List using ([]; _∷_)
open import Data.Nat as ℕ using (ℕ; suc; zero)
-- import Data.List.Relation.Equality.DecSetoid as []-≈
-- import Data.List.Relation.Equality.Setoid as []-≈
open import Data.List.Relation.Pointwise as Pointwise using (Pointwise)
open import Level using (lift; _⊔_; lower)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Polynomials.Irrelevant.Product
import Data.Product.Relation.Pointwise.NonDependent as Prod
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product
open import Function

Coeff-≈ : ∀ {n} → Rel (Poly n) ℓ → Rel (Coeff n) ℓ
Coeff-≈ rel (x ,~ _) (y ,~ _) = rel x y

Poly-≈ : (n : ℕ) → Rel (Poly n) ℓ
Poly-≈ ℕ.zero (lift x) (lift y) = x ≈C y
Poly-≈ (suc n) = Pointwise (Prod.Pointwise (Coeff-≈ (Poly-≈ n)) _≡_)

mutual
  ⟦⟧-cong : ∀ {n}
          → (xs : Poly n)
          → (ys : Poly n)
          → Poly-≈ n xs ys
          → (Ρ : Vec Carrier n)
          → ⟦ xs ⟧ Ρ ≈C ⟦ ys ⟧ Ρ
  ⟦⟧-cong {ℕ.zero} xs ys xs≈ys [] = xs≈ys
  ⟦⟧-cong {suc n} xs ys xs≈ys (ρ ∷ Ρ) = ⟦⟧-coeff-cong xs ys xs≈ys ρ Ρ

  ⟦⟧-coeff-cong : ∀ {n}
              → (xs : Coeffs n)
              → (ys : Coeffs n)
              → (Poly-≈ (suc n) xs ys)
              → (ρ : Carrier)
              → (Ρ : Vec Carrier n)
              → ⟦ xs ⟧ (ρ ∷ Ρ) ≈C ⟦ ys ⟧ (ρ ∷ Ρ)
  ⟦⟧-coeff-cong .[] .[] Pointwise.[] ρ Ρ = refl-C
  ⟦⟧-coeff-cong ((x , i) ∷ xs) ((y , .i) ∷ ys) ((fst , _≡_.refl) Pointwise.∷ xs≈ys) ρ Ρ =
    ⟦⟧-cong (fst~ x) (fst~ y) fst Ρ ⟨ +-cong-C ⟩ (⟦⟧-coeff-cong  xs ys xs≈ys ρ Ρ ⟨ *-cong-C ⟩ refl-C) ⟨ *-cong-C ⟩ refl-C

Coeff-≟ : ∀ {n} → Decidable (Poly-≈ n) → Decidable (Coeff-≈ (Poly-≈ n))
Coeff-≟ f (x ,~ _) (y ,~ _) = f x y

Poly-≟ : (n : ℕ) → Decidable (Poly-≈ n)
Poly-≟ ℕ.zero (lift x) (lift y) = x ≟C y
Poly-≟ (suc n) = Pointwise.decidable (Prod._×-decidable_ (Coeff-≟ (Poly-≟ n)) ℕ._≟_)
