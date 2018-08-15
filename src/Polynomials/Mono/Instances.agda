open import Algebra using (CommutativeSemiring)
open import Relation.Binary

module Polynomials.Mono.Instances
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open import Polynomials.Mono commutativeSemiring _≟C_
open import Polynomials.Mono.Equality commutativeSemiring _≟C_
open import Polynomials.SemiringReasoning ≋-setoid _⊞_ _⊠_ ⊞-cong ⊠-cong
open import Data.List as List using ([]; List; _∷_)
open CommutativeSemiring commutativeSemiring
open import Data.Product
open import Relation.Nullary

⊞-identityˡ : ∀ xs → [] ⊞ xs ≋ xs
⊞-identityˡ xs = ≋-refl

⊞-assoc : ∀ xs ys zs → (xs ⊞ ys) ⊞ zs ≋ xs ⊞ (ys ⊞ zs)
⊞-assoc [] ys zs = ≋-refl
⊞-assoc (x ∷ xs) [] zs = ≋-refl
⊞-assoc (x ∷ xs) (y ∷ ys) [] = {! !}
⊞-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = {!!}

⊞-comm : ∀ xs ys → xs ⊞ ys ≋ ys ⊞ xs
⊞-comm [] [] = []≋
⊞-comm [] (x ∷ ys) = ≋-refl
⊞-comm (x ∷ xs) [] = ≋-refl
⊞-comm (x ∷ xs) (y ∷ ys) = {!!}

⊠-identityˡ-nz : ∀ xs → .{1≠0 : 1# ≉0} → (1# ^^ 0 ⦅ 1≠0 ⦆ ∷ []) ⊠ xs ≋ xs
⊠-identityˡ-nz [] = []≋
⊠-identityˡ-nz (x ∷ xs) = {!!}

⊠-identityˡ : ∀ xs → ((1# , 0) ∷↓ []) ⊠ xs ≋ xs
⊠-identityˡ xs with 1# ≟C 0#
⊠-identityˡ xs | no ¬p = {!!}
⊠-identityˡ xs | yes p = {!!}
