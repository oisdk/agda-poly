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
open import Data.Empty

⊞-identityˡ : ∀ xs → [] ⊞ xs ≋ xs
⊞-identityˡ xs = ≋-refl

⊞-identityʳ : ∀ xs → xs ⊞ [] ≋ xs
⊞-identityʳ [] = []≋
⊞-identityʳ (x ∷ xs) = ≋-refl

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

import Data.Empty.Irrelevant as Irrelevant
open import Function

zero-ring : 1# ≈ 0# → ∀ x → x ≈ 0#
zero-ring p x = trans (sym (*-identityˡ x)) (trans (p ⟨ *-cong ⟩ refl) (zeroˡ x))

elim-1* : ∀ {w} x {Whatever : Set w} → .(x ≉0) → 1# * x ≈ 0# → Whatever
elim-1* x x≠0 p = Irrelevant.⊥-elim (x≠0 (trans (sym (*-identityˡ x)) p))

⋊-identityˡ : ∀ xs → 1# ⋊ xs ≋ xs
⋊-identityˡ [] = []≋
⋊-identityˡ (x ^^ i ⦅ x≠0 ⦆ ∷ xs) with (1# * x) ≟C 0#
⋊-identityˡ (x ^^ i ⦅ x≠0 ⦆ ∷ xs) | yes p = elim-1* x x≠0 p
⋊-identityˡ (x ^^ i ⦅ x≠0 ⦆ ∷ xs) | no ¬p = *-identityˡ x ∷≋ ⋊-identityˡ xs

⊠-identityˡ : ∀ xs → ((1# , 0) ∷↓ []) ⊠ xs ≋ xs
⊠-identityˡ xs with 1# ≟C 0#
⊠-identityˡ [] | yes p = ≋-refl
⊠-identityˡ (x ^^ i ⦅ x≠0 ⦆ ∷ xs) | yes p = Irrelevant.⊥-elim (x≠0 (zero-ring p x))
⊠-identityˡ xs | no ¬p = ⊠-identityˡ-nz xs
  where
  ⊠-identityˡ-nz : ∀ xs → .{1≠0 : 1# ≉0} → (1# ^^ 0 ⦅ 1≠0 ⦆ ∷ []) ⊠ xs ≋ xs
  ⊠-identityˡ-nz [] = []≋
  ⊠-identityˡ-nz (x ^^ i ⦅ x≠0 ⦆ ∷ xs) with (1# * x) ≟C 0#
  ⊠-identityˡ-nz (x ^^ i ⦅ x≠0 ⦆ ∷ xs) | yes p = elim-1* x x≠0 p
  ⊠-identityˡ-nz (x ^^ i ⦅ x≠0 ⦆ ∷ xs) | no ¬p = *-identityˡ x ∷≋ ≋-trans (⊞-identityʳ(1# ⋊ xs)) (⋊-identityˡ xs)

⊠-zeroˡ : ∀ xs → [] ⊠ xs ≋ []
⊠-zeroˡ xs = ≋-refl

⊠-assoc : ∀ xs ys zs → (xs ⊠ ys) ⊠ zs ≋ xs ⊠ (ys ⊠ zs)
⊠-assoc xs ys zs = {!!}

⊠-comm : ∀ xs ys → xs ⊠ ys ≋ ys ⊠ xs
⊠-comm xs ys = {!!}

⊠-⊞-distrib : ∀ xs ys zs → (ys ⊞ zs) ⊠ xs ≋ ((ys ⊠ xs) ⊞ (zs ⊠ xs))
⊠-⊞-distrib xs ys zs = {!!}
