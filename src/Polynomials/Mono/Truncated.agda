{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
open import Relation.Binary

module Polynomials.Mono.Truncated
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open import Polynomials.Mono commutativeSemiring _≟C_
open import Data.List as List using ([]; _∷_; foldr)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product
open import Data.Nat as ℕ


Normal : Poly → Set a
Normal xs = xs ≡ foldr _∷↓_ [] xs

record Poly↓ : Set a where
  constructor _↓⦅_⦆
  field
    ↑ : Poly
    .↕ : Normal ↑

open Poly↓

⊞-trunc : ∀ xs ys → Normal xs → Normal ys → Normal (xs ⊞ ys)
⊞-trunc [] ys pxs pys = pys
⊞-trunc (x ∷ xs) [] pxs pys = pxs
⊞-trunc ((i , x) ∷ xs) ((j , y) ∷ ys) pxs pys with ℕ.compare i j
⊞-trunc ((i , x) ∷ xs) ((.(suc (i + k)) , y) ∷ ys) pxs pys | less .i k = {!!}
⊞-trunc ((i , x) ∷ xs) ((.i , y) ∷ ys) pxs pys | equal .i = {!!}
⊞-trunc ((.(suc (j + k)) , x) ∷ xs) ((j , y) ∷ ys) pxs pys | greater .j k = {!!}

_⊞↓_ : Poly↓ → Poly↓ → Poly↓
(x ↓⦅ xp ⦆) ⊞↓ (y ↓⦅ yp ⦆) = (x ⊞ y) ↓⦅ {!!} ⦆

-- Define operators, instances on this type
