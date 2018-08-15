open import Algebra using (CommutativeSemiring)
open import Relation.Binary

module Polynomials.Mono.Equality
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open CommutativeSemiring commutativeSemiring
  renaming ( refl to refl-C
           ; sym to sym-C
           ; trans to trans-C
           ; +-cong to +-cong-C
           ; *-cong to *-cong-C)

open import Polynomials.Mono commutativeSemiring _≟C_
open import Data.List as List using ([]; _∷_)
open import Data.Product
open import Level using (_⊔_)
open import Algebra.FunctionProperties
open import Data.Nat as ℕ using (ℕ; suc)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

infixr 5 _∷≋_
infix 4 _≋_
data _≋_ : Poly → Poly → Set (a ⊔ ℓ) where
  []≋ : [] ≋ []
  _∷≋_ : ∀ {x y n xs ys} → .{x≠0 : x ≉0} → .{y≠0 : y ≉0} → x ≈ y → xs ≋ ys → x ^ n ⦅ x≠0 ⦆ ∷ xs ≋ y ^ n ⦅ y≠0 ⦆ ∷ ys

open import Function

⟦_⟧-cong : ∀ {xs ys} → xs ≋ ys → ∀ ρ → ⟦ xs ⟧ ρ ≈ ⟦ ys ⟧ ρ
⟦ []≋ ⟧-cong ρ = refl-C
⟦ p ∷≋ ps ⟧-cong ρ =  p ⟨ +-cong-C ⟩ ( ⟦ ps ⟧-cong ρ ⟨ *-cong-C ⟩ refl-C) ⟨ *-cong-C ⟩ refl-C
