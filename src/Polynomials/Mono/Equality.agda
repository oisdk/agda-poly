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

infixr 5 _∷≋0_
data _≋0 : Poly → Set ℓ where
  []≋0 : [] ≋0
  _∷≋0_ : ∀ {i x xs} → x ≈ 0# → xs ≋0 → ((i , x) ∷ xs) ≋0


infixr 5 _∷≋_
infix 4 _≋_
data _≋_ : Poly → Poly → Set ℓ where
  _≋0≋_ : ∀ {xs ys} → xs ≋0 → ys ≋0 → xs ≋ ys
  _∷<≋_ : ∀ {i k x xs y ys} → x ≈ 0# → xs ≋ ys → ((i , x) ∷ xs) ≋ ((ℕ.suc i ℕ.+ k , y) ∷ ys)
  _∷>≋_ : ∀ {i k x xs y ys} → y ≈ 0# → xs ≋ ys → ((ℕ.suc i ℕ.+ k , x) ∷ xs) ≋ ((i , y) ∷ ys)
  _∷≋_ : ∀ {x y n xs ys} → x ≈ y → xs ≋ ys → ((n , x) ∷ xs) ≋ ((n , y) ∷ ys)

open import Polynomials.SemiringReasoning setoid _+_ _*_ +-cong-C *-cong-C
open import Function

≋0-hom : ∀ {xs} → xs ≋0 → ∀ ρ → ⟦ xs ⟧ ρ ≈ 0#
≋0-hom []≋0 ρ = refl-C
≋0-hom {(i , x) ∷ xs} (p ∷≋0 ps) ρ =
  begin
    ⟦ (i , x) ∷ xs ⟧ ρ
  ≡⟨⟩
    (x + ⟦ xs ⟧ ρ * ρ) * ρ ^ i
  ≈⟨ ≪* (p ⟨ +-cong-C ⟩ (≪* ≋0-hom ps ρ)) ⟩
    (0# + 0# * ρ) * ρ ^ i
  ≈⟨ ≪* +-identityˡ _ ⟩
    (0# * ρ) * ρ ^ i
  ≈⟨  ≪* zeroˡ ρ ⟩
    0# * ρ ^ i
  ≈⟨ zeroˡ (ρ ^ i) ⟩
    0#
  ∎

⟦_⟧-cong : ∀ {xs ys} → xs ≋ ys → ∀ ρ → ⟦ xs ⟧ ρ ≈ ⟦ ys ⟧ ρ
⟦_⟧-cong (xp ≋0≋ yp) ρ = trans-C (≋0-hom xp ρ) (sym-C (≋0-hom yp ρ))
⟦_⟧-cong {((i , x) ∷ xs)} {((.(suc (i ℕ.+ _)) , y) ∷ ys)} (p ∷<≋ ps) ρ = {!!}
⟦_⟧-cong {((.(suc (j ℕ.+ _)) , x) ∷ xs)} {((j , y) ∷ ys)} (p ∷>≋ ps) ρ = {!!}
⟦_⟧-cong {((i , x) ∷ xs)} {((.i , y) ∷ ys)} (p ∷≋ ps) ρ = {!!}

-- ⟦ x ≋0≋ y ⟧-cong ρ = trans-C (≋0-hom x ρ) (sym-C (≋0-hom y ρ))
-- ⟦_⟧-cong {(i , x) ∷ xs} {(j , y) ∷ ys} (p ∷<≋ ps) ρ = {!!}
-- ⟦_⟧-cong {(i , x) ∷ xs} {(j , y) ∷ ys} (p ∷>≋ ps) ρ = {!!}
-- ⟦_⟧-cong {(i , x) ∷ xs} {(j , y) ∷ ys} (p ∷≋  ps) ρ = {!!}

-- open import Relation.Nullary
-- open import Relation.Binary

-- -- open IsEquivalence

-- -- ≋-equivalence : IsEquivalence _≋_
-- -- refl ≋-equivalence {[]} = []≋
-- -- refl ≋-equivalence {x ∷ xs} = refl-C ∷≋ refl ≋-equivalence
-- -- sym ≋-equivalence []≋ = []≋
-- -- sym ≋-equivalence (x ∷≋ xs) = sym-C x ∷≋ sym ≋-equivalence xs
-- -- trans ≋-equivalence []≋ []≋ = []≋
-- -- trans ≋-equivalence (x ∷≋ xs) (y ∷≋ ys) = trans-C x y ∷≋ trans ≋-equivalence xs ys

-- -- +-cong : Congruent₂ _≋_ _⊞_
-- -- +-cong []≋ []≋ = []≋
-- -- +-cong []≋ (y ∷≋ ys) = y ∷≋ ys
-- -- +-cong (x ∷≋ xs) []≋ = x ∷≋ xs
-- -- +-cong (x ∷≋ xs) (y ∷≋ ys) = {!!}

-- -- import Data.Nat as ℕ
-- -- import Relation.Binary.PropositionalEquality as ≡

-- -- _≟_ : ∀ xs ys → Dec (xs ≋ ys)
-- -- [] ≟ [] = yes []≋
-- -- [] ≟ (x ∷ ys) = no λ ()
-- -- (x ∷ xs) ≟ [] = no λ ()
-- -- ((i , x) ∷ xs) ≟ ((j , y) ∷ ys) with i ℕ.≟ j
-- -- ... | no ¬p = no λ { (z ∷≋ zs) → ¬p ≡.refl }
-- -- ... | yes ≡.refl with x ≟C y
-- -- ... | no ¬p = no λ { (z ∷≋ zs) → ¬p z }
-- -- ... | yes p with xs ≟ ys
-- -- ... | no ¬p = no λ { (z ∷≋ zs) → ¬p zs }
-- -- ... | yes ps = yes (p ∷≋ ps)
