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

⟦_⟧↕ : Poly → Set a
⟦ xs ⟧↕ = xs ≡ List.foldr _∷↓_ [] xs

infixr 5 _∷≋_
infix 4 _≋_
data _≋_ : Poly → Poly → Set ℓ where
  []≋ : [] ≋ []
  _∷≋_ : ∀ {x y n xs ys} → x ≈ y → xs ≋ ys → ((n , x) ∷ xs) ≋ ((n , y) ∷ ys)

-- open import Polynomials.SemiringReasoning setoid _+_ _*_ +-cong-C *-cong-C
-- open import Function

-- ≋0-hom : ∀ {xs} → xs ≋0 → ∀ ρ → ⟦ xs ⟧ ρ ≈ 0#
-- ≋0-hom []≋0 ρ = refl-C
-- ≋0-hom {(i , x) ∷ xs} (p ∷≋0 ps) ρ =
--   begin
--     ⟦ (i , x) ∷ xs ⟧ ρ
--   ≡⟨⟩
--     (x + ⟦ xs ⟧ ρ * ρ) * ρ ^ i
--   ≈⟨ ≪* (p ⟨ +-cong-C ⟩ (≪* ≋0-hom ps ρ)) ⟩
--     (0# + 0# * ρ) * ρ ^ i
--   ≈⟨ ≪* +-identityˡ _ ⟩
--     (0# * ρ) * ρ ^ i
--   ≈⟨  ≪* zeroˡ ρ ⟩
--     0# * ρ ^ i
--   ≈⟨ zeroˡ (ρ ^ i) ⟩
--     0#
--   ∎

-- open import Polynomials.Mono.Homomorphism commutativeSemiring _≟C_ using (pow-add)
-- import Relation.Binary.PropositionalEquality as ≡
-- import Data.Nat.Properties as ℕ-≡

-- ⟦_⟧-cong : ∀ {xs ys} → xs ≋ ys → ∀ ρ → ⟦ xs ⟧ ρ ≈ ⟦ ys ⟧ ρ
-- ⟦_⟧-cong (xp ≋0≋ yp) ρ = trans-C (≋0-hom xp ρ) (sym-C (≋0-hom yp ρ))
-- ⟦_⟧-cong {xs} {(i , yz) ∷ (k , y) ∷ ys} (p ∷<≋ ps) ρ = sym-C $
--   begin
--     ⟦ (i , yz) ∷ (k , y) ∷ ys ⟧ ρ
--   ≡⟨⟩
--     (yz + ⟦ (k , y) ∷ ys ⟧ ρ * ρ) * ρ ^ i
--   ≈⟨ ≪* (≪+ p ︔ +-identityˡ _) ⟩
--     (⟦ (k , y) ∷ ys ⟧ ρ * ρ) * ρ ^ i
--   ≈⟨ *-assoc _ ρ _ ⟩
--     ⟦ (k , y) ∷ ys ⟧ ρ * ρ ^ suc i
--   ≡⟨⟩
--     (y + ⟦ ys ⟧ ρ * ρ) * ρ ^ k * ρ ^ suc i
--   ≈⟨ *-assoc _ _ _ ︔ *≫ pow-add ρ k (suc i) ⟩
--     (y + ⟦ ys ⟧ ρ * ρ) * ρ ^ (k ℕ.+ suc i)
--   ≡⟨ ≡.cong (λ ki → (y + ⟦ ys ⟧ ρ * ρ) * ρ ^ ki) (ℕ-≡.+-comm k (suc i) ) ⟩
--     (y + ⟦ ys ⟧ ρ * ρ) * ρ ^ (suc i ℕ.+ k)
--   ≈⟨ sym-C (⟦ ps ⟧-cong ρ) ⟩
--     ⟦ xs ⟧ ρ
--   ∎
-- ⟦_⟧-cong {(i , xz) ∷ (k , x) ∷ xs} {ys} (p ∷>≋ ps) ρ =
--   begin
--     ⟦ (i , xz) ∷ (k , x) ∷ xs ⟧ ρ
--   ≡⟨⟩
--     (xz + ⟦ (k , x) ∷ xs ⟧ ρ * ρ) * ρ ^ i
--   ≈⟨ ≪* (≪+ p ︔ +-identityˡ _) ⟩
--     (⟦ (k , x) ∷ xs ⟧ ρ * ρ) * ρ ^ i
--   ≈⟨ *-assoc _ ρ _ ⟩
--     ⟦ (k , x) ∷ xs ⟧ ρ * ρ ^ suc i
--   ≡⟨⟩
--     (x + ⟦ xs ⟧ ρ * ρ) * ρ ^ k * ρ ^ suc i
--   ≈⟨ *-assoc _ _ _ ︔ *≫ pow-add ρ k (suc i) ⟩
--     (x + ⟦ xs ⟧ ρ * ρ) * ρ ^ (k ℕ.+ suc i)
--   ≡⟨ ≡.cong (λ ki → (x + ⟦ xs ⟧ ρ * ρ) * ρ ^ ki) (ℕ-≡.+-comm k (suc i) ) ⟩
--     (x + ⟦ xs ⟧ ρ * ρ) * ρ ^ (suc i ℕ.+ k)
--   ≈⟨ ⟦ ps ⟧-cong ρ ⟩
--     ⟦ ys ⟧ ρ
--   ∎
-- ⟦_⟧-cong {((i , x) ∷ xs)} {((.i , y) ∷ ys)} (p ∷≋ ps) ρ =
--   begin
--     ⟦ (i , x) ∷ xs ⟧ ρ
--   ≡⟨⟩
--     (x + ⟦ xs ⟧ ρ * ρ) * ρ ^ i
--   ≈⟨ ≪* (p ⟨ +-cong-C ⟩ (≪* ⟦ ps ⟧-cong ρ)) ⟩
--     ⟦ (i , y) ∷ ys ⟧ ρ
--   ∎

-- -- ⟦ x ≋0≋ y ⟧-cong ρ = trans-C (≋0-hom x ρ) (sym-C (≋0-hom y ρ))
-- -- ⟦_⟧-cong {(i , x) ∷ xs} {(j , y) ∷ ys} (p ∷<≋ ps) ρ = {!!}
-- -- ⟦_⟧-cong {(i , x) ∷ xs} {(j , y) ∷ ys} (p ∷>≋ ps) ρ = {!!}
-- -- ⟦_⟧-cong {(i , x) ∷ xs} {(j , y) ∷ ys} (p ∷≋  ps) ρ = {!!}

-- open import Relation.Nullary
-- open import Relation.Binary

-- open IsEquivalence

-- ≋-refl : ∀ {xs} → xs ≋ xs
-- ≋-refl {[]} = []≋0 ≋0≋ []≋0
-- ≋-refl {x ∷ xs} = refl-C ∷≋ ≋-refl

-- ≋-trans : ∀ {x y z} → x ≋ y → y ≋ z → x ≋ z
-- ≋-trans (x₁ ≋0≋ x₂) ys = {!-c!}
-- ≋-trans (x₁ ∷<≋ xs) ys = {!!}
-- ≋-trans (x₁ ∷>≋ xs) ys = {!!}
-- ≋-trans (x₁ ∷≋ xs) ys = {!!}

-- ≋-equivalence : IsEquivalence _≋_
-- refl ≋-equivalence = ≋-refl
-- sym ≋-equivalence (x ≋0≋ y) = y ≋0≋ x
-- sym ≋-equivalence (p ∷<≋ ps) = p ∷>≋ sym ≋-equivalence ps
-- sym ≋-equivalence (p ∷>≋ ps) = p ∷<≋ sym ≋-equivalence ps
-- sym ≋-equivalence (p ∷≋ ps) = sym-C p ∷≋ sym ≋-equivalence ps
-- trans ≋-equivalence (x ≋0≋ y) (x₁ ≋0≋ x₂)   = {!!}
-- trans ≋-equivalence (x ≋0≋ y) (x₁ ∷<≋ ys)   = {!!}
-- trans ≋-equivalence (x ≋0≋ y) (x₂ ∷>≋ ys)   = {!!}
-- trans ≋-equivalence (x ≋0≋ y) (x₂ ∷≋ ys)    = {!!}
-- trans ≋-equivalence (x ∷<≋ xs) (x₁ ≋0≋ x₂)  = {!!}
-- trans ≋-equivalence (x ∷<≋ xs) (x₁ ∷<≋ ys)  = {!!}
-- trans ≋-equivalence (x ∷<≋ xs) (x₁ ∷>≋ ys)  = {!!}
-- trans ≋-equivalence (x ∷<≋ xs) (x₁ ∷≋ ys)   = {!!}
-- trans ≋-equivalence (x₁ ∷>≋ xs) (x₂ ≋0≋ x₃) = {!!}
-- trans ≋-equivalence (x₁ ∷>≋ xs) (x₂ ∷<≋ ys) = {!!}
-- trans ≋-equivalence (x₁ ∷>≋ xs) (x₃ ∷>≋ ys) = {!!}
-- trans ≋-equivalence (x₁ ∷>≋ xs) (x₃ ∷≋ ys)  = {!!}
-- trans ≋-equivalence (x₁ ∷≋ xs) (x₂ ≋0≋ x₃)  = {!!}
-- trans ≋-equivalence (x₁ ∷≋ xs) (x₂ ∷<≋ ys)  = {!!}
-- trans ≋-equivalence (x₁ ∷≋ xs) (x₃ ∷>≋ ys)  = {!!}
-- trans ≋-equivalence (x₁ ∷≋ xs) (x₂ ∷≋ ys)   = {!!}

-- -- +-cong : Congruent₂ _≋_ _⊞_
-- -- -- +-cong []≋ []≋ = []≋
-- -- -- +-cong []≋ (y ∷≋ ys) = y ∷≋ ys
-- -- -- +-cong (x ∷≋ xs) []≋ = x ∷≋ xs
-- -- -- +-cong (x ∷≋ xs) (y ∷≋ ys) = {!!}

-- -- -- import Data.Nat as ℕ
-- -- -- import Relation.Binary.PropositionalEquality as ≡

-- -- -- _≟_ : ∀ xs ys → Dec (xs ≋ ys)
-- -- -- [] ≟ [] = yes []≋
-- -- -- [] ≟ (x ∷ ys) = no λ ()
-- -- -- (x ∷ xs) ≟ [] = no λ ()
-- -- -- ((i , x) ∷ xs) ≟ ((j , y) ∷ ys) with i ℕ.≟ j
-- -- -- ... | no ¬p = no λ { (z ∷≋ zs) → ¬p ≡.refl }
-- -- -- ... | yes ≡.refl with x ≟C y
-- -- -- ... | no ¬p = no λ { (z ∷≋ zs) → ¬p z }
-- -- -- ... | yes p with xs ≟ ys
-- -- -- ... | no ¬p = no λ { (z ∷≋ zs) → ¬p zs }
-- -- -- ... | yes ps = yes (p ∷≋ ps)
 
