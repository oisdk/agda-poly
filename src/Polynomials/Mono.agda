open import Algebra using (CommutativeSemiring)
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Nullary

module Polynomials.Mono
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open CommutativeSemiring commutativeSemiring hiding (zero)

open import Data.List as List using (_∷_; []; foldr; List)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Function
open import Data.Maybe
open import Data.Empty

-- Approaches:
--
-- Non-normalising operations.
--   * Possible explosions in size where they're not needed.
--   * Simple, elegant model for hoomomorphic proofs.
--
-- Normalising operations.
--   * Cheap, when done with single cons operator. Only constant factor
--     cost.
--   * Proofs become more complex.
--
-- Non-normalising equality
--   * Simple to implemenent.
--   * Simple to test for.
--   * Compatible with normalisation at end.
--   * Doesn't hold semiring laws.
--
-- Normalisation then  equality test
--   * Simple to implement
--   * Doesn't normalise representations (allows slop to stay)
--   * Possible best option.
--
-- Normalising equality
--   * Allows semiring operations.
--   * Very complex to test for, prove laws about.
--   * Allows for slop in operations.
--
-- Poly carries normalisation proof.
--   * Ugly proofs, I think.
--   * May be elegant way to get around it w/ fold homomorphisms etc.
--   * Infects all code.
--
-- In summary:
--   Option 1: normalise then test for simple equality on *all* equality tests.
--   Option 2: Carry normalised proof with Poly type.
--
-- The proof of normalisation is currently xs ≡ foldr _∷↓_ [] xs, which is impossible
-- to test for equality on.
--
-- How about Not (Any (0# ≈))? Or All (Not (0# ≈))?
-- ^^^^^^^^^^^^^^^^^^^^^ This is a good option.
--
-- ALSO: essential to consider fold-homomorphic-based proofs. Pushing through without
-- them and then coming back to add them in may take more time in the long run. So, to
-- consider:
--   * foldr-fusion
--   * foldr-laws


Poly : Set a
Poly = List.List (ℕ × Carrier)

pow : ℕ → Poly → Poly
pow i [] = []
pow i ((j , x) ∷ xs) = (j ℕ.+ i , x) ∷ xs


infixr 5 _∷↓_
_∷↓_ : (ℕ × Carrier) → Poly → Poly
_∷↓_ (i , x) with x ≟C 0#
... | yes p = pow (suc i)
... | no ¬p = _∷_ (i , x)

Normal : Poly → Set a
Normal xs = xs ≡ foldr _∷↓_ [] xs

record Poly↓ : Set a where
  constructor ⟨_⟩↓_
  field
    ↑ : Poly
    .↕ : Normal ↑

open Poly↓

foldr-step : ∀ {ℓ₁} {A B : Set ℓ₁} → (f : A → B → B) → (b : B) (x : A) (xs : List A) → foldr f b (x ∷ xs) ≡ f x (foldr f b xs)
foldr-step f b x xs = ≡.refl

tail′ : ∀ {a} {A : Set a} → List A → List A
tail′ [] = []
tail′ (x ∷ xs) = xs

non-zero : ∀ {i x xs} → (x ≈ 0#) → Normal ((i , x) ∷ xs) → ⊥
non-zero {i} {x} {xs} prf prf₂ with x ≟C 0#
non-zero {i} {x} {xs} prf prf₂ | no ¬p = ¬p prf
non-zero {i} {x} {[]} prf () | yes p
non-zero {i} {x} {x₁ ∷ xs} prf prf₂ | yes p = {!!}

pow-norm : ∀ i xs → Normal xs → Normal (pow i xs)
pow-norm i [] prf = prf
pow-norm i ((j , x) ∷ xs) prf with x ≟C 0#
pow-norm i ((j , x) ∷ xs) prf | yes p = {!!}
pow-norm i ((j , x) ∷ xs) prf | no ¬p = ≡.cong (_∷_ (j ℕ.+ i , x) ∘ tail′) prf

-- prf-∷ : ∀ {x xs} → xs ≡ foldr _∷↓_ [] xs → (x ∷↓ xs) ≡ foldr _∷↓_ [] (x ∷↓ xs)
-- prf-∷ {i , x} {xs} prf with x ≟C 0#
-- prf-∷ {i , x} {xs} prf | yes p = ≡.cong (pow (suc i)) {!!}
-- prf-∷ {i , x} {xs} prf | no ¬p = {!!}

infixr 5 _∷↕_
_∷↕_ : (ℕ × Carrier) → Poly↓ → Poly↓
x ∷↕ (⟨ xs ⟩↓ xp) = ⟨ x ∷↓ xs ⟩↓ {!!}

-- infixl 6 _⊞_
-- _⊞_ : Poly↓ → Poly↓ → Poly↓
-- ⊞-ne : ∀ {i j} → ℕ.Ordering i j → Carrier → Poly↓ → Carrier → Poly↓ → Poly↓
-- ⊞-ne-l : ℕ → Poly↓ → Carrier → Poly↓ → Poly↓
-- ⊞-ne-r : ℕ → Carrier → Poly↓ → Poly↓ → Poly↓

-- ⟨ [] ⟩↓ _ ⊞ ys = ys
-- ⟨ x ∷ xs ⟩↓ xp ⊞ ⟨ [] ⟩↓ _ = ⟨ x ∷ xs ⟩↓ xp
-- ⟨(i , x) ∷ xs ⟩↓ xp ⊞ ⟨(j , y) ∷ ys ⟩↓ yp = ⊞-ne (ℕ.compare i j) x xs y ys

-- ⊞-ne (ℕ.less    i k) x xs y ys = (i , x) ∷↓ ⊞-ne-l k xs y ys
-- ⊞-ne (ℕ.equal   i  ) x xs y ys = (i , x + y) ∷↓ (xs ⊞ ys)
-- ⊞-ne (ℕ.greater j k) x xs y ys = (j , y) ∷↓ ⊞-ne-r k x xs ys

-- ⊞-ne-l k [] y ys = (k , y) ∷↓ ys
-- ⊞-ne-l k ((i , x) ∷ xs) y ys = ⊞-ne (ℕ.compare i k) x xs y ys

-- ⊞-ne-r k x xs [] = (k , x) ∷↓ xs
-- ⊞-ne-r k x xs ((j , y) ∷ ys) = ⊞-ne (ℕ.compare k j) x xs y ys

-- Multiply a polynomial by a constant factor
-- infixl 7 _⋊_
-- _⋊_ : Carrier → Poly → Poly
-- x ⋊ ((j , y) ∷ ys) = (j , x * y) ∷↓ x ⋊ ys
-- x ⋊ [] = []

-- infixl 7 _⊠_
-- _⊠_ : Poly → Poly → Poly
-- [] ⊠ _ = []
-- (x ∷ xs) ⊠ [] = []
-- ((i , x) ∷ xs) ⊠ ((j , y) ∷ ys) = (i ℕ.+ j , x * y) ∷↓ x ⋊ ys ⊞ xs ⊠ ((0 , y) ∷ ys)

-- κ : Carrier → Poly
-- κ x = (zero , x) ∷↓ []

-- ι : Poly
-- ι = (suc zero , 1#) ∷↓ []

-- ----------------------------------------------------------------------
-- -- Evaluation
-- ----------------------------------------------------------------------
-- -- We "run" the polynomial on some input with Horner's method.

-- infixr 8 _^_
-- _^_ : Carrier → ℕ → Carrier
-- x ^ zero = 1#
-- x ^ suc n = x * x ^ n

-- _↦_^*_ : Carrier → (ℕ × Carrier) → Carrier → Carrier
-- ρ ↦ (i , x) ^* xs = (x + xs * ρ) * ρ ^ i

-- ⟦_⟧ : Poly → Carrier → Carrier
-- ⟦ xs ⟧ ρ = List.foldr (ρ ↦_^*_) 0# xs
