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
           ; *-cong to *-cong-C
           ; _≈_ to _≈C_ )

open import Polynomials.Mono commutativeSemiring _≟C_
open import Data.List as List using ([]; _∷_)

infixr 5 _∷≋_
infix 4 _≋_
data _≋_ : Poly → Poly → Set ℓ where
  []≋  : [] ≋ []
  _∷≋_ : ∀ {n x y xs ys}
       → .{x≠0 : x ≉0}
       → .{y≠0 : y ≉0}
       → x ≈C y → xs ≋ ys
       → x ^^ n ⦅ x≠0 ⦆ ∷ xs ≋ y ^^ n ⦅ y≠0 ⦆ ∷ ys

open import Function

⟦_⟧-cong : ∀ {xs ys} → xs ≋ ys → ∀ ρ → ⟦ xs ⟧ ρ ≈C ⟦ ys ⟧ ρ
⟦ []≋ ⟧-cong ρ = refl-C
⟦ p ∷≋ ps ⟧-cong ρ = p ⟨ +-cong-C ⟩ ( ⟦ ps ⟧-cong ρ ⟨ *-cong-C ⟩ refl-C) ⟨ *-cong-C ⟩ refl-C

≋-refl : Reflexive _≋_
≋-refl {[]} = []≋
≋-refl {x ∷ xs} = refl-C ∷≋ ≋-refl

≋-sym : Symmetric _≋_
≋-sym []≋ = []≋
≋-sym (p ∷≋ ps) = sym-C p ∷≋ ≋-sym ps

≋-trans : Transitive _≋_
≋-trans []≋ []≋ = []≋
≋-trans (x ∷≋ xs) (y ∷≋ ys) = trans-C x y ∷≋ (≋-trans xs ys)

≋-isEquivalence : IsEquivalence _≋_
≋-isEquivalence = record
  { refl  = ≋-refl
  ; sym   = ≋-sym
  ; trans = ≋-trans
  }

open import Level using (_⊔_)

≋-setoid : Setoid (a ⊔ ℓ) ℓ
≋-setoid = record
  { Carrier = Poly
  ; _≈_ = _≋_
  ; isEquivalence = ≋-isEquivalence
  }

open import Algebra.FunctionProperties _≋_
open import Relation.Binary.EqReasoning ≋-setoid
open import Data.Nat as ℕ using (ℕ; suc)
open import Data.Product
open import Relation.Nullary
open import Data.Empty

⍓-cong : ∀ {xs ys i} → xs ≋ ys → xs ⍓ i ≋ ys ⍓ i
⍓-cong []≋ = []≋
⍓-cong (p ∷≋ ps) = p ∷≋ ps

∷↓-cong : ∀ {x₁ x₂ i xs₁ xs₂} → x₁ ≈C x₂ → xs₁ ≋ xs₂ → (x₁ , i) ∷↓ xs₁ ≋ (x₂ , i) ∷↓ xs₂
∷↓-cong {x₁} {x₂} xp xps with x₁ ≟C 0# | x₂ ≟C 0#
∷↓-cong {x₁} {x₂} xp xps | yes _ | yes _ = ⍓-cong xps
∷↓-cong {x₁} {x₂} xp xps | yes p | no ¬p = ⊥-elim (¬p (trans-C (sym-C xp) p))
∷↓-cong {x₁} {x₂} xp xps | no ¬p | yes p = ⊥-elim (¬p (trans-C xp p))
∷↓-cong {x₁} {x₂} xp xps | no  _ | no  _ = xp ∷≋ xps


⊞-cong : Congruent₂ _⊞_
⊞-ne-l-cong : ∀ {k xs₁ xs₂ y₁ y₂ ys₁ ys₂} → .{y₁≠0 : y₁ ≉0} → .{y₂≠0 : y₂ ≉0} → xs₁ ≋ xs₂ → y₁ ≈C y₂ → ys₁ ≋ ys₂ → ⊞-ne-l k xs₁ y₁ y₁≠0 ys₁ ≋ ⊞-ne-l k xs₂ y₂ y₂≠0 ys₂
⊞-ne-r-cong : ∀ {k x₁ xs₁ ys₁ x₂ xs₂ ys₂} → .{x₁≠0 : x₁ ≉0} → .{x₂≠0 : x₂ ≉0} → x₁ ≈C x₂ → xs₁ ≋ xs₂ → ys₁ ≋ ys₂ → ⊞-ne-r k x₁ x₁≠0 xs₁ ys₁ ≋ ⊞-ne-r k x₂ x₂≠0 xs₂ ys₂

⊞-ne-cong : ∀ {i j}
          → (c : ℕ.Ordering i j)
          → ∀ {x₁ y₁ x₂ y₂ xs₁ ys₁ xs₂ ys₂}
          → .{x₁≠0 : x₁ ≉0}
          → .{x₂≠0 : x₂ ≉0}
          → .{y₁≠0 : y₁ ≉0}
          → .{y₂≠0 : y₂ ≉0}
          → x₁ ≈C x₂
          → xs₁ ≋ xs₂
          → y₁ ≈C y₂
          → ys₁ ≋ ys₂
          → ⊞-ne c x₁ x₁≠0 xs₁ y₁ y₁≠0 ys₁ ≋ ⊞-ne c x₂ x₂≠0 xs₂ y₂ y₂≠0 ys₂
⊞-ne-cong (ℕ.less m k) xp xps yp yps = xp ∷≋ ⊞-ne-l-cong xps yp yps
⊞-ne-cong (ℕ.greater m k) xp xps yp yps = yp ∷≋ ⊞-ne-r-cong xp xps yps
⊞-ne-cong (ℕ.equal i) {x₁} {y₁} {x₂} {y₂} xp xps yp yps with (x₁ + y₁) ≟C 0# | (x₂ + y₂) ≟C 0#
... | yes p | yes p₁ = ⍓-cong (⊞-cong xps yps)
... | yes p | no ¬p = ⊥-elim (¬p (trans-C (sym-C (+-cong-C xp yp)) p))
... | no ¬p | yes p = ⊥-elim (¬p (trans-C (+-cong-C xp yp) p))
... | no ¬p | no ¬p₁ = +-cong-C xp yp ∷≋ ⊞-cong xps yps

⊞-ne-l-cong []≋ yp yps = yp ∷≋ yps
⊞-ne-l-cong {k} (_∷≋_ {i} xp xps) yp yps = ⊞-ne-cong (ℕ.compare i k) xp xps yp yps

⊞-ne-r-cong xp xps []≋ = xp ∷≋ xps
⊞-ne-r-cong {k} xp xps (_∷≋_ {j} yp yps) = ⊞-ne-cong (ℕ.compare k j) xp xps yp yps

⊞-cong []≋ yp = yp
⊞-cong (xp ∷≋ xps) []≋ = xp ∷≋ xps
⊞-cong (_∷≋_ {i} xp xps) (_∷≋_ {j} yp yps) = ⊞-ne-cong (ℕ.compare i j) xp xps yp yps

