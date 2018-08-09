open import Algebra using (CommutativeSemiring)

module Polynomials.Poly.Sparse
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  where

open import Polynomials.Monomial.Sparse
  using ()
  renaming (Poly to Mono; _⊞_ to _⊕_; _⊠_ to _⊗_)

open CommutativeSemiring commutativeSemiring

open import Data.Nat as ℕ using (ℕ; suc; zero)

polySemiring : ℕ → CommutativeSemiring a ℓ

data Poly : ℕ → Set a where
  Κ : Carrier → Poly 0
  Ι : ∀ n {m} → Mono (polySemiring m) → Poly (suc n ℕ.+ m)

polySemiring n = record
  { Carrier = Poly n
  }