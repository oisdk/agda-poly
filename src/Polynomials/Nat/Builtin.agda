module Polynomials.Nat.Builtin where

open import Data.Nat as ℕ using (ℕ; zero; suc; Ordering; less; equal; greater)
open import Agda.Builtin.Nat using (_+_; _-_; _==_; _<_)
open import Data.Bool
open import Relation.Binary.PropositionalEquality.TrustMe
open import Relation.Binary.PropositionalEquality

-- A compare operation, with the same semantics as ℕ.compare, but
-- implemented using primitive operations.
compare : ∀ m n → Ordering m n
compare m n =
  if m < n
     then subst (Ordering m) (trustMe {x = suc (m + (n - m - 1))} {y = n}) (less m (n - m - 1))
     else if m == n
             then subst (Ordering m) (trustMe {x = m} {y = n}) (equal m)
             else subst (λ m′ → Ordering m′ n) (trustMe {x = suc (n + (m - n - 1))} {y = m}) (greater n (m - n - 1))
