{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
import Level

-- Some specialised tools for equaltional reasoning
module SemiringReasoning (commutativeSemiring : CommutativeSemiring Level.zero Level.zero) where

  open CommutativeSemiring commutativeSemiring

  open import Algebra.FunctionProperties _≈_ public
  open import Relation.Binary.EqReasoning setoid public

  -- These functions deal with setoid-specific congruences:
  -- the ellipsis (⋯) indicates the side that stays the same. i.e:
  --
  --   (x + y) + z
  -- ≈⟨ ⟨ +-comm x y ⟩+⋯ ⟩
  --   (y + x) + z
  ⟨_⟩+⋯ : ∀ {x y z} → x ≈ y → x + z ≈ y + z
  ⟨_⟩+⋯ prf = +-cong prf refl

  ⋯+⟨_⟩ : ∀ {x y z} → y ≈ z → x + y ≈ x + z
  ⋯+⟨_⟩ prf = +-cong refl prf

  ⟨_⟩*⋯ : ∀ {x y z} → x ≈ y → x * z ≈ y * z
  ⟨_⟩*⋯ prf = *-cong prf refl

  ⋯*⟨_⟩ : ∀ {x y z} → y ≈ z → x * y ≈ x * z
  ⋯*⟨_⟩ prf = *-cong refl prf

  -- If a function (a cangruence, for instance) appropriately changes
  -- the relation, it can be applied with this combinator. It is
  -- useful if both sides of the equation are getting large, and you
  -- want to "cancel from both sides" with something.
  infixr 2 _≅⟨_⟩_
  _≅⟨_⟩_ : ∀ w {x y z} → (y ≈ z → w ≈ x) → y IsRelatedTo z → w IsRelatedTo x
  _ ≅⟨ congruence ⟩ relTo y~z = relTo (congruence y~z)

  -- transitivity as an operator
  infixr 2 _︔_
  _︔_ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
  _︔_ = trans
