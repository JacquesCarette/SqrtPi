{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
-- add --safe when there are no more holes

open import Categories.Category -- we need it all
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.RigCategory

open import Categorical.SqrtRig

-- Everything is over a SqrtRig
module Categorical.Gates {o ℓ e} {C : Category o ℓ e}
  {M⊎ M× : Monoidal C} {S⊎ : Symmetric M⊎}
  {S× : Symmetric M×} {R : RigCategory C S⊎ S×} (SR : SqrtRig R) where


  open import Level using (Level)

  open import Categories.Category.Monoidal.Interchange.Braided (Symmetric.braided S⊎) using (module swapInner)

  open import Categorical.Scalars SR

  open Category C -- all of it
  open SqrtRig SR
  open Kit R

  X : 2×2
  X = σ⊕

  P : Scalar → 2×2
  P s = id ⊕₁ s

  -- Note: S was already defined in SqrtRig
  Z T H : 2×2
  Z = P -𝟙
  T = P i
  H = ω ● X ∘ S ∘ V ∘ S ∘ X

  -- note that this isn't quite what's in the paper, but it is equivalent
  Midswap : {A B C D : Obj} → (A ⊕₀ B) ⊕₀ (C ⊕₀ D) ⇒ (A ⊕₀ C) ⊕₀ (B ⊕₀ D)
  Midswap = swapInner.from
