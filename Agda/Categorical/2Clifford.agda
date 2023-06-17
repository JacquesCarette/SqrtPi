{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
-- add --safe when there are no more holes

-- Soundness and Completeness for ≤ 2-qubit Clifford relations

open import Categories.Category -- we need it all
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.RigCategory

open import Categorical.SqrtRig

-- Everything is over a SqrtRig
module Categorical.2Clifford {o ℓ e} {C : Category o ℓ e}
  {M⊎ M× : Monoidal C} {S⊎ : Symmetric M⊎}
  {S× : Symmetric M×} {R : RigCategory C S⊎ S×} (SR : SqrtRig R) where

  open import Level using (Level)

  -- open import Categories.Category.Monoidal.Interchange.Braided (Symmetric.braided S⊎) using (module swapInner)
  import Categories.Category.Monoidal.Reasoning as MonR
  open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
  
  private
    module S⊎ = Symmetric S⊎
    module S× = Symmetric S×

  open import Categorical.Scalars SR
  open import Categorical.Gates SR
  
  open Category C -- all of it
  open HomReasoning
  open SqrtRig SR
  open Kit R
  -- open MonR M× using (_⟩⊗⟨refl)
  -- open MonR M⊎ using () renaming (_⟩⊗⟨refl to _⟩⊕⟨refl)

  private
    variable
      A B : Obj
      f g : A ⇒ B
      s t : Scalar
      
  ----------------------------------------------------------------
  -- C1
  C1 : s ● f ≈ ρ⇒ ∘ f ⊗₁ s ∘ ρ⇐
  C1 = left-right-●
  -- C2
  C2 : (f ⊗₁ id) ∘ (id ⊗₁ g) ≈ (id ⊗₁ g) ∘ (f ⊗₁ id)
  C2 = Equiv.sym [ S×.⊗ ]-commute
  -- C3
  C3 : ω ^ 8 ≈ id
  C3 = E1
  -- C4
  C4 : H ^ 2 ≈ id
  C4 = {!!}
  -- C5
  C5 : S ^ 4 ≈ id
  C5 = {!!}
  -- C6
  C6 : (S ∘ H) ^ 3 ≈ ω ● id
  C6 = {!!}
  -- C7
  C7 : CZ ^ 2 ≈ id
  C7 = {!!}
  -- C8
  C8 : Ctrl Z ∘ (S ⊗₁ id) ≈ (S ⊗₁ id) ∘ Ctrl Z
  C8 = {!!}
  -- C9
  C9 : Ctrl Z ∘ (id ⊗₁ S) ≈ (id ⊗₁ S) ∘ Ctrl Z
  C9 = {!!}
  -- C10
  C10 : Ctrl Z ∘ (X ⊗₁ id) ≈ (X ⊗₁ Z) ∘ Ctrl Z
  C10 = ?
  -- C11
  -- C12
  -- C13
  -- C14
  -- C15
  -- C16
  -- C17
  -- C18
  -- C19
  -- C20
