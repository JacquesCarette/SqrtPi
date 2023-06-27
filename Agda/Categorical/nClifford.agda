{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
-- add --safe when there are no more holes

-- Soundness and Completeness for ≤ n-qubit Clifford relations

open import Categories.Category -- we need it all
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.RigCategory

open import Categorical.SqrtRig

-- Everything is over a SqrtRig
module Categorical.nClifford {o ℓ e} {C : Category o ℓ e}
  {M⊎ M× : Monoidal C} {S⊎ : Symmetric M⊎}
  {S× : Symmetric M×} {R : RigCategory C S⊎ S×} (SR : SqrtRig R) where

  open import Data.Product using (Σ; _,_)
  open import Level using (Level)

  -- open import Categories.Category.Monoidal.Interchange.Braided (Symmetric.braided S⊎) using (module swapInner)
  open import Categories.Morphism.Reasoning C
  import Categories.Category.Monoidal.Reasoning as MonR
  open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
  
  private
    module M× = Monoidal M×
    module S⊎ = Symmetric S⊎
    module S× = Symmetric S×

  open import Categorical.Scalars SR
  open import Categorical.Gates SR
  open import Categorical.MatProp SR
  
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
  Zz zZ : C [ (2C ⊗₀ 2C) ⊗₀ 2C , (2C ⊗₀ 2C) ⊗₀ 2C ]
  Zz = Ctrl Z ⊗₁ id ∘ α⇐ ∘ id ⊗₁ Ctrl Z ∘ α⇒
  zZ = α⇐ ∘ id ⊗₁ Ctrl Z ∘ α⇒ ∘ Ctrl Z ⊗₁ id
  
  B1 : zZ ≈ Zz
  B1 = {!!}

  --
  cc dd : C [ 2C ⊗₀ 2C , 2C ⊗₀ 2C ]
  cc = Ctrl Z ∘ (H ⊗₁ H) ∘ Ctrl Z
  dd = H ⊗₁ H ∘ Ctrl Z ∘ H ⊗₁ H
  
  B2 : cc ⊗₁ id ∘ id ⊗₁ dd ∘ cc ⊗₁ id ≈ id ⊗₁ cc ∘ dd ⊗₁ id ∘ id ⊗₁ cc
  B2 = {!!}

  --
  B3 : α⇐ ∘ id ⊗₁ Ctrl Z ∘ α⇒ ∘ dd ⊗₁ id ∘ Zz ∘ dd ⊗₁ id ∘ Zz ∘ dd ⊗₁ id ∘ Ctrl Z ⊗₁ id ≈ id
  B3 = {!!}

  --
  -- B4 still needs done
