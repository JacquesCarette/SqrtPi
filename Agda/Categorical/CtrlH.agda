{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
-- add --safe when there are no more holes

-- Various lemmas about Hadamard and controlled gates

open import Categories.Category -- we need it all
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.RigCategory

open import Categorical.SqrtRig

-- Everything is over a SqrtRig
module Categorical.CtrlH {o ℓ e} {C : Category o ℓ e}
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
  -- lem:ctrlh
  --
  -- Here we use ↝ to mean "becomes under conjugation with id ⊗₁ H",
  -- a prefix 'b' to mean bottom-controlled
  -- a prefix 's' means conjugation with H ⊗₁ id (i.e. swapped H)
  -- a prefix 'H' on the right means an additional conjugation with id ⊗₁ H
  CX↝CZ : id ⊗₁ H ∘ Ctrl X ∘ id ⊗₁ H ≈ Ctrl Z
  CX↝CZ = {!!}

  -- Note how this could also have been written
  -- SWAP ∘ id ⊗₁ H ∘ Ctrl X ∘ id ⊗₁ H ∘ SWAP ≈ Ctrl Z
  -- which shows how Ctrl Z is symmetric top-down
  bCX↝CZ : H ⊗₁ id ∘ SWAP ∘ Ctrl X ∘ SWAP ∘ H ⊗₁ id ≈ Ctrl Z
  bCX↝CZ = {!!}

  CZ↝CX :  id ⊗₁ H ∘ Ctrl Z ∘ id ⊗₁ H ≈ Ctrl X
  CZ↝CX = {!!}

  sCZ↝bCX :  H ⊗₁ id ∘ Ctrl Z ∘ H ⊗₁ id ≈ SWAP ∘ Ctrl X ∘ SWAP
  sCZ↝bCX = ?

  sCX↝HbCX : H ⊗₁ id ∘ Ctrl X ∘ H ⊗₁ id ≈ id ⊗₁ H ∘ SWAP ∘ Ctrl X ∘ SWAP ∘ id ⊗₁ H
  sCX↝HbCX = ?
  
