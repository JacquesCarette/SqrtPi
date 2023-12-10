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
  
  open import Categorical.Scalars SR
  open import Categorical.Gates SR
  open import Categorical.MatProp SR
  open import Categorical.CtrlH SR
  
  open SqrtRig SR

  module Q = MonR M×
  private
    variable
      A B : Obj
      f g : A ⇒ B
      s t : Scalar

  split₂ˡ² : ∀ {X₁ Y₁ M₂ X₂ Y₂ Z₂} {i : X₁ ⇒ Y₁} {f : Y₂ ⇒ Z₂} {g : X₂ ⇒ Y₂} {h : M₂ ⇒ X₂} → 
            i ⊗₁ (f ∘ g ∘ h) ≈ id ⊗₁ f ∘ id ⊗₁ g ∘ i ⊗₁ h
  split₂ˡ² {i = i} {f} {g} {h} = Equiv.trans Q.split₂ˡ (∘-resp-≈ʳ Q.split₂ˡ)

  split₂ʳ² : ∀ {X₁ Y₁ M₂ X₂ Y₂ Z₂} {i : X₁ ⇒ Y₁} {f : Y₂ ⇒ Z₂} {g : X₂ ⇒ Y₂} {h : M₂ ⇒ X₂} → 
            (f ∘ g ∘ h) ⊗₁ i ≈ f ⊗₁ i ∘ g ⊗₁ id ∘ h ⊗₁ id
  split₂ʳ² {i = i} {f} {g} {h} = Equiv.trans Q.split₁ʳ (refl⟩∘⟨ Q.split₁ʳ)

  postulate
    P1 : α⇐ ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ≈
         (Ctrl X ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ SWAP) ∘ (id ⊗₁ Ctrl X) ∘ α⇒
  ----------------------------------------------------------------
  Zz zZ : C [ (2C ⊗₀ 2C) ⊗₀ 2C , (2C ⊗₀ 2C) ⊗₀ 2C ]
  Zz = Ctrl Z ⊗₁ id ∘ α⇐ ∘ id ⊗₁ Ctrl Z ∘ α⇒
  zZ = α⇐ ∘ id ⊗₁ Ctrl Z ∘ α⇒ ∘ Ctrl Z ⊗₁ id

  B1 : zZ ≈ Zz
  B1 = begin
    α⇐ ∘ id ⊗₁ Ctrl Z ∘ α⇒ ∘ Ctrl Z ⊗₁ id ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⟺ CX↝CZ) ⟩∘⟨ refl⟩∘⟨ (⟺ bCX↝CZ ⟩⊗⟨refl) ⟩
    α⇐ ∘ id ⊗₁ (id ⊗₁ H ∘ Ctrl X ∘ id ⊗₁ H) ∘ 
      α⇒ ∘ ((H ⊗₁ id ∘ SWAP) ∘ Ctrl X ∘ (SWAP ∘ H ⊗₁ id)) ⊗₁ id ≈⟨ refl⟩∘⟨ split₂ˡ² ⟩∘⟨ refl⟩∘⟨ split₂ʳ² ⟩ 
    α⇐ ∘ (id ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ id ⊗₁ id ⊗₁ H) ∘ 
      α⇒ ∘ (H ⊗₁ id ∘ SWAP) ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ (SWAP ∘ H ⊗₁ id) ⊗₁ id  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (Q.split₁ʳ ⟩∘⟨ refl⟩∘⟨ Q.split₁ʳ) ⟩
    α⇐ ∘ (id ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ id ⊗₁ id ⊗₁ H) ∘ 
      α⇒ ∘ ((H ⊗₁ id) ⊗₁ id ∘ SWAP ⊗₁ id) ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc²'' ⟩  
    α⇐ ∘ (id ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ id ⊗₁ id ⊗₁ H) ∘
      (α⇒ ∘ (H ⊗₁ id) ⊗₁ id) ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (Equiv.trans (M×.assoc-commute-from ⟩∘⟨refl) assoc) ⟩
    α⇐ ∘ (id ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ id ⊗₁ id ⊗₁ H) ∘
      H ⊗₁ id ⊗₁ id ∘ α⇒ ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id  ≈⟨ {!!} ⟩
    α⇐ ∘ H ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ id ⊗₁ id ⊗₁ id ∘
      id ⊗₁ id ⊗₁ id ∘ α⇒ ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ H   ≈⟨ {!!} ⟩
    α⇐ ∘ H ⊗₁ (id ⊗₁ H) ∘ id ⊗₁ Ctrl X ∘ 
      α⇒ ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ H   ≈⟨ {!!} ⟩
    (H ⊗₁ id) ⊗₁ H ∘
      (α⇐ ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id)
      ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ H                                  ≈⟨ {!!} ⟩
    (H ⊗₁ id) ⊗₁ H ∘
      ((Ctrl X ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ SWAP) ∘ (id ⊗₁ Ctrl X) ∘ α⇒)
      ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ H                                  ≈⟨ {!!} ⟩
    Ctrl Z ⊗₁ id ∘ α⇐ ∘ id ⊗₁ Ctrl Z ∘ α⇒ ∎

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
  B4 : Ctrl Z ⊗₁ id ∘ α⇐ ∘ id ⊗₁ dd ∘ α⇒ ∘ zZ ∘ α⇐ ∘ id ⊗₁ dd ∘ α⇒ ∘ zZ
                          ∘ α⇐ ∘ id ⊗₁ dd ∘ id ⊗₁ Ctrl Z ∘ α⇒ ≈ id
  B4 = {!!}
