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
  
  open import Categorical.Scalars SR
  open import Categorical.Gates SR
  open import Categorical.MatProp SR
  open import Categorical.2Clifford SR
  
  open Category C -- all of it
  open HomReasoning
  open SqrtRig SR
  open Kit R
  open MonR M× using (serialize₁₂; serialize₂₁)
  open MonR M⊎ using () renaming (_⟩⊗⟨_ to _⟩⊕⟨_; _⟩⊗⟨refl to _⟩⊕⟨refl; refl⟩⊗⟨_ to refl⟩⊕⟨_)

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
  CX↝CZ = begin
    id ⊗₁ H ∘ (Mat⁻¹ ∘ (id ⊕₁ X) ∘ Mat) ∘ id ⊗₁ H ≈⟨ sym-assoc ○ sym-assoc ⟩∘⟨refl ○ assoc ○ refl⟩∘⟨ assoc ⟩
    (id ⊗₁ H ∘ Mat⁻¹) ∘ (id ⊕₁ X) ∘ Mat ∘ id ⊗₁ H ≈⟨ ⟺ Mat⁻¹-2f ⟩∘⟨ refl⟩∘⟨ Mat-f-right ⟩
    (Mat⁻¹ ∘ (H ⊕₁ H)) ∘ (id ⊕₁ X) ∘ H ⊕₁ H ∘ Mat ≈⟨ assoc ○ refl⟩∘⟨ ⟺ assoc²' ⟩
    Mat⁻¹ ∘ ((H ⊕₁ H) ∘ (id ⊕₁ X) ∘ H ⊕₁ H) ∘ Mat ≈⟨ refl⟩∘⟨ (⟺ (M⊎.⊗.homomorphism ○ refl⟩∘⟨ M⊎.⊗.homomorphism) ○ (refl⟩∘⟨ identityˡ) ⟩⊕⟨refl) ⟩∘⟨refl ⟩
    Mat⁻¹ ∘ ((H ∘ H) ⊕₁ (H ∘ X ∘ H)) ∘ Mat        ≈⟨ refl⟩∘⟨ A4 ⟩⊕⟨ HXH≡Z ⟩∘⟨refl ⟩
    Mat⁻¹ ∘ (id ⊕₁ Z) ∘ Mat                       ≡⟨⟩
    Ctrl Z                                        ∎

  -- Note how this could also have been written
  -- SWAP ∘ id ⊗₁ H ∘ Ctrl X ∘ id ⊗₁ H ∘ SWAP ≈ Ctrl Z
  -- which shows how Ctrl Z is symmetric top-down
  bCX↝CZ : (H ⊗₁ id ∘ SWAP) ∘ Ctrl X ∘ (SWAP ∘ H ⊗₁ id) ≈ Ctrl Z
  bCX↝CZ = begin
     (H ⊗₁ id ∘ SWAP) ∘ Ctrl X ∘ (SWAP ∘ H ⊗₁ id) ≈⟨ ⟺ (S×.braiding.⇒.commute (id , H)) ⟩∘⟨ refl⟩∘⟨ S×.braiding.⇒.commute (H , id) ⟩
     (SWAP ∘ id ⊗₁ H) ∘ Ctrl X ∘ (id ⊗₁ H ∘ SWAP) ≈⟨ assoc ○ refl⟩∘⟨ ⟺ assoc²' ⟩
     SWAP ∘ (id ⊗₁ H ∘ Ctrl X ∘ id ⊗₁ H) ∘ SWAP   ≈⟨ refl⟩∘⟨ CX↝CZ ⟩∘⟨refl ⟩
     SWAP ∘ Ctrl Z ∘ SWAP                         ≈⟨ SWAP-CP-SWAP ⟩
     Ctrl Z                                       ∎

  -- There's a much easier proof of this that repeating the one above, viz:
  CZ↝CX :  id ⊗₁ H ∘ Ctrl Z ∘ id ⊗₁ H ≈ Ctrl X
  CZ↝CX = begin
    id ⊗₁ H ∘ Ctrl Z ∘ id ⊗₁ H                         ≈⟨ refl⟩∘⟨ ⟺ CX↝CZ ⟩∘⟨refl ⟩
    id ⊗₁ H ∘ (id ⊗₁ H ∘ Ctrl X ∘ id ⊗₁ H) ∘ id ⊗₁ H   ≈⟨ sym-assoc ○ sym-assoc ⟩∘⟨refl ○ assoc²' ⟩
    (id ⊗₁ H ∘ id ⊗₁ H) ∘ Ctrl X ∘ (id ⊗₁ H ∘ id ⊗₁ H) ≈⟨ elimˡ (bottom-cancel A4) ○ elimʳ (bottom-cancel A4) ⟩
    Ctrl X                     ∎

  -- same here
  sCZ↝bCX : H ⊗₁ id ∘ Ctrl Z ∘ H ⊗₁ id ≈ SWAP ∘ Ctrl X ∘ SWAP
  sCZ↝bCX = begin
     H ⊗₁ id ∘ Ctrl Z ∘ H ⊗₁ id                                         ≈⟨ refl⟩∘⟨ ⟺ bCX↝CZ ⟩∘⟨refl ⟩
     H ⊗₁ id ∘ ((H ⊗₁ id ∘ SWAP) ∘ Ctrl X ∘ (SWAP ∘ H ⊗₁ id)) ∘ H ⊗₁ id ≈⟨ refl⟩∘⟨ (assoc ○ assoc ○ refl⟩∘⟨ (sym-assoc ○ ⟺ assoc²' ⟩∘⟨refl ○ assoc) ) ⟩
     H ⊗₁ id ∘ H ⊗₁ id ∘ (SWAP ∘ Ctrl X ∘ SWAP) ∘ H ⊗₁ id ∘ H ⊗₁ id     ≈⟨ cancelˡ (top-cancel A4) ○ elimʳ (top-cancel A4) ⟩
     SWAP ∘ Ctrl X ∘ SWAP ∎

  sCX↝HbCX : H ⊗₁ id ∘ Ctrl X ∘ H ⊗₁ id ≈ id ⊗₁ H ∘ (SWAP ∘ Ctrl X ∘ SWAP) ∘ id ⊗₁ H
  sCX↝HbCX = begin
    H ⊗₁ id ∘ Ctrl X ∘ H ⊗₁ id                                       ≈⟨ refl⟩∘⟨ ⟺ CZ↝CX ⟩∘⟨refl ⟩
    H ⊗₁ id ∘ (id ⊗₁ H ∘ Ctrl Z ∘ id ⊗₁ H) ∘ H ⊗₁ id                 ≈⟨ refl⟩∘⟨ assoc ○ sym-assoc ○ refl⟩∘⟨ assoc ⟩
    (H ⊗₁ id ∘ id ⊗₁ H) ∘ Ctrl Z ∘ (id ⊗₁ H ∘ H ⊗₁ id)               ≈˘⟨ serialize₁₂ ⟩∘⟨ SWAP-CP-SWAP ⟩∘⟨ serialize₂₁  ⟩
    (H ⊗₁ H) ∘ (SWAP ∘ Ctrl Z ∘ SWAP) ∘ (H ⊗₁ H)                     ≈⟨ pullˡ (pullˡ (⟺ (S×.braiding.⇒.commute (H , H)))) ○ assoc ⟩∘⟨refl ○ assoc ○ refl⟩∘⟨ (pull-last (S×.braiding.⇒.commute (H , H)) ○ ⟺ assoc²') ⟩
    SWAP ∘ (H ⊗₁ H ∘ Ctrl Z ∘ H ⊗₁ H) ∘ SWAP                         ≈⟨ refl⟩∘⟨ (serialize₁₂ ⟩∘⟨ refl⟩∘⟨ serialize₂₁ ○ assoc ○ refl⟩∘⟨ (⟺ assoc²')) ⟩∘⟨refl ⟩
    SWAP ∘ (H ⊗₁ id ∘ (id ⊗₁ H ∘ Ctrl Z ∘ id ⊗₁ H) ∘ H ⊗₁ id) ∘ SWAP ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ CZ↝CX ⟩∘⟨refl) ⟩∘⟨refl ⟩
    SWAP ∘ (H ⊗₁ id ∘ Ctrl X ∘ H ⊗₁ id) ∘ SWAP                       ≈⟨ refl⟩∘⟨ assoc ○ sym-assoc ○ refl⟩∘⟨ assoc ⟩
    (SWAP ∘ H ⊗₁ id) ∘ Ctrl X ∘ (H ⊗₁ id ∘ SWAP)                     ≈⟨ S×.braiding.⇒.commute (H , id) ⟩∘⟨ refl⟩∘⟨ ⟺ (S×.braiding.⇒.commute (id , H)) ⟩
    (id ⊗₁ H ∘ SWAP) ∘ Ctrl X ∘ (SWAP ∘ id ⊗₁ H)                     ≈⟨ assoc ○ refl⟩∘⟨ {!⟺ assoc²'!} ⟩
    id ⊗₁ H ∘ (SWAP ∘ Ctrl X ∘ SWAP) ∘ id ⊗₁ H                       ∎

  ---------------------------------------------------------------
  -- lem:nctrlh
  -- How is negative control related to Ctrl ?
  nCtrl~Ctrl : (f : Endo {A}) → nCtrl f ≈ X ⊗₁ id ∘ Ctrl f ∘ X ⊗₁ id
  nCtrl~Ctrl f = {!!}

  nCtrl+inv~Ctrl : (f : Endo {A}) → f ∘ f ≈ f → nCtrl f ≈ Ctrl f ∘ id ⊗₁ f
  nCtrl+inv~Ctrl f invol = {!!}
