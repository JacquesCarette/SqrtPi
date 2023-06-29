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
  -- Full Abstraction for ≤ 2-qubit Clifford
  --
  -- First two already hold in any rig category
  -- A1
  A1 : s ● f ≈ ρ⇒ ∘ f ⊗₁ s ∘ ρ⇐
  A1 = left-right-●
  -- A2
  A2 : (f ⊗₁ id) ∘ (id ⊗₁ g) ≈ (id ⊗₁ g) ∘ (f ⊗₁ id)
  A2 = Equiv.sym [ S×.⊗ ]-commute
  ------
  -- Next ones (A3-A13) are the ones that involve square-roots
  -- A3
  A3 : ω ^ 8 ≈ id
  A3 = E1
  -- C4
  A4 : H ^ 2 ≈ id
  A4 = begin
    H ∘ H ≡⟨⟩
    H ∘ (ω ● (X ∘ S ∘ V ∘ S ∘ X))                        ≈˘⟨ ●-over-∘ ⟩
    ω ● (ω ● (X ∘ S ∘ V ∘ S ∘ X) ∘ X ∘ S ∘ V ∘ S ∘ X)    ≈⟨ {!!} ⟩
    ω ^ 2 ● ((X ∘ S ∘ V ∘ S ∘ X) ∘ X ∘ S ∘ V ∘ S ∘ X)    ≈⟨ {!!} ⟩
    ω ^ 2 ● ((X ∘ S ∘ V ∘ S) ∘ S ∘ V ∘ S ∘ X)            ≈⟨ {!!} ⟩
    id                            ∎
  -- A5
  A5 : S ^ 4 ≈ id
  A5 = {!!}
  -- A6
  A6 : (S ∘ H) ^ 3 ≈ ω ● id
  A6 = {!!}
  -- A7
  A7 : CZ ^ 2 ≈ id
  A7 = {!!}
  -- A8
  A8 : Ctrl Z ∘ (S ⊗₁ id) ≈ (S ⊗₁ id) ∘ Ctrl Z
  A8 = {!!}
  -- A9
  A9 : Ctrl Z ∘ (id ⊗₁ S) ≈ (id ⊗₁ S) ∘ Ctrl Z
  A9 = {!!}
  -- A10 (i.e. given S²≡Z and HSSH≡X this is what we need to prove
  A10 : Ctrl Z ∘ (X ⊗₁ id) ≈ (X ⊗₁ Z) ∘ Ctrl Z
  A10 = {!!}
  -- A11 (Same comments as A10)
  -- Uses 4.5(5)
  A11 : Ctrl Z ∘ (id ⊗₁ X) ≈ Z ⊗₁ X ∘ Ctrl Z
  A11 = begin
    Ctrl Z ∘ (id ⊗₁ X)                 ≈˘⟨ SWAP-CP-SWAP ⟩∘⟨refl ⟩
    (SWAP ∘ Ctrl Z ∘ SWAP) ∘ (id ⊗₁ X) ≈⟨ assoc²' ⟩
    SWAP ∘ Ctrl Z ∘ SWAP ∘ (id ⊗₁ X)   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ S×.braiding.⇒.commute (id , X) ⟩
    SWAP ∘ Ctrl Z ∘ (X ⊗₁ id) ∘ SWAP   ≈⟨ refl⟩∘⟨ {!!} ⟩
    SWAP ∘ ((X ⊗₁ Z) ∘ Ctrl Z) ∘ SWAP  ≈⟨ {!!} ⟩
    (Z ⊗₁ X) ∘ SWAP ∘ Ctrl Z ∘ SWAP    ≈⟨ refl⟩∘⟨ SWAP-CP-SWAP ⟩
    (Z ⊗₁ X) ∘ Ctrl Z                  ∎
  -- A12
  A12 : inv ω ● ((S ∘ H ∘ S) ⊗₁ S) ∘ Ctrl Z ∘ (H ∘ S) ⊗₁ id ≈ Ctrl Z ∘ (H ⊗₁ id) ∘ Ctrl Z
  A12 = {!!}
  -- A13
  A13 : inv ω ● (S ⊗₁ (S ∘ H ∘ S)) ∘ Ctrl Z ∘ id ⊗₁ (H ∘ S)  ≈ Ctrl Z ∘ (id ⊗₁ H) ∘ Ctrl Z
  A13 = {!!}

