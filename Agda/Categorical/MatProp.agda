{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
-- add --safe when there are no more holes

open import Categories.Category -- we need it all
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.RigCategory

open import Categorical.SqrtRig

-- Everything is over a SqrtRig
module Categorical.MatProp {o ℓ e} {C : Category o ℓ e}
  {M⊎ M× : Monoidal C} {S⊎ : Symmetric M⊎}
  {S× : Symmetric M×} {R : RigCategory C S⊎ S×} (SR : SqrtRig R) where

  open import Level using (Level)

  import Categories.Category.Monoidal.Reasoning as MonR
  open import Categories.Morphism.Reasoning C

  open import Categorical.Scalars SR
  open import Categorical.Gates SR
  
  open Category C -- all of it
  open HomReasoning
  open SqrtRig SR
  open Kit R
  open MonR M× using (_⟩⊗⟨refl)
  open MonR M⊎ using () renaming (_⟩⊗⟨refl to _⟩⊕⟨refl; _⟩⊗⟨_ to _⟩⊕⟨_)

  private
    variable
      A B : Obj
      f : A ⇒ B
      s t : Scalar
      
  ----------------------------------------------------------------
  -- Lemma lem:mat
  -- (1)
  Mat-f-right : Mat ∘ (id ⊗₁ f) ≈ (f ⊕₁ f) ∘ Mat
  Mat-f-right {f = f} = begin
    (λ⇒ ⊕₁ λ⇒ ∘ δᵣ⇒) ∘ (id ⊗₁ f)               ≈⟨ assoc ○ refl⟩∘⟨ refl⟩∘⟨ Equiv.sym M⊎.⊗.identity ⟩⊗⟨refl ⟩
    λ⇒ ⊕₁ λ⇒ ∘ δᵣ⇒ ∘ ((id ⊕₁ id) ⊗₁ f)        ≈⟨ refl⟩∘⟨ dr-commute ⟩ 
    λ⇒ ⊕₁ λ⇒ ∘ (id ⊗₁ f) ⊕₁ (id ⊗₁ f) ∘ δᵣ⇒   ≈⟨ pullˡ (Equiv.sym M⊎.⊗.homomorphism) ⟩
    (λ⇒ ∘ (id ⊗₁ f)) ⊕₁ (λ⇒ ∘ (id ⊗₁ f)) ∘ δᵣ⇒ ≈⟨ (M×.unitorˡ-commute-from ⟩⊕⟨ M×.unitorˡ-commute-from) ⟩∘⟨refl ⟩
    (f ∘ λ⇒) ⊕₁ (f ∘ λ⇒) ∘ δᵣ⇒                 ≈⟨ pushˡ M⊎.⊗.homomorphism ⟩
    f ⊕₁ f ∘ (λ⇒ ⊕₁ λ⇒) ∘ δᵣ⇒                  ∎

  -- (2)
  Mat-SWAP : Mat ∘ SWAP ≈ Midswap ∘ Mat
  Mat-SWAP = {!!}

  --- useful lemma for (3) below
  Midswap≡MSwapM⁻¹ : Midswap ≈ Mat ∘ SWAP ∘ Mat⁻¹
  Midswap≡MSwapM⁻¹ = begin
    Midswap                 ≈⟨ insertʳ Mat-invʳ ⟩
    (Midswap ∘ Mat) ∘ Mat⁻¹ ≈⟨ pushˡ (Equiv.sym Mat-SWAP) ⟩
    Mat ∘ SWAP ∘ Mat⁻¹      ∎
    
  -- (3)
  SWAP-Mat⁻¹ : SWAP ∘ Mat⁻¹ ≈ Mat⁻¹ ∘ Midswap
  SWAP-Mat⁻¹ = begin
    SWAP ∘ Mat⁻¹                 ≈⟨ insertˡ Mat-invˡ ⟩
    Mat⁻¹ ∘ (Mat ∘ SWAP ∘ Mat⁻¹) ≈˘⟨ refl⟩∘⟨ Midswap≡MSwapM⁻¹ ⟩
    Mat⁻¹ ∘ Midswap ∎

  -- (4)
  Mat-f-left : Mat ∘ (f ⊗₁ id) ≈ Midswap ∘ (f ⊕₁ f) ∘ Midswap ∘ Mat
  Mat-f-left = {!!}

  -- (5)
  SWAP-CP-SWAP : SWAP ∘ Ctrl (P s) ∘ SWAP ≈ Ctrl (P s)
  SWAP-CP-SWAP = {!!}

  -- (6)
  CP-comm : Ctrl (P s) ∘ Ctrl (P t) ≈ Ctrl (P t) ∘ Ctrl (P s)
  CP-comm = {!!}

  -- (7)
  CP-P-right : Ctrl (P s) ∘ (id ⊗₁ P s) ≈ (id ⊗₁ P s) ∘ Ctrl (P s)
  CP-P-right = {!!}
  
  -- (8)
  Mat-X-left : Mat ∘ (X ⊗₁ id {2C}) ≈ σ⊕ ∘ Mat
  Mat-X-left = {!!}
  
  -- (9) (for some reason, Agda won't infer which object Mat is over)
  Mat-P-left : {D : Obj} → Mat {D} ∘ (P s ⊗₁ id) ≈ (id ⊕₁ (s ● id)) ∘ Mat
  Mat-P-left = {!!}

  ----------------------------------------------------------------
  -- Lemma lem:had
  HXH≡Z : H ∘ X ∘ H ≈ Z
  HXH≡Z = {!!}

  HZH≡X : H ∘ Z ∘ H ≈ X
  HZH≡X = {!!}

  -----------------------------------------------------------------
  -- useful corrolaries
  HSSH≡X : H ∘ S ∘ S ∘ H ≈ X
  HSSH≡X = begin
    H ∘ S ∘ S ∘ H ≈⟨ pull-center S²≡Z ⟩
    H ∘ Z ∘ H     ≈⟨ HZH≡X ⟩
    X             ∎
