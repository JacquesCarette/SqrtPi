{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
-- add --safe when there are no more holes

open import Categories.Category -- we need it all
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.RigCategory

open import Categorical.SqrtRig

-- Everything is over a SqrtRig
module Categorical.SleatorWeinfurter {o ℓ e} {C : Category o ℓ e}
  {M⊎ M× : Monoidal C} {S⊎ : Symmetric M⊎}
  {S× : Symmetric M×} {R : RigCategory C S⊎ S×} (SR : SqrtRig R) where

  open import Data.Product using (_,_)
  open import Level using (Level)

  open import Categories.Category.Monoidal.Properties using (module Kelly's)
  open import Categories.Category.Monoidal.Utilities using (module Shorthands)
  open Shorthands M⊎ using () renaming (α⇒ to ⊕α⇒; α⇐ to ⊕α⇐)
  import Categories.Category.Monoidal.Reasoning as MonR
  open import Categories.Morphism.Reasoning C

  open import Categorical.Scalars SR
  open import Categorical.Gates SR
  
  open SqrtRig SR
  open MonR M× using (_⟩⊗⟨refl)
  open MonR M⊎ using (parallel; split₁ˡ)
    renaming (_⟩⊗⟨refl to _⟩⊕⟨refl; _⟩⊗⟨_ to _⟩⊕⟨_; refl⟩⊗⟨_ to refl⟩⊕⟨_;
    ⊗-distrib-over-∘ to ⊕-distrib-over-∘)

  private
    variable
      A B W₁ W₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Obj
      f g f₁ f₂ f₃ g₁ g₂ g₃ : A ⇒ B

  ---------------------------------------------------------------------------------------

  3Q : Obj
  3Q = 2C ⊗₀ 2C ⊗₀ 2C
  
  3Mat : 2C ⊗₀ 2C ⊗₀ A ⇒ (A ⊕₀ A) ⊕₀ (A ⊕₀ A)
  3Mat = Mat ⊕₁ Mat ∘ Mat

  3Mat⁻¹ : (A ⊕₀ A) ⊕₀ (A ⊕₀ A) ⇒ 2C ⊗₀ 2C ⊗₀ A
  3Mat⁻¹ = Mat⁻¹ ∘ Mat⁻¹ ⊕₁ Mat⁻¹

  Ctrl₁₃V : 3Q ⇒ 3Q
  Ctrl₁₃V = 3Mat⁻¹ ∘ (id ⊕₁ (V ⊕₁ V)) ∘ 3Mat

  -- V† = V³ = VX.
  V† : 2C ⇒ 2C
  V† = V ∘ X
  
  Ctrl₂₃VX : 3Q ⇒ 3Q
  Ctrl₂₃VX = 3Mat⁻¹ ∘ (id ⊕₁ V†) ⊕₁ (id ⊕₁ V†) ∘ 3Mat

  Ctrl₂₃V : 3Q ⇒ 3Q
  Ctrl₂₃V = 3Mat⁻¹ ∘ (id ⊕₁ V) ⊕₁ (id ⊕₁ V) ∘ 3Mat

  -- be precise about the arguments here, to help inference
  CNOT₁₂ : 3Q ⇒ 3Q
  CNOT₁₂ = 3Mat⁻¹ ∘ (id {A = 2C ⊕₀ 2C} ⊕₁ σ⊕ {X = 2C} {Y = 2C}) ∘ 3Mat

  ----------------------------------------------------------------------------------
  -- lemma that should be moved elsewhere, but useful here
  -- note the weird order, i.e. first-occurence!
  cancelInner3 : f₃ ∘ g₁ ≈ id → (f₁ ∘ f₂ ∘ f₃) ∘ (g₁ ∘ g₂ ∘ g₃) ≈ (f₁ ∘ f₂) ∘ g₂ ∘ g₃
  cancelInner3 {f₃ = f₃} {g₁} {f₁ = f₁} {f₂} {g₂ = g₂} {g₃ = g₃} fg≈id = begin
    (f₁ ∘ f₂ ∘ f₃) ∘ (g₁ ∘ g₂ ∘ g₃)   ≈⟨ sym-assoc ⟩∘⟨refl ⟩
    ((f₁ ∘ f₂) ∘ f₃) ∘ (g₁ ∘ g₂ ∘ g₃) ≈⟨ cancelInner fg≈id ⟩
    (f₁ ∘ f₂) ∘ g₂ ∘ g₃ ∎

  -- 3Mat inverse
  3Mat-inv : 3Mat {A} ∘ 3Mat⁻¹ ≈ id
  3Mat-inv = begin
    (Mat ⊕₁ Mat ∘ Mat) ∘ Mat⁻¹ ∘ Mat⁻¹ ⊕₁ Mat⁻¹ ≈⟨ cancelInner Mat-invʳ ⟩
    Mat ⊕₁ Mat ∘ Mat⁻¹ ⊕₁ Mat⁻¹                 ≈˘⟨ M⊎.⊗.homomorphism ⟩
    (Mat ∘ Mat⁻¹) ⊕₁ (Mat ∘ Mat⁻¹)              ≈⟨ Mat-invʳ ⟩⊕⟨ Mat-invʳ ⟩
    id ⊕₁ id                                    ≈⟨ M⊎.⊗.identity ⟩
    id                                          ∎
    

  -- the core of the SL identity
  additive-SL : ((id ⊕₁ (V ⊕₁ V))) ∘ (id ⊕₁ σ⊕) ∘ ((id {A = 2C} ⊕₁ V†) ⊕₁ (id ⊕₁ V†)) ∘
    (id ⊕₁ σ⊕) ∘ ((id ⊕₁ V) ⊕₁ (id ⊕₁ V)) ≈ (id ⊕₁ id) ⊕₁ (id ⊕₁ X)
  additive-SL = begin
    (id ⊕₁ (V ⊕₁ V)) ∘ (id ⊕₁ σ⊕) ∘
    ((id ⊕₁ V†) ⊕₁ (id ⊕₁ V†)) ∘
    (id ⊕₁ σ⊕) ∘ ((id ⊕₁ V) ⊕₁ (id ⊕₁ V))
        ≈⟨ refl⟩∘⟨ pullˡ (parallel id-comm-sym (S⊎.braiding.⇒.commute (id , V†))) ⟩
    (id ⊕₁ (V ⊕₁ V)) ∘ (((id ⊕₁ V†) ⊕₁ (V† ⊕₁ id)) ∘
    (id ⊕₁ σ⊕)) ∘
    (id ⊕₁ σ⊕) ∘ ((id ⊕₁ V) ⊕₁ (id ⊕₁ V))
        ≈⟨ refl⟩∘⟨ cancelInner (⟺ M⊎.⊗.homomorphism ○ identity² ⟩⊕⟨ S⊎.commutative ○ M⊎.⊗.identity ) ⟩
    (id ⊕₁ (V ⊕₁ V)) ∘ ((id ⊕₁ V†) ⊕₁ (V† ⊕₁ id)) ∘
    ((id ⊕₁ V) ⊕₁ (id ⊕₁ V))
        ≈⟨ Equiv.sym (M⊎.⊗.homomorphism ○ refl⟩∘⟨ M⊎.⊗.homomorphism) ⟩
    (id ∘ (id ⊕₁ V†) ∘ (id ⊕₁ V)) ⊕₁ ((V ⊕₁ V) ∘ (V† ⊕₁ id) ∘ (id ⊕₁ V))
        ≈⟨ (identityˡ ○ ⟺ M⊎.⊗.homomorphism) ⟩⊕⟨ ⟺ (M⊎.⊗.homomorphism ○ refl⟩∘⟨ M⊎.⊗.homomorphism) ⟩
    ((id ∘ id) ⊕₁ (V† ∘ V)) ⊕₁ ((V ∘ V† ∘ id) ⊕₁ (V ∘ id ∘ V))
        ≈⟨ (identity² ⟩⊕⟨ VXV≡id) ⟩⊕⟨ (((refl⟩∘⟨ identityʳ) ○ VVX≡id) ⟩⊕⟨ (refl⟩∘⟨ identityˡ ○ E2)) ⟩
    (id ⊕₁ id) ⊕₁ (id ⊕₁ X) ∎
  
  -- since this is huge, use a lot more vertical space for layout
  SL₁ : Ctrl₁₃V ∘ CNOT₁₂ ∘ Ctrl₂₃VX ∘ CNOT₁₂ ∘ Ctrl₂₃V ≈ 3Mat⁻¹ ∘ (id ⊕₁ id) ⊕₁ (id ⊕₁ X) ∘ 3Mat
  SL₁ = begin
    (3Mat⁻¹ ∘ (id ⊕₁ (V ⊕₁ V)) ∘ 3Mat) ∘
    (3Mat⁻¹ ∘ (id ⊕₁ σ⊕) ∘ 3Mat) ∘
    (3Mat⁻¹ ∘ (id ⊕₁ V†) ⊕₁ (id ⊕₁ V†) ∘ 3Mat) ∘
    (3Mat⁻¹ ∘ (id ⊕₁ σ⊕) ∘ 3Mat) ∘
    (3Mat⁻¹ ∘ (id ⊕₁ V) ⊕₁ (id ⊕₁ V) ∘ 3Mat)
                                        ≈⟨ extendʳ (cancelInner3 3Mat-inv) ⟩
    (3Mat⁻¹ ∘ (id ⊕₁ (V ⊕₁ V))) ∘
    ((id ⊕₁ σ⊕) ∘ 3Mat) ∘
    (3Mat⁻¹ ∘ (id ⊕₁ V†) ⊕₁ (id ⊕₁ V†) ∘ 3Mat) ∘
    (3Mat⁻¹ ∘ (id ⊕₁ σ⊕) ∘ 3Mat) ∘
    (3Mat⁻¹ ∘ (id ⊕₁ V) ⊕₁ (id ⊕₁ V) ∘ 3Mat)
                                        ≈⟨ refl⟩∘⟨ extendʳ (cancelInner 3Mat-inv) ⟩
    (3Mat⁻¹ ∘ (id ⊕₁ (V ⊕₁ V))) ∘
    (id ⊕₁ σ⊕) ∘
    ((id ⊕₁ V†) ⊕₁ (id ⊕₁ V†) ∘ 3Mat) ∘
    (3Mat⁻¹ ∘ (id ⊕₁ σ⊕) ∘ 3Mat) ∘
    (3Mat⁻¹ ∘ (id ⊕₁ V) ⊕₁ (id ⊕₁ V) ∘ 3Mat)
                                         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (cancelInner 3Mat-inv) ⟩
    (3Mat⁻¹ ∘ (id ⊕₁ (V ⊕₁ V))) ∘
    (id ⊕₁ σ⊕) ∘
    ((id ⊕₁ V†) ⊕₁ (id ⊕₁ V†)) ∘
    ((id ⊕₁ σ⊕) ∘ 3Mat) ∘
    (3Mat⁻¹ ∘ (id ⊕₁ V) ⊕₁ (id ⊕₁ V) ∘ 3Mat)
                                         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelInner 3Mat-inv ⟩
    (3Mat⁻¹ ∘ (id ⊕₁ (V ⊕₁ V))) ∘
    (id ⊕₁ σ⊕) ∘
    ((id ⊕₁ V†) ⊕₁ (id ⊕₁ V†)) ∘
    (id ⊕₁ σ⊕) ∘
    ((id ⊕₁ V) ⊕₁ (id ⊕₁ V) ∘ 3Mat)
                                        ≈⟨ assoc ○ refl⟩∘⟨ (sym-assoc ○ sym-assoc ○
                                           refl⟩∘⟨ sym-assoc ○ sym-assoc ○
                                           (assoc ○ assoc) ⟩∘⟨refl) ⟩
    3Mat⁻¹ ∘ ((id ⊕₁ (V ⊕₁ V)) ∘
    (id ⊕₁ σ⊕) ∘
    ((id ⊕₁ V†) ⊕₁ (id ⊕₁ V†)) ∘
    (id ⊕₁ σ⊕) ∘
    ((id ⊕₁ V) ⊕₁ (id ⊕₁ V))) ∘ 3Mat    ≈⟨ refl⟩∘⟨ additive-SL ⟩∘⟨refl ⟩
    3Mat⁻¹ ∘ (id ⊕₁ id) ⊕₁ (id ⊕₁ X) ∘ 3Mat        ∎

  SL₂ : 3Mat⁻¹ ∘ (id ⊕₁ id) ⊕₁ (id ⊕₁ X) ∘ 3Mat ≈ CCX
  SL₂ = begin
    (Mat⁻¹ ∘ Mat⁻¹ ⊕₁ Mat⁻¹) ∘ (id ⊕₁ id) ⊕₁ (id ⊕₁ X) ∘ Mat ⊕₁ Mat ∘ Mat
        ≈⟨ assoc ○ refl⟩∘⟨ ⟺ assoc²' ⟩
    Mat⁻¹ ∘ (Mat⁻¹ ⊕₁ Mat⁻¹ ∘ (id ⊕₁ id) ⊕₁ (id ⊕₁ X) ∘ Mat ⊕₁ Mat) ∘ Mat
        ≈˘⟨ refl⟩∘⟨ (M⊎.⊗.homomorphism ○ refl⟩∘⟨ M⊎.⊗.homomorphism) ⟩∘⟨refl ⟩
    Mat⁻¹ ∘ (Mat⁻¹ ∘ (id ⊕₁ id) ∘ Mat) ⊕₁ (Mat⁻¹ ∘ (id ⊕₁ X) ∘ Mat) ∘ Mat
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ elimˡ M⊎.⊗.identity ○ Mat-invˡ) ⟩⊕⟨refl ⟩∘⟨refl ⟩
    Mat⁻¹ ∘ (id ⊕₁ (Mat⁻¹ ∘ (id ⊕₁ X) ∘ Mat)) ∘ Mat                       ∎
