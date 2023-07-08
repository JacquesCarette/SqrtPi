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
  
  open import Categorical.Scalars SR
  open import Categorical.Gates SR
  open import Categorical.MatProp SR
  
  open Category C -- all of it
  open HomReasoning
  open SqrtRig SR
  open Kit R
  open MonR M× using (serialize₁₂)
  open MonR M⊎ using () renaming (_⟩⊗⟨_ to _⟩⊕⟨_)

  private
    variable
      A B : Obj
      f g : A ⇒ B
      s t : Scalar

  ----------------------------------------------------------------
  -- As usual, some lemmas used implicitly need proof
  E3-inv : S ∘ V ∘ S ≈ ω ^ 6 ● (V ∘ S ∘ V)
  E3-inv = begin
    S ∘ V ∘ S                     ≈˘⟨ 𝟙●f≈f _ ⟩
    𝟙 ● (S ∘ V ∘ S)               ≈⟨ ●-congˡ (⟺ E1) ⟩
    ω ^ 8 ● (S ∘ V ∘ S)           ≈⟨ ●-congˡ (⟺ (^-add ω 6 2)) ⟩
    (ω ^ 6 ∘ ω ^ 2) ● (S ∘ V ∘ S) ≈˘⟨ push-scalar-left ⟩
    ω ^ 6 ● (ω ^ 2 ● (S ∘ V ∘ S)) ≈⟨ ●-congʳ (⟺ E3) ⟩
    ω ^ 6 ● (V ∘ S ∘ V) ∎
  
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
    H ∘ H                                                ≡⟨⟩
    H ∘ (ω ● (X ∘ S ∘ V ∘ S ∘ X))                        ≈˘⟨ ●-over-∘ ⟩
    ω ● (ω ● (X ∘ S ∘ V ∘ S ∘ X) ∘ X ∘ S ∘ V ∘ S ∘ X)    ≈⟨ ●-congʳ ●-assocʳ ○ push-scalar-left ⟩
    ω ^ 2 ● ((X ∘ S ∘ V ∘ S ∘ X) ∘ X ∘ S ∘ V ∘ S ∘ X)    ≈⟨ ●-congʳ (sym-assoc ○ pull-last (sym-assoc ⟩∘⟨refl ○ cancelʳ X²≡id) ⟩∘⟨refl) ⟩
    i ● ((X ∘ S ∘ V ∘ S) ∘ S ∘ V ∘ S ∘ X)                ≈⟨ ●-congʳ ((refl⟩∘⟨ E3-inv) ⟩∘⟨ (⟺ assoc²' ○ E3-inv ⟩∘⟨refl)) ⟩
    i ● ((X ∘ ω ^ 6 ● (V ∘ S ∘ V)) ∘ (ω ^ 6 ● (V ∘ S ∘ V) ∘ X)) ≈⟨ extract-scalar3 ⟩
    (i ∘ ω ^ 6) ● ((X ∘ ω ^ 6 ● (V ∘ S ∘ V)) ∘ ((V ∘ S ∘ V) ∘ X)) ≈⟨ ●-cong (^-add ω 2 6) assoc ⟩
    ω ^ 8 ● (X ∘ ω ^ 6 ● (V ∘ S ∘ V) ∘ ((V ∘ S ∘ V) ∘ X)) ≈⟨ extract-scalar3 ⟩
    (ω ^ 8 ∘ ω ^ 6) ● (X ∘ (V ∘ S ∘ V) ∘ ((V ∘ S ∘ V) ∘ X)) ≈⟨ ●-cong (E1 ⟩∘⟨refl) (refl⟩∘⟨ sym-assoc ⟩∘⟨ assoc)  ⟩
    (𝟙 ∘ ω ^ 6) ● (X ∘ ((V ∘ S) ∘ V) ∘ V ∘ (S ∘ V) ∘ X)   ≈⟨ ●-cong identityˡ (refl⟩∘⟨ center E2) ⟩
    ω ^ 6 ● (X ∘ (V ∘ S) ∘ X ∘ (S ∘ V) ∘ X)               ≈⟨ ●-congʳ (refl⟩∘⟨ assoc ○ sym-assoc ○ refl⟩∘⟨ (sym-assoc ○ refl⟩∘⟨ assoc ○ pullˡ assoc) ) ⟩
    ω ^ 6 ● ((X ∘ V) ∘ (S ∘ X ∘ S) ∘ (V ∘ X))             ≈⟨ ●-congʳ (refl⟩∘⟨ PXP i ⟩∘⟨refl) ⟩
    ω ^ 6 ● ((X ∘ V) ∘ (i ● X) ∘ V ∘ X)                   ≈⟨ extract-scalar3 ⟩
    (ω ^ 6 ∘ ω ^ 2) ● ((X ∘ V) ∘ X ∘ V ∘ X)               ≈⟨ ●-cong (^-add ω 6 2) (XV-comm ⟩∘⟨refl) ⟩
    ω ^ 8 ● ((V ∘ X) ∘ X ∘ V ∘ X)                         ≈⟨ ●-congˡ E1 ○ 𝟙●f≈f _ ⟩
    (V ∘ X) ∘ X ∘ V ∘ X                                   ≈⟨ cancelInner X²≡id ⟩
    V ∘ V ∘ X                                             ≈⟨ pullˡ E2 ⟩
    X ∘ X                                                 ≈⟨ X²≡id ⟩
    id                                                    ∎
  -- A5
  A5 : S ^ 4 ≈ id
  A5 = begin
    (P i) ^ 4             ≈⟨ sym-assoc ⟩
    (P i) ^ 2 ∘ (P i) ^ 2 ≈⟨ P² i ⟩∘⟨ P² i ⟩
    (P (i ^ 2)) ^ 2       ≈⟨ P² (i ∘ i) ⟩
    P (i ^ 2 ∘ i ^ 2)     ≈⟨ cong-P (^-add i 2 2 ○ i⁴≡𝟙) ⟩
    id ⊕₁ id              ≈⟨ M⊎.⊗.identity ⟩
    id        ∎
  -- A6
  -- prelim lemma
  SH-expand : S ∘ H ≈ ω ^ 3 ● (X ∘ V ∘ S ∘ X)
  SH-expand = begin
    S ∘ ω ● (X ∘ S ∘ V ∘ S ∘ X)   ≈˘⟨ ●-over-∘ ⟩
    ω ● (S ∘ X ∘ S ∘ V ∘ S ∘ X)   ≈⟨ ●-congʳ (⟺ assoc²' ○ PXP i ⟩∘⟨refl) ⟩
    ω ● ((ω ^ 2 ● X) ∘ V ∘ S ∘ X) ≈⟨ ●-congʳ ●-assocʳ ⟩
    ω ● (ω ^ 2 ● (X ∘ V ∘ S ∘ X)) ≈⟨ push-scalar-left ⟩
    ω ^ 3 ● (X ∘ V ∘ S ∘ X)       ∎
  
  A6 : (S ∘ H) ^ 3 ≈ ω ● id
  A6 = begin
    (S ∘ H) ^ 3                   ≈⟨ base^-cong SH-expand 3 ⟩
    (ω ^ 3 ● (X ∘ V ∘ S ∘ X)) ^ 3 ≡⟨⟩
    ω ^ 3 ● (X ∘ V ∘ S ∘ X) ∘ ω ^ 3 ● (X ∘ V ∘ S ∘ X) ∘ ω ^ 3 ● (X ∘ V ∘ S ∘ X)
        ≈⟨ refl⟩∘⟨ merge-scalars  ⟩
    ω ^ 3 ● (X ∘ V ∘ S ∘ X) ∘ (ω ^ 3 ∘ ω ^ 3) ● ((X ∘ V ∘ S ∘ X) ∘ X ∘ V ∘ S ∘ X)
        ≈⟨ merge-scalars ⟩
    (ω ^ 3 ∘ ω ^ 3 ∘ ω ^ 3) ● ((X ∘ V ∘ S ∘ X) ∘ (X ∘ V ∘ S ∘ X) ∘ X ∘ V ∘ S ∘ X)
        ≈⟨ ●-cong (refl⟩∘⟨ ^-add ω 3 3) (pullˡ (pull-last (cancelInner X²≡id))) ⟩
    (ω ^ 3 ∘ ω ^ 6) ● ((X ∘ V ∘ S ∘ V ∘ S ∘ X) ∘ X ∘ V ∘ S ∘ X)
        ≈⟨ ●-cong (^-add ω 3 6) (pull-last (pull-last (cancelInner X²≡id))) ⟩
    ω ^ 9 ● (X ∘ V ∘ S ∘ V ∘ S ∘ V ∘ S ∘ X)
        ≈⟨ ●-cong (ω⁸⁺ᵃ≡ωᵃ {1}) (refl⟩∘⟨ (⟺ assoc²' ○ E3 ⟩∘⟨refl)) ⟩
    ω ● (X ∘ (ω ^ 2 ● (S ∘ V ∘ S) ∘ S ∘ V ∘ S ∘ X))
        ≈⟨ extract-scalar3 ⟩
    ω ^ 3 ● (X ∘ (S ∘ V ∘ S) ∘ S ∘ V ∘ S ∘ X)
        ≈⟨ ●-congʳ (refl⟩∘⟨ ⟺ (cancelInner X²≡id)) ⟩
    ω ^ 3 ● (X ∘ ((S ∘ V ∘ S) ∘ X) ∘ X ∘ S ∘ V ∘ S ∘ X)
        ≈⟨ ●-cong (⟺ (^-add ω 2 1)) (sym-assoc ○ (refl⟩∘⟨ (assoc ○ refl⟩∘⟨ assoc)) ⟩∘⟨refl) ⟩
    (ω ^ 2 ∘ ω) ● ((X ∘ S ∘ V ∘ S ∘ X) ∘ X ∘ S ∘ V ∘ S ∘ X)
        ≈˘⟨ extract-scalar2 ⟩
    ω ^ 2 ● ((X ∘ S ∘ V ∘ S ∘ X) ∘ ω ● (X ∘ S ∘ V ∘ S ∘ X))
        ≈⟨ ⟺ push-scalar-left ○ ●-congʳ ●-assocˡ ⟩
    ω ● (ω ● (X ∘ S ∘ V ∘ S ∘ X) ∘ ω ● (X ∘ S ∘ V ∘ S ∘ X))
        ≡⟨⟩
    ω ● (H ∘ H)
        ≈⟨ ●-congʳ A4 ⟩
    ω ● id      ∎
  -- A7
  A7 : CZ ^ 2 ≈ id
  A7 = CZ²≡id
  -- A8
  A8 : Ctrl Z ∘ (S ⊗₁ id) ≈ (S ⊗₁ id) ∘ Ctrl Z
  A8 = begin
    Ctrl Z ∘ (S ⊗₁ id)                 ≈⟨ ⟺ SWAP-CP-SWAP ⟩∘⟨refl ⟩
    (SWAP ∘ Ctrl Z ∘ SWAP) ∘ (S ⊗₁ id) ≈⟨ assoc ○ refl⟩∘⟨ pullʳ (S×.braiding.⇒.commute (S , id)) ⟩
    SWAP ∘ (Ctrl Z ∘ (id ⊗₁ S) ∘ SWAP) ≈⟨ refl⟩∘⟨ pullˡ (CP-P-right (^-comm 4 2)) ⟩
    SWAP ∘ ((id ⊗₁ S) ∘ Ctrl Z) ∘ SWAP ≈⟨ pull-first (S×.braiding.⇒.commute (id , S)) ○ assoc ⟩
    (S ⊗₁ id) ∘ SWAP ∘ Ctrl Z ∘ SWAP    ≈⟨ refl⟩∘⟨ SWAP-CP-SWAP ⟩
    (S ⊗₁ id) ∘ Ctrl Z ∎ 
  -- A9
  A9 : Ctrl Z ∘ (id ⊗₁ S) ≈ (id ⊗₁ S) ∘ Ctrl Z
  A9 = CP-P-right (^-comm 4 2)
  
  -- A10 (i.e. given S²≡Z and HSSH≡X this is what we need to prove
  A10 : Ctrl Z ∘ (X ⊗₁ id) ≈ (X ⊗₁ Z) ∘ Ctrl Z
  A10 = begin
    (Mat⁻¹ ∘ (id ⊕₁ Z) ∘ Mat) ∘ (X ⊗₁ id)               ≈⟨ sym-assoc ⟩∘⟨refl ○ pullʳ Mat-X-left ⟩
    (Mat⁻¹ ∘ (id ⊕₁ Z)) ∘ σ⊕ ∘ Mat                      ≈⟨ center (⟺ (S⊎.braiding.⇒.commute (Z , id))) ⟩
    Mat⁻¹ ∘ (σ⊕ ∘ (Z ⊕₁ id)) ∘ Mat                      ≈⟨ pull-first Mat⁻¹σ ⟩
    ((X ⊗₁ id) ∘ Mat⁻¹) ∘ (Z ⊕₁ id) ∘ Mat               ≈˘⟨ refl⟩∘⟨ identityʳ ⟩⊕⟨ Z²≡id ⟩∘⟨refl ⟩
    ((X ⊗₁ id) ∘ Mat⁻¹) ∘ ((Z ∘ id) ⊕₁ (Z ∘ Z)) ∘ Mat   ≈⟨ refl⟩∘⟨ M⊎.⊗.homomorphism ⟩∘⟨refl ⟩
    ((X ⊗₁ id) ∘ Mat⁻¹) ∘ ((Z ⊕₁ Z) ∘ (id ⊕₁ Z)) ∘ Mat  ≈⟨ sym-assoc ○ center Mat⁻¹-2f ⟩∘⟨refl ⟩
    ((X ⊗₁ id) ∘ ((id ⊗₁ Z) ∘ Mat⁻¹) ∘ (id ⊕₁ Z)) ∘ Mat ≈⟨ assoc ○ refl⟩∘⟨ assoc ○ pull-first (⟺ serialize₁₂) ⟩
    (X ⊗₁ Z) ∘ Mat⁻¹ ∘ (id ⊕₁ Z) ∘ Mat    ∎
  
  -- A11 (Same comments as A10)
  -- Uses 4.5(5)
  A11 : Ctrl Z ∘ (id ⊗₁ X) ≈ Z ⊗₁ X ∘ Ctrl Z
  A11 = begin
    Ctrl Z ∘ (id ⊗₁ X)                 ≈˘⟨ SWAP-CP-SWAP ⟩∘⟨refl ⟩
    (SWAP ∘ Ctrl Z ∘ SWAP) ∘ (id ⊗₁ X) ≈⟨ assoc²' ⟩
    SWAP ∘ Ctrl Z ∘ SWAP ∘ (id ⊗₁ X)   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ S×.braiding.⇒.commute (id , X) ⟩
    SWAP ∘ Ctrl Z ∘ (X ⊗₁ id) ∘ SWAP   ≈⟨ refl⟩∘⟨ pullˡ A10 ⟩
    SWAP ∘ ((X ⊗₁ Z) ∘ Ctrl Z) ∘ SWAP  ≈⟨ pull-first (S×.braiding.⇒.commute (X , Z)) ○ assoc ⟩
    (Z ⊗₁ X) ∘ SWAP ∘ Ctrl Z ∘ SWAP    ≈⟨ refl⟩∘⟨ SWAP-CP-SWAP ⟩
    (Z ⊗₁ X) ∘ Ctrl Z                  ∎

  -- prelim lemmas
  -- A12
  A12 : ω ^ 7 ● ((S ∘ H ∘ S) ⊗₁ S) ∘ Ctrl Z ∘ (H ∘ S) ⊗₁ id ≈ Ctrl Z ∘ (H ⊗₁ id) ∘ Ctrl Z
  A12 = {!!}
  -- A13
  A13 : ω ^ 7 ● (S ⊗₁ (S ∘ H ∘ S)) ∘ Ctrl Z ∘ id ⊗₁ (H ∘ S)  ≈ Ctrl Z ∘ (id ⊗₁ H) ∘ Ctrl Z
  A13 = {!!}

