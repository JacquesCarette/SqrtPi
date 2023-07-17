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

  open import Data.Product using (_,_)
  open import Level using (Level)

  open import Categories.Category.Monoidal.Braided.Properties using (braiding-coherence)
  open import Categories.Category.Monoidal.Interchange.Braided (Symmetric.braided S⊎)
  import Categories.Category.Monoidal.Interchange.Symmetric as IS
  open IS S⊎
  open import Categories.Category.Monoidal.Properties using (module Kelly's)
  open import Categories.Category.Monoidal.Utilities using (module Shorthands)
  open Shorthands M⊎ using () renaming (α⇒ to ⊕α⇒; α⇐ to ⊕α⇐)
  import Categories.Category.Monoidal.Reasoning as MonR
  open import Categories.Morphism.Reasoning C

  open import Categorical.Scalars SR
  open import Categorical.Gates SR
  
  open SqrtRig SR
  open Kit R 
  open MonR M× using (_⟩⊗⟨refl)
  open MonR M⊎ using (parallel; split₁ˡ)
    renaming (_⟩⊗⟨refl to _⟩⊕⟨refl; _⟩⊗⟨_ to _⟩⊕⟨_; refl⟩⊗⟨_ to refl⟩⊕⟨_;
    ⊗-distrib-over-∘ to ⊕-distrib-over-∘)

  private
    variable
      A B W₁ W₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Obj
      f g : A ⇒ B
      s t : Scalar
      
  ----------------------------------------------------------------
  -- Lemma lem:mat
  -- (1)
  Mat-f-right : Mat ∘ (id ⊗₁ f) ≈ (f ⊕₁ f) ∘ Mat
  Mat-f-right {f = f} = begin
    (λ⇒ ⊕₁ λ⇒ ∘ δᵣ⇒) ∘ (id ⊗₁ f)               ≈⟨ pullʳ (refl⟩∘⟨ ⟺ M⊎.⊗.identity ⟩⊗⟨refl) ⟩
    λ⇒ ⊕₁ λ⇒ ∘ δᵣ⇒ ∘ ((id ⊕₁ id) ⊗₁ f)        ≈⟨ refl⟩∘⟨ dr-commute ⟩ 
    λ⇒ ⊕₁ λ⇒ ∘ (id ⊗₁ f) ⊕₁ (id ⊗₁ f) ∘ δᵣ⇒   ≈⟨ extendʳ (parallel M×.unitorˡ-commute-from M×.unitorˡ-commute-from) ⟩
    f ⊕₁ f ∘ (λ⇒ ⊕₁ λ⇒) ∘ δᵣ⇒                  ∎

  -- (1)' that is used in the proof of (7) but inlined there
  Mat⁻¹-2f : Mat⁻¹ ∘ (f ⊕₁ f) ≈ (id ⊗₁ f) ∘ Mat⁻¹
  Mat⁻¹-2f {f = f} = begin
    Mat⁻¹ ∘ (f ⊕₁ f)                   ≈⟨ insertʳ Mat-invʳ ⟩
    ((Mat⁻¹ ∘ (f ⊕₁ f)) ∘ Mat) ∘ Mat⁻¹ ≈⟨ pullʳ (⟺ Mat-f-right) ⟩∘⟨refl ⟩
    (Mat⁻¹ ∘ Mat ∘ (id ⊗₁ f)) ∘ Mat⁻¹  ≈⟨ cancelˡ Mat-invˡ ⟩∘⟨refl ⟩
    (id ⊗₁ f) ∘ Mat⁻¹                  ∎
  
  -- (2)
  -- recall that Midswap is α⇐ ∘ id ⊗ (α⇒ ∘ σ⇒ ⊗ id ∘ α⇐) ∘ α⇒
  -- and
  {-
      laplazaIX : ∀ {A B C D} → [ (A ⊕₀ B) ⊗₀ (C ⊕₀ D) ⇒ (((A ⊗₀ C) ⊕₀ (B ⊗₀ C)) ⊕₀ (A ⊗₀ D)) ⊕₀ (B ⊗₀ D) ]⟨
        dr.from                ⇒⟨ (A ⊗₀ (C ⊕₀ D)) ⊕₀ (B ⊗₀ (C ⊕₀ D)) ⟩
        dl.from ⊕₁ dl.from     ⇒⟨ ((A ⊗₀ C) ⊕₀ (A ⊗₀ D)) ⊕₀ ((B ⊗₀ C) ⊕₀ (B ⊗₀ D)) ⟩
        ⊕α⇐                    ⇒⟨ (((A ⊗₀ C) ⊕₀ (A ⊗₀ D)) ⊕₀ (B ⊗₀ C)) ⊕₀ (B ⊗₀ D) ⟩
        ⊕α⇒ ⊕₁ C.id           ⇒⟨ ((A ⊗₀ C) ⊕₀ ((A ⊗₀ D) ⊕₀ (B ⊗₀ C))) ⊕₀ (B ⊗₀ D) ⟩
        (C.id ⊕₁ B⊕) ⊕₁ C.id  ⇒⟨ ((A ⊗₀ C) ⊕₀ ((B ⊗₀ C) ⊕₀ (A ⊗₀ D))) ⊕₀ (B ⊗₀ D) ⟩
        ⊕α⇐ ⊕₁ C.id
      ≈
        dl.from                ⇒⟨ ((A ⊕₀ B) ⊗₀ C) ⊕₀ ((A ⊕₀ B) ⊗₀ D) ⟩
        dr.from ⊕₁ dr.from     ⇒⟨ ((A ⊗₀ C) ⊕₀ (B ⊗₀ C)) ⊕₀ ((A ⊗₀ D) ⊕₀ (B ⊗₀ D))  ⟩
        ⊕α⇐
  ie
    α⇐ ∘ δᵣ⇒ ⊕₁ δᵣ⇒ ∘ δₗ⇒ ≈ α⇐ ⊕₁ id ∘ (id ⊕₁ σ⇒) ⊕₁ id ∘ α⇒ ⊕₁ id ∘ α⇐ ∘ δₗ⇒ ⊕₁ δₗ⇒ ∘ δᵣ⇒
  -}

  -- Square 1: (A+B) (C+D) ===> (A+B) C + (A+B) D

  lap-coh-1-sq1 : (σ⊗ ⊕₁ σ⊗) ∘ δᵣ⇒ ∘ σ⊗ ≈ (δₗ⇒ {X₁} {X₂} {A ⊕₀ B})
  lap-coh-1-sq1 = Equiv.sym (Equiv.sym assoc ○ ∘-resp-≈ˡ laplazaII ○ assoc) ○ elimʳ S×.commutative

  -- Square 2: C (A+B) + D (A + B) ===> (AC + BC) + (AD + BD)

  lap-coh-1-sq2-help : (σ⊗ ⊕₁ σ⊗) ∘ (δₗ⇒ {A} {B} {X₁}) ∘ σ⊗ ≈ δᵣ⇒ 
  lap-coh-1-sq2-help =
        ∘-resp-≈ʳ laplazaII ○
        sym-assoc ○
        elimˡ (Equiv.sym ⊕-distrib-over-∘ ○
               M⊎.⊗.F-resp-≈ (S×.commutative , S×.commutative) ○
               M⊎.⊗.identity )

  lap-coh-1-sq2-half : ∀ {A B X₁} → (σ⊗ ⊕₁ σ⊗) ∘ (δₗ⇒ {A} {B} {X₁}) ≈ δᵣ⇒ ∘ σ⊗
  lap-coh-1-sq2-half = begin
    (σ⊗ ⊕₁ σ⊗) ∘ δₗ⇒                ≈⟨ introʳ S×.commutative ⟩
    ((σ⊗ ⊕₁ σ⊗) ∘ δₗ⇒) ∘ (σ⊗ ∘ σ⊗)  ≈⟨ sym-assoc ○ assoc ⟩∘⟨refl ⟩
    ((σ⊗ ⊕₁ σ⊗) ∘ δₗ⇒ ∘ σ⊗) ∘ σ⊗    ≈⟨ lap-coh-1-sq2-help ⟩∘⟨refl ⟩
    δᵣ⇒ ∘ σ⊗ ∎
 
  lap-coh-1-sq2 : (δᵣ⇒ ⊕₁ δᵣ⇒) ∘ (σ⊗ ⊕₁ σ⊗) ≈ (σ⊗ ⊕₁ σ⊗) ⊕₁ (σ⊗ ⊕₁ σ⊗) ∘ (δₗ⇒ {A} {B} {X₁} ⊕₁ δₗ⇒ {A} {B} {X₂})
  lap-coh-1-sq2 = ⟺ (parallel lap-coh-1-sq2-half lap-coh-1-sq2-half)

  -- Square 3: 

  swap1≈id : σ⊗ {1C} {1C} ≈ id
  swap1≈id = begin
    σ⊗             ≈⟨ introˡ M×.unitorˡ.isoˡ ⟩
    (λ⇐ ∘ λ⇒) ∘ σ⊗ ≈⟨ assoc ⟩
    λ⇐ ∘ λ⇒ ∘ σ⊗   ≈⟨ refl⟩∘⟨ braiding-coherence S×.braided ⟩
    λ⇐ ∘ ρ⇒        ≈⟨ ∘-resp-≈ʳ (⟺ (Kelly's.coherence₃ M×)) ○ M×.unitorˡ.isoˡ ⟩
    id ∎

  lap-coh-1-sq3 : (σ⊗ {1C} {1C} ⊕₁ σ⊗ {1C} {1C}) ⊕₁ σ⊗ {1C} {1C} ⊕₁ σ⊗ {1C} {1C} ≈ id
  lap-coh-1-sq3 =
    (swap1≈id ⟩⊕⟨ swap1≈id) ⟩⊕⟨ swap1≈id ⟩⊕⟨ swap1≈id ○
    (M⊎.⊗.identity ⟩⊕⟨ M⊎.⊗.identity) ○ M⊎.⊗.identity 

  -- Square 4: (A + B) (C + D) ===> (AC + AD) + (BC + BD)
  -- α⇐ ⊕₁ id ∘ (id ⊕₁ σ⇒) ⊕₁ id ∘ α⇒ ⊕₁ id ∘ α⇐
  lap-coh-1-sq4 : Midswap {A = W₁ ⊗₀ W₂} {W₁ ⊗₀ X₂} {Y₁ ⊗₀ W₂} {Y₁ ⊗₀ X₂} ∘ (δₗ⇒ ⊕₁ δₗ⇒) ∘ δᵣ⇒ ≈ (δᵣ⇒ ⊕₁ δᵣ⇒) ∘ δₗ⇒
  lap-coh-1-sq4 = begin
    Midswap ∘ (δₗ⇒ ⊕₁ δₗ⇒) ∘ δᵣ⇒
      ≡⟨⟩
    (⊕α⇐ ∘ (id ⊕₁ (⊕α⇒ ∘ (σ⊕ ⊕₁ id) ∘ ⊕α⇐)) ∘ ⊕α⇒) ∘ (δₗ⇒ ⊕₁ δₗ⇒) ∘ δᵣ⇒
      ≈⟨ swapInner-coherent ⟩∘⟨refl ⟩
    (⊕α⇒ ∘ ((⊕α⇐ ∘ (id ⊕₁ σ⊕) ∘ ⊕α⇒) ⊕₁ id) ∘ ⊕α⇐) ∘ (δₗ⇒ ⊕₁ δₗ⇒) ∘ δᵣ⇒
      ≈⟨ (refl⟩∘⟨ (split₁ˡ ○ refl⟩∘⟨ split₁ˡ) ⟩∘⟨refl) ⟩∘⟨refl ⟩
    (⊕α⇒ ∘ ((⊕α⇐ ⊕₁ id) ∘ ((id ⊕₁ σ⊕) ⊕₁ id) ∘ (⊕α⇒ ⊕₁ id)) ∘ ⊕α⇐) ∘ (δₗ⇒ ⊕₁ δₗ⇒) ∘ δᵣ⇒
      ≈⟨ assoc ○ refl⟩∘⟨ (assoc ○ assoc ○ refl⟩∘⟨ assoc) ⟩
    ⊕α⇒ ∘ (⊕α⇐ ⊕₁ id) ∘ ((id ⊕₁ σ⊕) ⊕₁ id) ∘ (⊕α⇒ ⊕₁ id) ∘ ⊕α⇐ ∘ (δₗ⇒ ⊕₁ δₗ⇒) ∘ δᵣ⇒
      ≈⟨ refl⟩∘⟨ laplazaIX ⟩ 
    ⊕α⇒ ∘ ⊕α⇐ ∘ (δᵣ⇒ ⊕₁ δᵣ⇒) ∘ δₗ⇒
      ≈⟨ sym-assoc ⟩ 
    (⊕α⇒ ∘ ⊕α⇐) ∘ (δᵣ⇒ ⊕₁ δᵣ⇒) ∘ δₗ⇒
      ≈⟨ elimˡ S⊎.braided.associator.isoʳ  ⟩ 
    (δᵣ⇒ ⊕₁ δᵣ⇒) ∘ δₗ⇒ ∎
  
   -- Glue squares 1, 2, and 4:

  lap-coh-1-sq124 : (σ⊗ ⊕₁ σ⊗) ⊕₁ (σ⊗ ⊕₁ σ⊗) ∘ δₗ⇒ ⊕₁ δₗ⇒ ∘ δᵣ⇒ ∘ σ⊗ ≈ (δᵣ⇒ ⊕₁ δᵣ⇒) ∘ (δₗ⇒ {X₁} {X₂} {A ⊕₀ B})
  lap-coh-1-sq124 = begin
    (σ⊗ ⊕₁ σ⊗) ⊕₁ (σ⊗ ⊕₁ σ⊗) ∘ δₗ⇒ ⊕₁ δₗ⇒ ∘ δᵣ⇒ ∘ σ⊗
      ≈⟨ pullˡ (Equiv.sym lap-coh-1-sq2) ○ assoc ⟩ 
    (δᵣ⇒ ⊕₁ δᵣ⇒) ∘ (σ⊗ ⊕₁ σ⊗) ∘ δᵣ⇒ ∘ σ⊗
      ≈⟨ refl⟩∘⟨ lap-coh-1-sq1 ⟩ 
    (δᵣ⇒ ⊕₁ δᵣ⇒) ∘ δₗ⇒ ∎

  -- Glue all squares

  lap-coh-1 : (δₗ⇒ ⊕₁ δₗ⇒) ∘ δᵣ⇒ ∘ SWAP ≈ Midswap ∘ (δₗ⇒ ⊕₁ δₗ⇒) ∘ δᵣ⇒
  lap-coh-1 = Equiv.sym (elimˡ lap-coh-1-sq3) ○ lap-coh-1-sq124 ○ Equiv.sym lap-coh-1-sq4

  Mat-SWAP : Mat {2C} ∘ SWAP ≈ Midswap ∘ Mat
  Mat-SWAP = begin
    ((λ⇒ ⊕₁ λ⇒) ∘ δᵣ⇒) ∘ SWAP                                  ≈⟨ laplazaXXIII ⟩⊕⟨ laplazaXXIII ⟩∘⟨refl ⟩∘⟨refl ⟩
    (((λ⇒ ⊕₁ λ⇒) ∘ δₗ⇒ ) ⊕₁ ((λ⇒ ⊕₁ λ⇒) ∘ δₗ⇒) ∘ δᵣ⇒) ∘ SWAP  ≈⟨ M⊎.⊗.homomorphism ⟩∘⟨refl ⟩∘⟨refl ⟩
    (((λ⇒ ⊕₁ λ⇒) ⊕₁ (λ⇒ ⊕₁ λ⇒) ∘ ( δₗ⇒ ⊕₁ δₗ⇒)) ∘ δᵣ⇒) ∘ SWAP ≈⟨ assoc ○ assoc ⟩
    (λ⇒ ⊕₁ λ⇒) ⊕₁ (λ⇒ ⊕₁ λ⇒) ∘ (δₗ⇒ ⊕₁ δₗ⇒) ∘ δᵣ⇒ ∘ SWAP     ≈⟨ refl⟩∘⟨ lap-coh-1 ⟩
    (λ⇒ ⊕₁ λ⇒) ⊕₁ (λ⇒ ⊕₁ λ⇒) ∘ Midswap ∘ (δₗ⇒ ⊕₁ δₗ⇒) ∘ δᵣ⇒   ≈⟨ pullˡ (⟺ swapInner-natural) ○ assoc ⟩
    Midswap ∘ (λ⇒ ⊕₁ λ⇒) ⊕₁ (λ⇒ ⊕₁ λ⇒) ∘ (δₗ⇒ ⊕₁ δₗ⇒) ∘ δᵣ⇒   ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    Midswap ∘ ((λ⇒ ⊕₁ λ⇒) ⊕₁ (λ⇒ ⊕₁ λ⇒) ∘ (δₗ⇒ ⊕₁ δₗ⇒)) ∘ δᵣ⇒ ≈˘⟨ refl⟩∘⟨ M⊎.⊗.homomorphism ⟩∘⟨refl ⟩
    Midswap ∘ (((λ⇒ ⊕₁ λ⇒) ∘ δₗ⇒) ⊕₁ ((λ⇒ ⊕₁ λ⇒) ∘ δₗ⇒)) ∘ δᵣ⇒ ≈˘⟨ refl⟩∘⟨ laplazaXXIII ⟩⊕⟨ laplazaXXIII ⟩∘⟨refl ⟩
    Midswap ∘ λ⇒ ⊕₁ λ⇒ ∘ δᵣ⇒ ∎

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
  Mat-f-left {f = f} = begin
    Mat ∘ (f ⊗₁ id)                    ≈⟨ insertʳ S×.commutative ⟩∘⟨refl ⟩
    ((Mat ∘ SWAP) ∘ SWAP) ∘ (f ⊗₁ id)  ≈⟨ pullʳ (S×.braiding.⇒.commute (f , id)) ⟩
    (Mat ∘ SWAP) ∘ (id ⊗₁ f) ∘ SWAP    ≈⟨ Mat-SWAP ⟩∘⟨refl ⟩
    (Midswap ∘ Mat) ∘ (id ⊗₁ f) ∘ SWAP ≈⟨ pullʳ (pullˡ Mat-f-right) ⟩
    Midswap ∘ ((f ⊕₁ f) ∘ Mat) ∘ SWAP  ≈⟨ refl⟩∘⟨ pullʳ Mat-SWAP ⟩
    Midswap ∘ (f ⊕₁ f) ∘ Midswap ∘ Mat ∎

  -- (5)
  SWAP-CP-SWAP : SWAP ∘ Ctrl (P s) ∘ SWAP ≈ Ctrl (P s)
  SWAP-CP-SWAP {s = s} = begin
    SWAP ∘ (Mat⁻¹ ∘ (id ⊕₁ P s) ∘ Mat) ∘ SWAP                       ≈⟨ refl⟩∘⟨ assoc ○ sym-assoc ○ refl⟩∘⟨ assoc ⟩
    (SWAP ∘ Mat⁻¹) ∘ (id ⊕₁ P s) ∘ (Mat ∘ SWAP)                     ≈⟨ SWAP-Mat⁻¹ ⟩∘⟨ Equiv.refl ⟩∘⟨ Mat-SWAP ⟩
    (Mat⁻¹ ∘ Midswap) ∘ (id ⊕₁ P s) ∘ (Midswap ∘ Mat)               ≈˘⟨ refl⟩∘⟨ M⊎.⊗.identity ⟩⊕⟨refl ⟩∘⟨refl ⟩
    (Mat⁻¹ ∘ Midswap) ∘ ((id ⊕₁ id) ⊕₁ (id ⊕₁ s)) ∘ (Midswap ∘ Mat) ≈⟨ refl⟩∘⟨ pullˡ (⟺ swapInner-natural) ⟩
    (Mat⁻¹ ∘ Midswap) ∘ (Midswap ∘ ((id ⊕₁ id) ⊕₁ (id ⊕₁ s))) ∘ Mat ≈⟨ pullˡ (cancelInner swapInner-commutative) ⟩
    (Mat⁻¹ ∘ (id ⊕₁ id) ⊕₁ (id ⊕₁ s)) ∘ Mat                         ≈⟨ pushˡ (refl⟩∘⟨ M⊎.⊗.identity ⟩⊕⟨refl) ⟩
    Ctrl (P s)                                                       ∎

  -- (5)' convenient reformulation of above
  SWAP-CP : SWAP ∘ Ctrl (P s) ≈ Ctrl (P s) ∘ SWAP
  SWAP-CP {s = s} = begin
    SWAP ∘ Ctrl (P s)                 ≈⟨ insertʳ S×.commutative ○ assoc ⟩∘⟨refl ⟩
    (SWAP ∘ Ctrl (P s) ∘ SWAP) ∘ SWAP ≈⟨ SWAP-CP-SWAP ⟩∘⟨refl ⟩
    Ctrl (P s) ∘ SWAP                 ∎
  
  -- (10)
  Ctrl-merge : {g h : Endo A} → Ctrl g ∘ Ctrl h ≈ Ctrl (g ∘ h)
  Ctrl-merge {g = g} {h} = begin
    (Mat⁻¹ ∘ id ⊕₁ g ∘ Mat) ∘ Mat⁻¹ ∘ id ⊕₁ h ∘ Mat   ≈⟨ sym-assoc ⟩∘⟨refl ⟩
    ((Mat⁻¹ ∘ id ⊕₁ g) ∘ Mat) ∘ Mat⁻¹ ∘ id ⊕₁ h ∘ Mat ≈⟨ cancelInner Mat-invʳ ⟩
    (Mat⁻¹ ∘ id ⊕₁ g) ∘ id ⊕₁ h ∘ Mat                 ≈⟨ center (⟺ M⊎.⊗.homomorphism) ⟩
    Mat⁻¹ ∘ (id ∘ id) ⊕₁ (g ∘ h) ∘ Mat                ≈⟨ refl⟩∘⟨ identity² ⟩⊕⟨refl ⟩∘⟨refl ⟩
    Mat⁻¹ ∘ id ⊕₁ (g ∘ h) ∘ Mat                       ∎
  
  -- (6)
  Ctrl-comm : f ∘ g ≈ g ∘ f → Ctrl f ∘ Ctrl g ≈ Ctrl g ∘ Ctrl f
  Ctrl-comm {f = f} {g} fg≡gf = begin
    Ctrl f ∘ Ctrl g ≈⟨ Ctrl-merge ⟩
    Ctrl (f ∘ g)    ≈⟨ refl⟩∘⟨ refl⟩⊕⟨ fg≡gf ⟩∘⟨refl ⟩ -- expand defn to see
    Ctrl (g ∘ f)    ≈˘⟨ Ctrl-merge ⟩
    Ctrl g ∘ Ctrl f ∎

  CP-comm : s ∘ t ≈ t ∘ s → Ctrl (P s) ∘ Ctrl (P t) ≈ Ctrl (P t) ∘ Ctrl (P s)
  CP-comm st≡ts = Ctrl-comm (P-comm st≡ts)

  -- (7)
  CP-P-right : s ∘ t ≈ t ∘ s → Ctrl (P s) ∘ (id ⊗₁ P t) ≈ (id ⊗₁ P t) ∘ Ctrl (P s)
  CP-P-right {s = s} {t} st≡ts = begin
    (Mat⁻¹ ∘ (id ⊕₁ P s) ∘ Mat) ∘ (id ⊗₁ P t)  ≈⟨ pullʳ (pullʳ Mat-f-right) ⟩
    Mat⁻¹ ∘ (id ⊕₁ P s) ∘ (P t ⊕₁ P t) ∘ Mat   ≈⟨ refl⟩∘⟨ pullˡ (⟺ M⊎.⊗.homomorphism) ⟩
    Mat⁻¹ ∘ ((id ∘ P t) ⊕₁ (P s ∘ P t)) ∘ Mat  ≈⟨ refl⟩∘⟨ id-comm-sym ⟩⊕⟨ P-comm st≡ts ⟩∘⟨refl ⟩
    Mat⁻¹ ∘ ((P t ∘ id) ⊕₁ (P t ∘ P s)) ∘ Mat  ≈⟨ refl⟩∘⟨ M⊎.⊗.homomorphism ⟩∘⟨refl ⟩
    Mat⁻¹ ∘ ((P t ⊕₁ P t) ∘ (id ⊕₁ P s)) ∘ Mat ≈⟨ assoc²'' ⟩
    (Mat⁻¹ ∘ (P t ⊕₁ P t)) ∘ (id ⊕₁ P s) ∘ Mat ≈⟨ Mat⁻¹-2f ⟩∘⟨refl ○ assoc ⟩
    (id ⊗₁ P t) ∘ Mat⁻¹ ∘ (id ⊕₁ P s) ∘ Mat    ∎
  
  -- (8)
  -- convenient general lemma
  parallel-intro : {A B : Obj} {f : A ⇒ B} {g : B ⇒ A} → f ∘ g ≈ id → f ⊕₁ f ∘ g ⊕₁ g ≈ id
  parallel-intro {f = f} {g} fg≈id = begin
    f ⊕₁ f ∘ g ⊕₁ g    ≈˘⟨ M⊎.⊗.homomorphism ⟩
    (f ∘ g) ⊕₁ (f ∘ g) ≈⟨ fg≈id ⟩⊕⟨ fg≈id ⟩
    id ⊕₁ id           ≈⟨ M⊎.⊗.identity ⟩
    id              ∎
    
  lapI+II : δᵣ⇒ ∘ (X ⊗₁ id {A}) ≈ σ⊕ ∘ δᵣ⇒
  lapI+II = begin
    δᵣ⇒ ∘ (X ⊗₁ id)                             ≈⟨ introˡ (parallel-intro S×.commutative)○ pullʳ sym-assoc ⟩
    (σ⊗ ⊕₁ σ⊗) ∘ ((σ⊗ ⊕₁ σ⊗) ∘ δᵣ⇒) ∘ (X ⊗₁ id) ≈⟨ refl⟩∘⟨ (⟺ laplazaII) ⟩∘⟨refl ⟩
    (σ⊗ ⊕₁ σ⊗) ∘ (δₗ⇒ ∘ σ⊗) ∘ (X ⊗₁ id)         ≈⟨ refl⟩∘⟨ pullʳ (S×.braiding.⇒.commute (X , id)) ⟩
    (σ⊗ ⊕₁ σ⊗) ∘ δₗ⇒ ∘ (id ⊗₁ X) ∘ σ⊗           ≈⟨ refl⟩∘⟨ pullˡ (⟺ laplazaI) ⟩
    (σ⊗ ⊕₁ σ⊗) ∘ (σ⊕ ∘ δₗ⇒) ∘ σ⊗                ≈⟨ refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ laplazaII)) ⟩
    (σ⊗ ⊕₁ σ⊗) ∘ σ⊕ ∘ (σ⊗ ⊕₁ σ⊗) ∘ δᵣ⇒          ≈⟨ pullˡ (⟺ (S⊎.braiding.⇒.commute _)) ⟩
    (σ⊕ ∘ (σ⊗ ⊕₁ σ⊗)) ∘ (σ⊗ ⊕₁ σ⊗) ∘ δᵣ⇒        ≈⟨ cancelInner (parallel-intro S×.commutative) ⟩
    σ⊕ ∘ δᵣ⇒ ∎
    
  Mat-X-left : {A : Obj} → Mat ∘ (X ⊗₁ id {A}) ≈ σ⊕ ∘ Mat
  Mat-X-left = begin
    ((λ⇒ ⊕₁ λ⇒) ∘ δᵣ⇒) ∘ (X ⊗₁ id) ≈⟨ pullʳ lapI+II ⟩
    (λ⇒ ⊕₁ λ⇒) ∘ σ⊕ ∘ δᵣ⇒          ≈⟨ pullˡ (⟺ (S⊎.braiding.⇒.commute (λ⇒ , λ⇒))) ⟩
    (σ⊕ ∘ (λ⇒ ⊕₁ λ⇒)) ∘ δᵣ⇒        ≈⟨ assoc ⟩ 
    σ⊕ ∘ (λ⇒ ⊕₁ λ⇒) ∘ δᵣ⇒          ∎

  -- cor of above
  Mat⁻¹σ : {A : Obj} → Mat⁻¹ ∘ σ⊕ ≈ (X ⊗₁ id {A}) ∘ Mat⁻¹
  Mat⁻¹σ = begin
    Mat⁻¹ ∘ σ⊕                          ≈⟨ insertʳ Mat-invʳ ⟩
    ((Mat⁻¹ ∘ σ⊕) ∘ Mat) ∘ Mat⁻¹        ≈⟨ pullʳ (⟺ Mat-X-left) ⟩∘⟨refl ⟩
    (Mat⁻¹ ∘ (Mat ∘ (X ⊗₁ id))) ∘ Mat⁻¹ ≈⟨ cancelˡ Mat-invˡ ⟩∘⟨refl ⟩
    (X ⊗₁ id) ∘ Mat⁻¹                   ∎
  
  -- (9) (for some reason, Agda won't infer which object Mat is over)
  Mat-P-left : Mat {2C} ∘ (P s ⊗₁ id) ≈ (id ⊕₁ (s ● id)) ∘ Mat
  Mat-P-left {s = s} = begin
    Mat ∘ (P s ⊗₁ id)                                     ≈⟨ Mat-f-left ⟩ -- and defn of P s
    Midswap ∘ ((id ⊕₁ s) ⊕₁ (id ⊕₁ s)) ∘ Midswap ∘ Mat    ≈⟨ refl⟩∘⟨ pullˡ (⟺ swapInner-natural) ⟩
    Midswap ∘ (Midswap ∘ ((id ⊕₁ id) ⊕₁ (s ⊕₁ s))) ∘ Mat  ≈⟨ assoc²'' ○ elimˡ swapInner-commutative ⟩
    (id ⊕₁ id) ⊕₁ (s ⊕₁ s) ∘ Mat                          ≈⟨ M⊎.⊗.identity ⟩⊕⟨ ⊕-to-●id ⟩∘⟨refl ⟩
    (id ⊕₁ (s ● id)) ∘ Mat                              ∎

  -- immediate cor. of (9) that's used as if it were (9) in the proofs
  P-Mat⁻¹ : (P s ⊗₁ id) ∘ Mat⁻¹ {2C} ≈ Mat⁻¹ ∘ (id ⊕₁ s ● id)
  P-Mat⁻¹ {s = s} = begin
    (P s ⊗₁ id) ∘ Mat⁻¹ {2C}               ≈⟨ insertˡ Mat-invˡ ⟩
    Mat⁻¹ ∘ Mat ∘ (P s ⊗₁ id) ∘ Mat⁻¹      ≈⟨ refl⟩∘⟨ pullˡ Mat-P-left ⟩
    Mat⁻¹ ∘ ((id ⊕₁ s ● id) ∘ Mat) ∘ Mat⁻¹ ≈⟨ refl⟩∘⟨ cancelʳ Mat-invʳ ⟩
    Mat⁻¹ ∘ (id ⊕₁ s ● id)                 ∎
  
  ----------------------------------------------------------------
  -- Lemma lem:had
  HXH≡Z : H ∘ X ∘ H ≈ Z
  HXH≡Z = begin
    ω ● (X ∘ S ∘ V ∘ S ∘ X) ∘ X ∘ ω ● (X ∘ S ∘ V ∘ S ∘ X)       ≈⟨ pullˡ ●-assocʳ  ⟩
    (ω ● ((X ∘ S ∘ V ∘ S ∘ X) ∘ X)) ∘ (ω ● (X ∘ S ∘ V ∘ S ∘ X)) ≈⟨ merge-scalars ⟩
    (ω ∘ ω) ● (((X ∘ S ∘ V ∘ S ∘ X) ∘ X) ∘ X ∘ S ∘ V ∘ S ∘ X)   ≈⟨ ●-congʳ (pullʳ (cancelˡ X²≡id)) ⟩
    i ● ((X ∘ S ∘ V ∘ S ∘ X) ∘ S ∘ V ∘ S ∘ X)                    ≈⟨ ●-congʳ (sym-assoc ○ (sym-assoc ⟩∘⟨refl ○ sym-assoc ⟩∘⟨refl ○ assoc ○ assoc ⟩∘⟨ assoc) ⟩∘⟨refl) ⟩
    i ● (((X ∘ S ∘ V) ∘ (S ∘ X ∘ S)) ∘ V ∘ S ∘ X)                ≈⟨ ●-congʳ ((refl⟩∘⟨ PXP i) ⟩∘⟨refl) ⟩
    i ● (((X ∘ S ∘ V) ∘ (i ● X)) ∘ V ∘ S ∘ X)                    ≈⟨ ●-congʳ assoc ○ extract-scalar3 ⟩
    (i ∘ i) ● ((X ∘ S ∘ V) ∘ X ∘ V ∘ S ∘ X)                      ≈⟨ ●-cong i²≡-𝟙 (refl⟩∘⟨ pullˡ XV-comm) ⟩
    -𝟙 ● ((X ∘ S ∘ V) ∘ (V ∘ X) ∘ S ∘ X)                         ≈⟨ ●-congʳ (sym-assoc ○ (sym-assoc ⟩∘⟨refl ○ center E2) ⟩∘⟨refl) ⟩
    -𝟙 ● (((X ∘ S) ∘ X ∘ X) ∘ S ∘ X)                             ≈⟨ ●-congʳ (elimʳ X²≡id ⟩∘⟨refl)  ⟩
    -𝟙 ● ((X ∘ S) ∘ S ∘ X)                                       ≈⟨ ●-congʳ (center S²≡Z) ⟩
    -𝟙 ● (X ∘ Z ∘ X)                                             ≈⟨ ●-congʳ (pullˡ (XPs -𝟙²≡𝟙)) ⟩
    -𝟙 ● (-𝟙 ● (Z ∘ X) ∘ X)                                      ≈⟨ ●-congʳ ●-assocʳ ○ push-scalar-left ⟩
    (-𝟙 ∘ -𝟙) ● ((Z ∘ X) ∘ X)                                    ≈⟨ ●-cong -𝟙²≡𝟙 (cancelʳ X²≡id) ⟩
    𝟙 ● P -𝟙                                                     ≈⟨ 𝟙●f≈f _ ⟩
    Z                                                            ∎

  HZH≡X : H ∘ Z ∘ H ≈ X
  HZH≡X = begin
    ω ● (X ∘ S ∘ V ∘ S ∘ X) ∘ Z ∘ ω ● (X ∘ S ∘ V ∘ S ∘ X)          ≈⟨ pullˡ ●-assocʳ ⟩
    (ω ● ((X ∘ S ∘ V ∘ S ∘ X) ∘ Z)) ∘ (ω ● (X ∘ S ∘ V ∘ S ∘ X))    ≈⟨ merge-scalars ⟩
    (ω ∘ ω) ● (((X ∘ S ∘ V ∘ S ∘ X) ∘ Z) ∘ X ∘ S ∘ V ∘ S ∘ X)      ≈⟨ ●-congʳ (pull-last (pull-last (XPs -𝟙²≡𝟙)) ⟩∘⟨refl) ⟩
    i ● ((X ∘ S ∘ V ∘ S ∘ -𝟙 ● (Z ∘ X)) ∘ X ∘ S ∘ V ∘ S ∘ X)       ≈⟨ ●-congʳ ( (⟺ assoc² ○ sym-assoc) ⟩∘⟨refl) ⟩
    i ● (((((X ∘ S) ∘ V) ∘ S) ∘ -𝟙 ● (Z ∘ X)) ∘ X ∘ S ∘ V ∘ S ∘ X) ≈⟨ ●-congʳ assoc ○ extract-scalar3 ⟩
    (i ∘ -𝟙) ● ((((X ∘ S) ∘ V) ∘ S) ∘ (Z ∘ X) ∘ X ∘ S ∘ V ∘ S ∘ X)  ≈⟨ ●-cong (⟺ -i≡i◎-𝟙) (refl⟩∘⟨ cancelInner X²≡id) ⟩
    -i ● ((((X ∘ S) ∘ V) ∘ S) ∘ Z ∘ S ∘ V ∘ S ∘ X)                 ≈⟨ ●-congʳ (center (P-comm (^-comm 2 4))) ⟩
    -i ● (((X ∘ S) ∘ V) ∘ (Z ∘ S) ∘ S ∘ V ∘ S ∘ X)                 ≈⟨ ●-congʳ (refl⟩∘⟨ center S²≡Z ) ⟩
    -i ● (((X ∘ S) ∘ V) ∘ Z ∘ Z ∘ V ∘ S ∘ X)                       ≈⟨ ●-congʳ (refl⟩∘⟨ cancelˡ Z²≡id ) ⟩
    -i ● (((X ∘ S) ∘ V) ∘ V ∘ S ∘ X)                               ≈⟨ ●-congʳ (center E2) ⟩
    -i ● ((X ∘ S) ∘ X ∘ S ∘ X)                                     ≈⟨ ●-congʳ (refl⟩∘⟨ sym-assoc ○ assoc ○ refl⟩∘⟨ (sym-assoc ○ PXP i ⟩∘⟨refl)) ⟩
    -i ● (X ∘ i ● X ∘ X)                                           ≈⟨ extract-scalar3 ⟩
    (-i ∘ i) ● (X ∘ X ∘ X)                                         ≈⟨ ●-cong -i◎i≡𝟙 (cancelˡ X²≡id) ⟩
    𝟙 ● X                                                          ≈⟨ 𝟙●f≈f X ⟩
    X                                                              ∎

  -----------------------------------------------------------------
  -- useful corrolaries
  HSSH≡X : H ∘ S ∘ S ∘ H ≈ X
  HSSH≡X = begin
    H ∘ S ∘ S ∘ H ≈⟨ pull-center S²≡Z ⟩
    H ∘ Z ∘ H     ≈⟨ HZH≡X ⟩
    X             ∎
