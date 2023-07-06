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

  open import Categories.Category.Monoidal.Interchange.Braided (Symmetric.braided S⊎)
  open import Categories.Category.Monoidal.Interchange.Symmetric S⊎
  import Categories.Category.Monoidal.Reasoning as MonR
  open import Categories.Morphism.Reasoning C

  open import Categorical.Scalars SR
  open import Categorical.Gates SR
  
  open Category C -- all of it
  open HomReasoning
  open SqrtRig SR
  open Kit R
  open MonR M× using (_⟩⊗⟨refl)
  open MonR M⊎ using (parallel)
    renaming (_⟩⊗⟨refl to _⟩⊕⟨refl; _⟩⊗⟨_ to _⟩⊕⟨_; refl⟩⊗⟨_ to refl⟩⊕⟨_)

  private
    variable
      A B : Obj
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
  Mat-SWAP : Mat {2C} ∘ SWAP ≈ Midswap ∘ Mat
  Mat-SWAP = begin
    ((λ⇒ ⊕₁ λ⇒) ∘ δᵣ⇒) ∘ SWAP                                  ≈⟨ laplazaXXIII ⟩⊕⟨ laplazaXXIII ⟩∘⟨refl ⟩∘⟨refl ⟩
    (((λ⇒ ⊕₁ λ⇒) ∘ δₗ⇒ ) ⊕₁ ((λ⇒ ⊕₁ λ⇒) ∘ δₗ⇒) ∘ δᵣ⇒) ∘ SWAP  ≈⟨ M⊎.⊗.homomorphism ⟩∘⟨refl ⟩∘⟨refl ⟩
    (((λ⇒ ⊕₁ λ⇒) ⊕₁ (λ⇒ ⊕₁ λ⇒) ∘ ( δₗ⇒ ⊕₁ δₗ⇒)) ∘ δᵣ⇒) ∘ SWAP ≈⟨ {!!} ⟩
    (λ⇒ ⊕₁ λ⇒) ⊕₁ (λ⇒ ⊕₁ λ⇒) ∘ ( δₗ⇒ ⊕₁ δₗ⇒) ∘ δᵣ⇒ ∘ SWAP     ≈⟨ {!!} ⟩
    (λ⇒ ⊕₁ λ⇒) ⊕₁ (λ⇒ ⊕₁ λ⇒) ∘ Midswap ∘ (δₗ⇒ ⊕₁ δₗ⇒) ∘ δᵣ⇒   ≈⟨ {!!} ⟩
    Midswap ∘ (λ⇒ ⊕₁ λ⇒) ⊕₁ (λ⇒ ⊕₁ λ⇒) ∘ (δₗ⇒ ⊕₁ δₗ⇒) ∘ δᵣ⇒   ≈⟨ {!!} ⟩ -- reassoc
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

  -- (10)
  Ctrl-merge : {g h : Endo {A}} → Ctrl g ∘ Ctrl h ≈ Ctrl (g ∘ h)
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
  CP-comm {s = s} {t} st≡ts = Ctrl-comm (P-comm s t st≡ts)

  -- (7)
  CP-P-right : s ∘ t ≈ t ∘ s → Ctrl (P s) ∘ (id ⊗₁ P t) ≈ (id ⊗₁ P t) ∘ Ctrl (P s)
  CP-P-right {s = s} {t} st≡ts = begin
    (Mat⁻¹ ∘ (id ⊕₁ P s) ∘ Mat) ∘ (id ⊗₁ P t)  ≈⟨ pullʳ (pullʳ Mat-f-right) ⟩
    Mat⁻¹ ∘ (id ⊕₁ P s) ∘ (P t ⊕₁ P t) ∘ Mat   ≈⟨ refl⟩∘⟨ pullˡ (⟺ M⊎.⊗.homomorphism) ⟩
    Mat⁻¹ ∘ ((id ∘ P t) ⊕₁ (P s ∘ P t)) ∘ Mat  ≈⟨ refl⟩∘⟨ id-comm-sym ⟩⊕⟨ P-comm s t st≡ts ⟩∘⟨refl ⟩
    Mat⁻¹ ∘ ((P t ∘ id) ⊕₁ (P t ∘ P s)) ∘ Mat  ≈⟨ refl⟩∘⟨ M⊎.⊗.homomorphism ⟩∘⟨refl ⟩
    Mat⁻¹ ∘ ((P t ⊕₁ P t) ∘ (id ⊕₁ P s)) ∘ Mat ≈⟨ assoc²'' ⟩
    (Mat⁻¹ ∘ (P t ⊕₁ P t)) ∘ (id ⊕₁ P s) ∘ Mat ≈⟨ Mat⁻¹-2f ⟩∘⟨refl ○ assoc ⟩
    (id ⊗₁ P t) ∘ Mat⁻¹ ∘ (id ⊕₁ P s) ∘ Mat    ∎
  
  -- (8)
  Mat-X-left : Mat ∘ (X ⊗₁ id {2C}) ≈ σ⊕ ∘ Mat
  Mat-X-left = {!!}
  
  -- (9) (for some reason, Agda won't infer which object Mat is over)
  Mat-P-left : Mat {2C} ∘ (P s ⊗₁ id) ≈ (id ⊕₁ (s ● id)) ∘ Mat
  Mat-P-left {s = s} = begin
    Mat ∘ (P s ⊗₁ id)                                     ≈⟨ Mat-f-left ⟩ -- and defn of P s
    Midswap ∘ ((id ⊕₁ s) ⊕₁ (id ⊕₁ s)) ∘ Midswap ∘ Mat    ≈⟨ refl⟩∘⟨ pullˡ (⟺ swapInner-natural) ⟩
    Midswap ∘ (Midswap ∘ ((id ⊕₁ id) ⊕₁ (s ⊕₁ s))) ∘ Mat  ≈⟨ assoc²'' ○ elimˡ swapInner-commutative ⟩
    (id ⊕₁ id) ⊕₁ (s ⊕₁ s) ∘ Mat                          ≈⟨ M⊎.⊗.identity ⟩⊕⟨ ⊕-to-●id ⟩∘⟨refl ⟩
    (id ⊕₁ (s ● id)) ∘ Mat                              ∎

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
