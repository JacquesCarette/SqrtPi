{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
-- add --safe when there are no more holes

open import Categories.Category -- we need it all
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.RigCategory

open import Categorical.SqrtRig

-- Everything is over a SqrtRig
module Categorical.Gates {o ℓ e} {C : Category o ℓ e}
  {M⊎ M× : Monoidal C} {S⊎ : Symmetric M⊎}
  {S× : Symmetric M×} {R : RigCategory C S⊎ S×} (SR : SqrtRig R) where

  open import Data.Product using (_,_)
  open import Level using (Level)

  -- open import Categories.Functor.Bifunctor using (module Bifunctor)
  open import Categories.Category.Monoidal.Interchange.Braided (Symmetric.braided S⊎) using (module swapInner)
  import Categories.Category.Monoidal.Reasoning as MonR
  import Categories.Morphism.Reasoning as MR
  
  private
    module S⊎ = Symmetric S⊎

  open import Categorical.Scalars SR

  open Category C -- all of it
  open HomReasoning
  open SqrtRig SR
  open Kit R
  open MR C
  -- open MonR M× using (_⟩⊗⟨refl)
  open MonR M⊎ using (serialize₂₁) renaming (_⟩⊗⟨refl to _⟩⊕⟨refl; _⟩⊗⟨_ to _⟩⊕⟨_)
  
  X : 2×2
  X = σ⊕

  P : Scalar → 2×2
  P s = id ⊕₁ s

  -- Note: S was already defined in SqrtRig
  Z T H : 2×2
  Z = P -𝟙
  T = P ω
  H = ω ● (X ∘ S ∘ V ∘ S ∘ X)

  -- note that this isn't quite what's in the paper, but it is equivalent
  Midswap : {A B C D : Obj} → (A ⊕₀ B) ⊕₀ (C ⊕₀ D) ⇒ (A ⊕₀ C) ⊕₀ (B ⊕₀ D)
  Midswap = swapInner.from

  Mat : {A : Obj} → 2C ⊗₀ A ⇒ A ⊕₀ A
  Mat = (λ⇒ ⊕₁ λ⇒) ∘ δᵣ⇒

  Mat⁻¹ : {A : Obj} → A ⊕₀ A ⇒ 2C ⊗₀ A
  Mat⁻¹ = δᵣ⇐ ∘ λ⇐ ⊕₁ λ⇐
  
  Ctrl : {A : Obj} (m : Endo {A}) → 2C ⊗₀ A ⇒ 2C ⊗₀ A
  Ctrl m = Mat⁻¹ ∘ (id ⊕₁ m) ∘ Mat

  nCtrl : {A : Obj} (m : Endo {A}) → 2C ⊗₀ A ⇒ 2C ⊗₀ A
  nCtrl m = Mat⁻¹ ∘ (m ⊕₁ id) ∘ Mat

  SWAP CX CZ : 2C ⊗₀ 2C ⇒ 2C ⊗₀ 2C
  SWAP = σ⊗
  CX = Ctrl X
  CZ = Ctrl Z

  CCX :  2C ⊗₀ 2C ⊗₀ 2C ⇒ 2C ⊗₀ 2C ⊗₀ 2C
  CCX = Ctrl CX

  ------------------------------------------------------------------------
  -- Properties of Gates (split?)

  -- Lemma lem:gates
  -- (ii)
  X²≡id : X ^ 2 ≈ id
  X²≡id = S⊎.commutative

  -- (iii)
  P² : (s : Scalar) → (P s) ^ 2 ≈ P (s ^ 2)
  P² s = begin
    (id ⊕₁ s) ∘ (id ⊕₁ s) ≈˘⟨ S⊎.⊗.homomorphism ⟩
    (id ∘ id) ⊕₁ (s ∘ s)  ≈⟨ identity² ⟩⊕⟨refl ⟩
    id ⊕₁ s ^ 2           ∎

  -- (iv) Split into two parts. Show P is invertible instead of assuming
  P-invˡ : (s : Scalar) → P (inv s) ∘ P s ≈ id
  P-invˡ s = begin
    (id ⊕₁ inv s) ∘ (id ⊕₁ s) ≈˘⟨ S⊎.⊗.homomorphism ⟩
    (id ∘ id) ⊕₁ (inv s ∘ s)  ≈⟨ identity² ⟩⊕⟨ invˡ s ⟩
    id ⊕₁ id                  ≈⟨ S⊎.⊗.identity ⟩
    id                         ∎
  P-invʳ : (s : Scalar) → P s ∘ P (inv s) ≈ id
  P-invʳ s = begin
    (id ⊕₁ s) ∘ (id ⊕₁ inv s) ≈˘⟨ S⊎.⊗.homomorphism ⟩
    (id ∘ id) ⊕₁ (s ∘ inv s)  ≈⟨ identity² ⟩⊕⟨ invʳ s ⟩
    id ⊕₁ id                  ≈⟨ S⊎.⊗.identity ⟩
    id                         ∎

  -- (v)
  {- no needed
  P-comm : (s t : Scalar) → P s ∘ P t ≈ P t ∘ P s
  P-comm s t = {!!}
  -}
  -- (vi)
  PXP : (s : Scalar) → P s ∘ X ∘ P s ≈ s ● X
  PXP s = begin
    (id ⊕₁ s) ∘ X ∘ (id ⊕₁ s)  ≈⟨ refl⟩∘⟨ S⊎.braiding.⇒.commute (id , s) ⟩
    (id ⊕₁ s) ∘ (s ⊕₁ id) ∘ X  ≈⟨ pullˡ (Equiv.sym serialize₂₁)  ⟩
    (s ⊕₁ s) ∘ X               ≈˘⟨ identityʳ ⟩⊕⟨ identityʳ ⟩∘⟨refl ⟩
    ((s ∘ id) ⊕₁ (s ∘ id)) ∘ X ≈˘⟨ scalar-●≈∘ ⟩⊕⟨ scalar-●≈∘ ⟩∘⟨refl ⟩
    (s ● id ⊕₁ s ● id) ∘ X     ≈˘⟨ ●-distrib-⊕ ⟩∘⟨refl ⟩
    (s ● (id ⊕₁ id)) ∘ X       ≈˘⟨ ●-assocˡ ⟩
    s ● ((id ⊕₁ id) ∘ X)       ≈⟨ ●-congʳ (elimˡ S⊎.⊗.identity) ⟩
    s ● X                      ∎

  -- (vii)
  XV-comm : X ∘ V ≈ V ∘ X
  XV-comm = begin
    X ∘ V   ≈˘⟨ E2 ⟩∘⟨refl ⟩
    (V ∘ V) ∘ V ≈⟨ assoc ⟩
    V ∘ (V ∘ V) ≈⟨ refl⟩∘⟨ E2 ⟩
    V ∘ X       ∎

  -- lemma that makes (viii) and (ix) the same
  CA∘CB≡id : {A B : 2×2} → A ≈ B → Ctrl A ∘ Ctrl B ≈ id
  CA∘CB≡id {A = A} {B} A≈B = begin
    (Mat⁻¹ ∘ (id ⊕₁ A) ∘ Mat) ∘ Mat⁻¹ ∘ (id ⊕₁ B) ∘ Mat ≈⟨ {!!} ⟩
    (Mat⁻¹ ∘ (id ⊕₁ A)) ∘ (id ⊕₁ B) ∘ Mat               ≈⟨ {!!} ⟩
    Mat⁻¹ ∘ (id ∘ id) ⊕₁ (A ∘ B) ∘ Mat                  ≈⟨ {!!} ⟩
    Mat⁻¹ ∘ id ⊕₁ id ∘ Mat                              ≈⟨ {!!} ⟩
    Mat⁻¹ ∘ Mat                                         ≈⟨ {!!} ⟩
    id                                                   ∎
    
  -- (viii)
  CX²≡id : CX ^ 2 ≈ id
  CX²≡id = {!begin
    (Mat⁻¹ ∘ (id ⊕₁ m) ∘ Mat) ∘ Mat⁻¹ ∘ (id ⊕₁ m) ∘ Mat!}

  -- (ix)
  CZ²≡id : CZ ^ 2 ≈ id
  CZ²≡id = {!!}

  -- (x)
  CCX²≡id : CCX ^ 2 ≈ id
  CCX²≡id = {!!}

  -- (xi)
  XPs : (s : Scalar) → X ∘ P s ≈ s ● P (inv s) ∘ X
  XPs s = {!!}

  -----------------------------------------------------------------------------
  -- Corrolaries that are used in the proofs "inline"
  cong-P : {s t : Scalar} → (s ≈ t) → P s ≈ P t
  cong-P = MonR.⊗-resp-≈ʳ M⊎
  
  S²≡Z : S ∘ S ≈ Z
  S²≡Z = begin
    P i ∘ P i ≈⟨ P² i ⟩
    P (i ^ 2) ≈⟨ cong-P i²≡-𝟙 ⟩
    P -𝟙      ∎
