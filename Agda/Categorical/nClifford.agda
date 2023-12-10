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

  open import Categorical.CtrlH SR
  open import Categorical.2Clifford SR
  -- open import Categories.Category.Monoidal.Interchange.Braided (Symmetric.braided S⊎) using (module swapInner)
  open import Categories.Morphism.Reasoning C
  import Categories.Category.Monoidal.Reasoning as MonR
  open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
  
  open import Categorical.Scalars SR
  open import Categorical.Gates SR
  open import Categorical.MatProp SR
  
  open SqrtRig SR

  private
    variable
      A B : Obj
      f g : A ⇒ B
      s t : Scalar

  postulate
    P1 : α⇐ ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ≈
         SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ α⇐ ∘ id ⊗₁ Ctrl X ∘ α⇒
  ----------------------------------------------------------------
  Zz zZ : C [ (2C ⊗₀ 2C) ⊗₀ 2C , (2C ⊗₀ 2C) ⊗₀ 2C ]
  Zz = Ctrl Z ⊗₁ id ∘ α⇐ ∘ id ⊗₁ Ctrl Z ∘ α⇒
  zZ = α⇐ ∘ id ⊗₁ Ctrl Z ∘ α⇒ ∘ Ctrl Z ⊗₁ id

  helper : id ≈ id ∘ id ∘ id
  helper = begin
    id ≈⟨ ⟺  identity² ⟩
    id ∘ id ≈⟨ refl⟩∘⟨ ⟺  identity² ⟩
    id ∘ id ∘ id ∎

  helper2l : ∀ {A B C D} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} →
                id ⊗₁ (f ∘ g ∘ h) ≈ id ⊗₁ f ∘ id ⊗₁ g ∘ id ⊗₁ h
  helper2l {f = f} {g} {h} = begin
    id ⊗₁ (f ∘ g ∘ h) ≈⟨ helper ⟩⊗⟨refl ○ ⊗-distrib-over-∘ ○ (refl⟩∘⟨ ⊗-distrib-over-∘) ⟩
    id ⊗₁ f ∘ id ⊗₁ g ∘ id ⊗₁ h ∎

  helper2r : ∀ {A B C D} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} →
                   (f ∘ g ∘ h) ⊗₁ id ≈ f ⊗₁ id ∘ g ⊗₁ id ∘ h ⊗₁ id
  helper2r {f = f} {g} {h} = begin
    (f ∘ g ∘ h) ⊗₁ id ≈⟨ refl⟩⊗⟨ helper ○ ⊗-distrib-over-∘ ○ (refl⟩∘⟨ ⊗-distrib-over-∘) ⟩
    f ⊗₁ id ∘ g ⊗₁ id ∘ h ⊗₁ id ∎

  helper3l : ∀ {A B C D E} {f : B ⇒ C} {g : D ⇒ E} {h : A ⇒ B}  →
                   (id ⊗₁ f) ∘ (g ⊗₁ h) ≈ (g ⊗₁ f) ∘ (id ⊗₁ h)
  helper3l {f = f} {g} {h} = begin
    id ⊗₁ f ∘ g ⊗₁ h ≈⟨  merge₂ˡ ○  split₂ʳ  ⟩
    g ⊗₁ f ∘ id ⊗₁ h ∎

  helper3r : ∀ {A B C D E} {f : B ⇒ C} {g : D ⇒ E} {h : A ⇒ B}  →
                   (f ⊗₁ id) ∘ (h ⊗₁ g) ≈ (f ⊗₁ g) ∘ (h ⊗₁ id)
  helper3r {f = f} {g} {h} = begin
    f ⊗₁ id ∘ h ⊗₁ g ≈⟨ (⟺  ⊗split₁ˡ) ○ split₁ʳ  ⟩
    f ⊗₁ g ∘ h ⊗₁ id ∎

  helper4 : ∀ {A B C D E F} {f : A ⇒ B} {g : C ⇒ D} {h : E ⇒ F}  → (id ⊗₁ id ⊗₁ id) ∘ (f ⊗₁ g ⊗₁ h) ≈ f ⊗₁ g ⊗₁ h
  helper4 {f = f} {g} {h} = begin
    (id ⊗₁ id ⊗₁ id) ∘ (f ⊗₁ g ⊗₁ h) ≈⟨ merge₂ˡ ⟩
    f ⊗₁ (id ⊗₁ id ∘ g ⊗₁ h) ≈⟨ refl⟩⊗⟨ merge₂ˡ ⟩
    f ⊗₁ (g ⊗₁ (id ∘ h)) ≈⟨ refl⟩⊗⟨ refl⟩⊗⟨ identityˡ ⟩
    f ⊗₁ g ⊗₁ h ∎

  helper5 : ∀ {A B C D E F} {f : A ⇒ B} {g : C ⇒ D} {h : E ⇒ F}  → (f ⊗₁ g ⊗₁ h) ∘ (id ⊗₁ id ⊗₁ id) ≈ f ⊗₁ g ⊗₁ h
  helper5 {f = f} {g} {h} = begin
    (f ⊗₁ g ⊗₁ h) ∘ (id ⊗₁ id ⊗₁ id) ≈⟨ merge₂ʳ ⟩
    f ⊗₁ (g ⊗₁ h ∘ id ⊗₁ id) ≈⟨ refl⟩⊗⟨ merge₂ʳ ⟩
    f ⊗₁ (g ⊗₁ (h ∘ id)) ≈⟨ refl⟩⊗⟨ refl⟩⊗⟨ identityʳ ⟩
    f ⊗₁ g ⊗₁ h ∎

  helper6 : ∀ {A B C D E} {f : A ⇒  B ⊗₀ C} {g : D ⇒ E}  → (id ⊗₁ id) ⊗₁ id ∘ f ⊗₁ g ≈ f ⊗₁ g
  helper6 {f = f} {g} = begin
    (id ⊗₁ id) ⊗₁ id ∘ f ⊗₁ g ≈⟨ M×.⊗.identity ⟩⊗⟨refl ⟩∘⟨refl ⟩
    id ⊗₁ id ∘ f ⊗₁ g ≈⟨ M×.⊗.identity ⟩∘⟨refl ⟩
    id ∘ f ⊗₁ g ≈⟨ identityˡ ⟩
    f ⊗₁ g ∎

  helper7l : ∀ {A B C D} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} → 
                  id ⊗₁ f ∘ id ⊗₁ g ∘ id ⊗₁ h ≈ id ⊗₁ (f ∘ g ∘ h)
  helper7l {f = f} {g} {h} = begin
     id ⊗₁ f ∘ id ⊗₁ g ∘ id ⊗₁ h ≈⟨ refl⟩∘⟨ merge₂ˡ ⟩
     id ⊗₁ f ∘ id ⊗₁ (g ∘ h) ≈⟨ merge₂ˡ ⟩
     id ⊗₁ (f ∘ g ∘ h) ∎

  helper7r : ∀ {A B C D} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} → 
                  f ⊗₁ id ∘ g ⊗₁ id ∘ h ⊗₁ id ≈ (f ∘ g ∘ h) ⊗₁ id
  helper7r {f = f} {g} {h} = begin
     f ⊗₁ id ∘ g ⊗₁ id ∘ h ⊗₁ id ≈⟨ refl⟩∘⟨ ⟺ split₁ʳ ⟩
     f ⊗₁ id ∘ (g ∘ h) ⊗₁ id ≈⟨ ⟺ split₁ʳ ⟩
     (f ∘ g ∘ h) ⊗₁ id ∎
     
    
  B1 : zZ ≈ Zz
  B1 = begin
    α⇐ ∘ id ⊗₁ Ctrl Z ∘ α⇒ ∘ Ctrl Z ⊗₁ id ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ (⟺  CX↝CZ))  ⟩∘⟨refl ⟩ -- CZ↝CX and bCX↝CZ
    α⇐ ∘ id ⊗₁ (id ⊗₁ H ∘ Ctrl X ∘ id ⊗₁ H) ∘ α⇒ ∘ Ctrl Z ⊗₁ id ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ ((⟺  bCX↝CZ) ⟩⊗⟨refl))) ⟩
    α⇐ ∘ id ⊗₁ (id ⊗₁ H ∘ Ctrl X ∘ id ⊗₁ H) ∘ α⇒ ∘ ((H ⊗₁ id ∘ SWAP) ∘ Ctrl X ∘ (SWAP ∘ H ⊗₁ id)) ⊗₁ id ≈⟨ refl⟩∘⟨ helper2l ⟩∘⟨ (refl⟩∘⟨ helper2r) ⟩
    α⇐ ∘ (id ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ id ⊗₁ id ⊗₁ H) ∘
      α⇒ ∘ ((H ⊗₁ id) ∘ SWAP) ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ (SWAP ∘ (H ⊗₁ id)) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ʳ ⟩∘⟨ refl⟩∘⟨ split₁ʳ ⟩
    α⇐ ∘ (id ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ id ⊗₁ id ⊗₁ H) ∘
      α⇒ ∘ ((H ⊗₁ id) ⊗₁ id ∘ SWAP ⊗₁ id) ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ assoc ○ refl⟩∘⟨ refl⟩∘⟨ assoc   ⟩
    α⇐ ∘ id ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ id ⊗₁ id ⊗₁ H ∘
      α⇒ ∘ ((H ⊗₁ id) ⊗₁ id ∘ SWAP ⊗₁ id) ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    α⇐ ∘ id ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ id ⊗₁ id ⊗₁ H ∘
      α⇒ ∘ (H ⊗₁ id) ⊗₁ id ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺  assoc ⟩  --bifunc
    α⇐ ∘ id ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ id ⊗₁ id ⊗₁ H ∘
      (α⇒ ∘ (H ⊗₁ id) ⊗₁ id) ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺  (Equiv.sym M×.assoc-commute-from) ⟩∘⟨refl ⟩
    α⇐ ∘ id ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ id ⊗₁ id ⊗₁ H ∘
      (H ⊗₁ id ⊗₁ id ∘ α⇒ ) ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺  assoc ⟩
    α⇐ ∘ id ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ (id ⊗₁ id ⊗₁ H ∘
      H ⊗₁ id ⊗₁ id) ∘ α⇒  ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ helper3l ⟩∘⟨refl ⟩
    α⇐ ∘ id ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ (H ⊗₁ id ⊗₁ H ∘
      id ⊗₁ id ⊗₁ id) ∘ α⇒  ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ○ refl⟩∘⟨ refl⟩∘⟨ ⟺  assoc ⟩
    α⇐ ∘ id ⊗₁ id ⊗₁ H ∘ (id ⊗₁ Ctrl X ∘ H ⊗₁ id ⊗₁ H) ∘
      id ⊗₁ id ⊗₁ id ∘ α⇒  ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ helper3l ⟩∘⟨refl  ⟩
    α⇐ ∘ id ⊗₁ id ⊗₁ H ∘ (H ⊗₁ Ctrl X ∘ id ⊗₁ id ⊗₁ H) ∘
      id ⊗₁ id ⊗₁ id ∘ α⇒  ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ○ refl⟩∘⟨ ⟺  assoc  ⟩
    α⇐ ∘ (id ⊗₁ id ⊗₁ H ∘ H ⊗₁ Ctrl X) ∘ id ⊗₁ id ⊗₁ H ∘
      id ⊗₁ id ⊗₁ id ∘ α⇒  ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ helper3l ⟩∘⟨refl ⟩
    α⇐ ∘ (H ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X) ∘ id ⊗₁ id ⊗₁ H ∘
      id ⊗₁ id ⊗₁ id ∘ α⇒  ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ assoc ⟩
    α⇐ ∘ H ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ id ⊗₁ id ⊗₁ H ∘
      id ⊗₁ id ⊗₁ id ∘ α⇒  ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺  assoc ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ helper5 ⟩∘⟨refl ⟩
    α⇐ ∘ H ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ id ⊗₁ id ⊗₁ H ∘
      α⇒  ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺  assoc  ⟩
    α⇐ ∘ H ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ (id ⊗₁ id ⊗₁ H ∘
      α⇒)  ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺  M×.assoc-commute-from ⟩∘⟨refl ⟩
    α⇐ ∘ H ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ (α⇒ ∘ (id ⊗₁ id) ⊗₁ H)  ∘ 
      SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    α⇐ ∘ H ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ (id ⊗₁ id) ⊗₁ H ∘ 
      SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺  assoc  ⟩
    α⇐ ∘ H ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ ((id ⊗₁ id) ⊗₁ H ∘ 
      SWAP ⊗₁ id) ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺  helper3r ⟩∘⟨refl ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    α⇐ ∘ H ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ (id ⊗₁ id) ⊗₁ id ∘ 
      SWAP ⊗₁ H ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨  refl⟩∘⟨ ⟺  assoc ⟩
    α⇐ ∘ H ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ (id ⊗₁ id) ⊗₁ id ∘ 
      (SWAP ⊗₁ H ∘ Ctrl X ⊗₁ id) ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺  helper3r ⟩∘⟨refl ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc  ⟩
    α⇐ ∘ H ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ (id ⊗₁ id) ⊗₁ id ∘ 
      SWAP ⊗₁ id ∘ Ctrl X ⊗₁ H ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨  refl⟩∘⟨ refl⟩∘⟨ ⟺   assoc ⟩
    α⇐ ∘ H ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ (id ⊗₁ id) ⊗₁ id ∘ 
      SWAP ⊗₁ id ∘ (Ctrl X ⊗₁ H ∘ SWAP ⊗₁ id) ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺  helper3r ⟩∘⟨refl ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    α⇐ ∘ H ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ (id ⊗₁ id) ⊗₁ id ∘ 
      SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ H ∘ (H ⊗₁ id) ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺  helper3r ⟩
    α⇐ ∘ H ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ (id ⊗₁ id) ⊗₁ id ∘ 
      SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ H ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺  assoc ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ helper6  ⟩∘⟨refl ⟩
    α⇐ ∘ H ⊗₁ id ⊗₁ H ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ 
      SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ H ≈⟨ ⟺   assoc  ⟩
    (α⇐ ∘ H ⊗₁ id ⊗₁ H) ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ 
      SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ H ≈⟨ M×.assoc-commute-to ⟩∘⟨refl  ⟩
    ((H ⊗₁ id) ⊗₁ H ∘
      α⇐) ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id
      ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ H                                  ≈⟨ assoc ⟩
      
    (H ⊗₁ id) ⊗₁ H ∘
      α⇐ ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id
      ∘ SWAP ⊗₁ id ∘ (H ⊗₁ id) ⊗₁ H                                  ≈⟨  refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺  assoc ⟩

    (H ⊗₁ id) ⊗₁ H ∘
      α⇐ ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ SWAP ⊗₁ id ∘ (Ctrl X ⊗₁ id
      ∘ SWAP ⊗₁ id) ∘ (H ⊗₁ id) ⊗₁ H                              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨  refl⟩∘⟨ ⟺  assoc ⟩

    (H ⊗₁ id) ⊗₁ H ∘
      α⇐ ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ (SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id
      ∘ SWAP ⊗₁ id) ∘ (H ⊗₁ id) ⊗₁ H                              ≈⟨ refl⟩∘⟨ refl⟩∘⟨  refl⟩∘⟨ ⟺  assoc ⟩

    (H ⊗₁ id) ⊗₁ H ∘
      α⇐ ∘ id ⊗₁ Ctrl X ∘ (α⇒ ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id
      ∘ SWAP ⊗₁ id) ∘ (H ⊗₁ id) ⊗₁ H                              ≈⟨ refl⟩∘⟨  refl⟩∘⟨ ⟺  assoc ⟩

    (H ⊗₁ id) ⊗₁ H ∘
      α⇐ ∘ (id ⊗₁ Ctrl X ∘ α⇒ ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id
      ∘ SWAP ⊗₁ id) ∘ (H ⊗₁ id) ⊗₁ H                              ≈⟨ refl⟩∘⟨ ⟺  assoc ⟩

    (H ⊗₁ id) ⊗₁ H ∘
      (α⇐ ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id
      ∘ SWAP ⊗₁ id) ∘ (H ⊗₁ id) ⊗₁ H                                  ≈⟨ refl⟩∘⟨ P1 ⟩∘⟨refl ⟩

    (H ⊗₁ id) ⊗₁ H ∘ (SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ 
      SWAP ⊗₁ id ∘ α⇐ ∘ id ⊗₁ Ctrl X ∘ α⇒) ∘ (H ⊗₁ id) ⊗₁ H            ≈⟨ refl⟩∘⟨  assoc ⟩

    (H ⊗₁ id) ⊗₁ H ∘ SWAP ⊗₁ id ∘ (Ctrl X ⊗₁ id ∘ 
      SWAP ⊗₁ id ∘ α⇐ ∘ id ⊗₁ Ctrl X ∘ α⇒) ∘ (H ⊗₁ id) ⊗₁ H            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩

    (H ⊗₁ id) ⊗₁ H ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ 
      (SWAP ⊗₁ id ∘ α⇐ ∘ id ⊗₁ Ctrl X ∘ α⇒) ∘ (H ⊗₁ id) ⊗₁ H            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩

    (H ⊗₁ id) ⊗₁ H ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ 
      SWAP ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ Ctrl X ∘ α⇒) ∘ (H ⊗₁ id) ⊗₁ H            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩

    (H ⊗₁ id) ⊗₁ H ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ 
      SWAP ⊗₁ id ∘ α⇐ ∘ (id ⊗₁ Ctrl X ∘ α⇒) ∘ (H ⊗₁ id) ⊗₁ H            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩

    (H ⊗₁ id) ⊗₁ H ∘ SWAP ⊗₁ id ∘ Ctrl X ⊗₁ id ∘ 
      SWAP ⊗₁ id ∘ α⇐ ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ (H ⊗₁ id) ⊗₁ H            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺  assoc ○  refl⟩∘⟨ refl⟩∘⟨ ⟺  ⊗split₁ˡ ⟩∘⟨refl ⟩

    (H ⊗₁ id) ⊗₁ H ∘ SWAP ⊗₁ id ∘ (Ctrl X ∘ 
      SWAP) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ (H ⊗₁ id) ⊗₁ H            ≈⟨ refl⟩∘⟨ ⟺  assoc ○  refl⟩∘⟨ ⟺  ⊗split₁ˡ ⟩∘⟨refl  ⟩

    (H ⊗₁ id) ⊗₁ H ∘ (SWAP ∘ Ctrl X ∘ SWAP) ⊗₁ id 
      ∘ α⇐ ∘ id ⊗₁ Ctrl X ∘ α⇒ ∘ (H ⊗₁ id) ⊗₁ H                        ≈⟨ refl⟩∘⟨ (⟺  sCZ↝bCX ⟩⊗⟨refl) ⟩∘⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⟺  CZ↝CX) ⟩∘⟨refl ⟩

    (H ⊗₁ id) ⊗₁ H ∘ (H ⊗₁ id ∘ Ctrl Z ∘ H ⊗₁ id) ⊗₁ id 
      ∘ α⇐ ∘ id ⊗₁ (id ⊗₁ H ∘ Ctrl Z ∘ id ⊗₁ H) ∘ α⇒ ∘ (H ⊗₁ id) ⊗₁ H  ≈⟨ refl⟩∘⟨ ⟺  helper7r ⟩∘⟨ refl⟩∘⟨ ⟺  helper7l ⟩∘⟨refl  ⟩

    (H ⊗₁ id) ⊗₁ H ∘ ((H ⊗₁ id) ⊗₁ id ∘ Ctrl Z ⊗₁ id 
      ∘ (H ⊗₁ id) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ id ⊗₁ (id ⊗₁ H)) ∘ α⇒ ∘ (H ⊗₁ id) ⊗₁ H       ≈⟨ refl⟩∘⟨ assoc ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc  ⟩

    (H ⊗₁ id) ⊗₁ H ∘ (H ⊗₁ id) ⊗₁ id ∘ (Ctrl Z ⊗₁ id
      ∘ (H ⊗₁ id) ⊗₁ id) ∘ α⇐ ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ (id ⊗₁ Ctrl Z ∘ id ⊗₁ (id ⊗₁ H)) ∘ α⇒ ∘ (H ⊗₁ id) ⊗₁ H       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩

    (H ⊗₁ id) ⊗₁ H ∘ (H ⊗₁ id) ⊗₁ id ∘ Ctrl Z ⊗₁ id 
      ∘ (H ⊗₁ id) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ id ⊗₁ (id ⊗₁ H) ∘ α⇒ ∘ (H ⊗₁ id) ⊗₁ H      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (⟺  assoc ○ ⟺  M×.assoc-commute-from ⟩∘⟨refl ○ assoc) ⟩

    (H ⊗₁ id) ⊗₁ H ∘ (H ⊗₁ id) ⊗₁ id ∘ Ctrl Z ⊗₁ id 
      ∘ (H ⊗₁ id) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ α⇒ ∘ (id ⊗₁ id) ⊗₁ H ∘ (H ⊗₁ id) ⊗₁ H      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ M×.⊗.identity ⟩⊗⟨refl ⟩∘⟨refl ⟩

    (H ⊗₁ id) ⊗₁ H ∘ (H ⊗₁ id) ⊗₁ id ∘ Ctrl Z ⊗₁ id 
      ∘ (H ⊗₁ id) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ α⇒ ∘ id ⊗₁ H ∘ (H ⊗₁ id) ⊗₁ H      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ merge₂ˡ ⟩

    (H ⊗₁ id) ⊗₁ H ∘ (H ⊗₁ id) ⊗₁ id ∘ Ctrl Z ⊗₁ id 
      ∘ (H ⊗₁ id) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ α⇒ ∘ (H ⊗₁ id) ⊗₁ (H ∘ H)      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ A4 ⟩

    (H ⊗₁ id) ⊗₁ H ∘ (H ⊗₁ id) ⊗₁ id ∘ Ctrl Z ⊗₁ id 
      ∘ (H ⊗₁ id) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ α⇒ ∘ (H ⊗₁ id) ⊗₁ id      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ M×.assoc-commute-from ⟩

    (H ⊗₁ id) ⊗₁ H ∘ (H ⊗₁ id) ⊗₁ id ∘ Ctrl Z ⊗₁ id 
      ∘ (H ⊗₁ id) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ H ⊗₁ (id ⊗₁ id) ∘ α⇒      ≈⟨ ⟺  assoc ○ ⟺  split₁ʳ ⟩∘⟨refl ⟩

    ((H ⊗₁ id) ∘ (H ⊗₁ id)) ⊗₁ H ∘ Ctrl Z ⊗₁ id 
      ∘ (H ⊗₁ id) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ H ⊗₁ (id ⊗₁ id) ∘ α⇒      ≈⟨ ⟺  split₁ʳ ⟩⊗⟨refl ⟩∘⟨refl  ⟩

    ((H ∘ H) ⊗₁ id) ⊗₁ H ∘ Ctrl Z ⊗₁ id 
      ∘ (H ⊗₁ id) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ H ⊗₁ (id ⊗₁ id) ∘ α⇒      ≈⟨ A4 ⟩⊗⟨refl ⟩⊗⟨refl ⟩∘⟨refl  ⟩

    (id ⊗₁ id) ⊗₁ H ∘ Ctrl Z ⊗₁ id 
      ∘ (H ⊗₁ id) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ H ⊗₁ (id ⊗₁ id) ∘ α⇒      ≈⟨ M×.⊗.identity ⟩⊗⟨refl ⟩∘⟨refl  ⟩

    id ⊗₁ H ∘ Ctrl Z ⊗₁ id 
      ∘ (H ⊗₁ id) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ H ⊗₁ (id ⊗₁ id) ∘ α⇒      ≈⟨ ⟺  assoc ○ ⟺  split₁ʳ ⟩∘⟨refl ⟩

    (id ∘ Ctrl Z) ⊗₁ H
      ∘ (H ⊗₁ id) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ H ⊗₁ (id ⊗₁ id) ∘ α⇒      ≈⟨ identityˡ ⟩⊗⟨refl ⟩∘⟨refl  ⟩ 

    Ctrl Z ⊗₁ H
      ∘ (H ⊗₁ id) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ H ⊗₁ (id ⊗₁ id) ∘ α⇒      ≈⟨ refl⟩∘⟨  ⟺  assoc ○ refl⟩∘⟨ ⟺  M×.assoc-commute-to ⟩∘⟨refl ○ refl⟩∘⟨  assoc ⟩ 

    Ctrl Z ⊗₁ H
      ∘ α⇐ ∘ H ⊗₁ (id ⊗₁ id) ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ H ⊗₁ (id ⊗₁ id) ∘ α⇒      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ M×.⊗.identity ⟩∘⟨refl  ⟩ 

    Ctrl Z ⊗₁ H
      ∘ α⇐ ∘ H ⊗₁ id ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ H ⊗₁ (id ⊗₁ id) ∘ α⇒      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ M×.⊗.identity ⟩∘⟨refl  ⟩ 

    Ctrl Z ⊗₁ H
      ∘ α⇐ ∘ H ⊗₁ id ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ H ⊗₁ id ∘ α⇒      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (⟺  assoc ○ merge₂ˡ ⟩∘⟨refl) ⟩ 

    Ctrl Z ⊗₁ H
      ∘ α⇐ ∘ H ⊗₁ id ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ H ⊗₁ (Ctrl Z ∘ id) ∘ α⇒      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ identityʳ ⟩∘⟨refl ⟩ 

    Ctrl Z ⊗₁ H
      ∘ α⇐ ∘ H ⊗₁ id ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ H ⊗₁ Ctrl Z ∘ α⇒      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (⟺  assoc ○ helper3l ⟩∘⟨refl) ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩ 

    Ctrl Z ⊗₁ H
      ∘ α⇐ ∘ H ⊗₁ id ∘ H ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ α⇒      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (⟺  assoc ○ ⟺  ⊗split₁ˡ ⟩∘⟨refl) ⟩ 

    Ctrl Z ⊗₁ H
      ∘ α⇐ ∘ (H ∘ H) ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ α⇒      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ A4 ⟩⊗⟨refl ⟩∘⟨refl ⟩ 

    Ctrl Z ⊗₁ H ∘ α⇐ ∘ id ⊗₁ (id ⊗₁ H) 
        ∘ id ⊗₁ Ctrl Z ∘ α⇒      ≈⟨ refl⟩∘⟨ ⟺  assoc ○ refl⟩∘⟨ M×.assoc-commute-to ⟩∘⟨refl ○ refl⟩∘⟨ assoc ⟩ 

    Ctrl Z ⊗₁ H ∘ (id ⊗₁ id) ⊗₁ H ∘ α⇐
        ∘ id ⊗₁ Ctrl Z ∘ α⇒      ≈⟨ refl⟩∘⟨ M×.⊗.identity ⟩⊗⟨refl ⟩∘⟨refl ⟩

    Ctrl Z ⊗₁ H ∘ id ⊗₁ H ∘ α⇐
        ∘ id ⊗₁ Ctrl Z ∘ α⇒      ≈⟨ ⟺  assoc ○  ⟺  split₂ʳ ⟩∘⟨refl ⟩ 

    Ctrl Z ⊗₁ (H ∘ H) ∘ α⇐
        ∘ id ⊗₁ Ctrl Z ∘ α⇒      ≈⟨ refl⟩⊗⟨ A4 ⟩∘⟨refl ⟩ 

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
