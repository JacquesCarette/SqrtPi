{-# OPTIONS --without-K --exact-split #-}

open import Categories.Category -- we need it all
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.RigCategory

open import Categorical.SqrtRig

-- Everything is over a SqrtRig
module Categorical.Examples {o ℓ e} {C : Category o ℓ e}
  {M⊎ M× : Monoidal C} {S⊎ : Symmetric M⊎}
  {S× : Symmetric M×} {R : RigCategory C S⊎ S×} (SR : SqrtRig R) where

open import Categorical.Scalars SR
open import Categorical.Gates SR

open Category C
open HomReasoning
open SqrtRig SR
open Kit R

Ctrl′ : {A : Obj} (m : Endo A) → A ⊗₀ 2C ⇒ A ⊗₀ 2C
Ctrl′ m = σ⊗ ∘ Ctrl m ∘ σ⊗

-------------------------------------------------------------------------------------
-- Bell circuit
bell :  2C ⊗₀ 2C ⇒ 2C ⊗₀ 2C
bell = (H ⊗₁ id) ∘ CX

-- QFT on 3 qubits

qft1 : C [ 2C , 2C ]
qft1 = H

qft2 :  2C ⊗₀ 2C ⇒ 2C ⊗₀ 2C
qft2 = H ⊗₁ id ∘ Ctrl′ S ∘ id ⊗₁ qft1

qft3 :  2C ⊗₀ 2C ⊗₀ 2C ⇒ 2C ⊗₀ 2C ⊗₀ 2C
qft3 = (H ⊗₁ id) ∘
  (α⇒ ∘ Ctrl′ S ⊗₁ id ∘ α⇐) ∘
  ((id ⊗₁ σ⊗) ∘ (α⇒ ∘ Ctrl′ (P (ω ^ 3)) ⊗₁ id ∘ α⇐) ∘ (id ⊗₁ σ⊗)) ∘
  id ⊗₁ qft2
  
-- Examples of reasoning

-- Tiny proof for intro

SS≡Z : S ∘ S ≈ Z 
SS≡Z = S²≡Z -- from Gates.agda

{- This is A4 in 2Clifford.agda
HH≡id : H ∘ H ≈ id
HH≡id = {!!} -- p.13
-}
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
