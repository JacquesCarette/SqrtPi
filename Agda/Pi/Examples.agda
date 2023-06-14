{-# OPTIONS --without-K --exact-split #-}

module Pi.Examples where

open import Data.Nat using (ℕ)

open import Pi.Types using (U; _×ᵤ_; 𝟚) 
open import Pi.Language using (_⟷_; id⟷; _⊕_; _⊗_; _◎_; ω; V; assocl⋆; assocr⋆)
open import Pi.Terms using (ctrl; ctrl'; X; CX; CCX; SWAP)
open import Pi.Scalars using (Scalar; _^_; _●_) 
open import Pi.Equivalences 

-------------------------------------------------------------------------------------
-- Common gates

φ : Scalar → (𝟚 ⟷ 𝟚)
φ s = id⟷ ⊕ s

R : ℕ → (𝟚 ⟷ 𝟚)
R n = φ (ω ^ n)

Z S T H : 𝟚 ⟷ 𝟚
Z = R 4
S = R 2
T = R 1
H = ω ● (X ◎ S ◎ V ◎ S ◎ X)  

CZ : 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚
CZ = ctrl Z

-- Bell circuit

bell : 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚
bell = (H ⊗ id⟷) ◎ CX

-- QFT on 3 qubits

qft1 : 𝟚 ⟷ 𝟚
qft1 = H

qft2 : 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚
qft2 = (H ⊗ id⟷) ◎ ctrl' (R 2) ◎ (id⟷ ⊗ qft1)

qft3 : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
qft3 =
  (H ⊗ id⟷) ◎
  (assocl⋆ ◎ (ctrl' (R 2) ⊗ id⟷) ◎ assocr⋆) ◎ 
  ((id⟷ ⊗ SWAP) ◎ (assocl⋆ ◎ (ctrl' (R 3) ⊗ id⟷) ◎ assocr⋆) ◎ id⟷ ⊗ SWAP) ◎ 
  id⟷ ⊗ qft2

-- Examples of reasoning

-- Tiny proof for intro

SS≡Z : S ◎ S ⟷₂ Z 
SS≡Z = trans⟷₂ hom◎⊕⟷₂ (resp⊕⟷₂ idl◎l assoc◎r)

HH≡id : H ◎ H ⟷₂ id⟷
HH≡id = {!!} -- p.13

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
