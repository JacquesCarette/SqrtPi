{-# OPTIONS --without-K --exact-split #-}

module Pi.Examples where

open import Pi.Types using (U; I; 𝟚; _+ᵤ_; _×ᵤ_)
open import Pi.Language
  using (_⟷_; id⟷; swap₊; swap⋆; dist; _◎_; _⊕_; ω; V;
         unite⋆l; assocl₊; assocr₊)
open import Pi.Terms using (ctrl; x; cx; ccx)
open import Pi.Scalars using (-𝟙; i; _^_; _●_)
open import Pi.Equivalences 

private
  variable
    t t₁ t₂ t₃ t₄ : U
    
-------------------------------------------------------------------------------------
-- Common gates

Scalar : Set
Scalar = I ⟷ I

e^iπ/4 √-i : Scalar
e^iπ/4 = ω ^ 2
√-i = ω ^ 3

φ : Scalar → (𝟚 ⟷ 𝟚)
φ s = id⟷ ⊕ s

X Z S T H : 𝟚 ⟷ 𝟚
X = x
Z = φ -𝟙 
S = φ i
T = φ e^iπ/4
H = √-i ● (S ◎ V ◎ S)
H' = ω ● (X ◎ S ◎ V ◎ S ◎ X)  -- same as H ??

CX CZ SWAP : 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚
CX = cx
CZ = ctrl Z
SWAP = swap⋆

CCX : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
CCX = ccx

midswap : (t₁ +ᵤ t₂) +ᵤ (t₃ +ᵤ t₄) ⟷ (t₁ +ᵤ t₃) +ᵤ (t₂ +ᵤ t₄)
midswap = assocr₊ ◎ 
          (id⟷ ⊕ assocl₊) ◎ 
          (id⟷ ⊕ (swap₊ ⊕ id⟷)) ◎ 
          (id⟷ ⊕ assocr₊) ◎
          assocl₊

mat : 𝟚 ×ᵤ t ⟷ t +ᵤ t
mat = dist ◎ unite⋆l ⊕ unite⋆l

-- Tiny proof for intro

SS≡Z : S ◎ S ⟷₂ Z 
SS≡Z = trans⟷₂ hom◎⊕⟷₂ (resp⊕⟷₂ idl◎l id⟷₂) 



-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
