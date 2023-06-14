{-# OPTIONS --without-K --exact-split --safe #-}

module Pi.Terms where

open import Pi.Types using (U; _+ᵤ_; _×ᵤ_; 𝟚)
open import Pi.Language
  using (_⟷_; id⟷; _◎_; _⊕_; _⊗_; 
         unite⋆l; dist; factor; swap₊; swap⋆; assocr₊; assocl₊)

private
  variable
    t t₁ t₂ t₃ t₄ : U
    
-------------------------------------------------------------------------------------
-- Common terms

-- control qubit is the first one

ctrl : t ⟷ t → (𝟚 ×ᵤ t) ⟷ (𝟚 ×ᵤ t)
ctrl c = dist ◎ (id⟷ ⊕ id⟷ ⊗ c) ◎ factor

-- control qubit is the second one

ctrl' : (t ⟷ t) → (t ×ᵤ 𝟚 ⟷ t ×ᵤ 𝟚)
ctrl' g = swap⋆ ◎ ctrl g ◎ swap⋆ 

-- classical gates

X : 𝟚 ⟷ 𝟚
X = swap₊

CX : 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚
CX = ctrl X

CCX : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
CCX = ctrl CX

SWAP : 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚
SWAP = swap⋆

-- helpful combinators

midswap : (t₁ +ᵤ t₂) +ᵤ (t₃ +ᵤ t₄) ⟷ (t₁ +ᵤ t₃) +ᵤ (t₂ +ᵤ t₄)
midswap = assocr₊ ◎ 
          (id⟷ ⊕ assocl₊) ◎ 
          (id⟷ ⊕ (swap₊ ⊕ id⟷)) ◎ 
          (id⟷ ⊕ assocr₊) ◎
          assocl₊

mat : 𝟚 ×ᵤ t ⟷ t +ᵤ t
mat = dist ◎ unite⋆l ⊕ unite⋆l

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
