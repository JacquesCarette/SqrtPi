{-# OPTIONS --without-K --exact-split #-}

module Pi.Norm where

open import Pi.Types using (U; _+ᵤ_; _×ᵤ_; I; 𝟚) 
open import Pi.Language
  using (_⟷_; id⟷; _⊕_; _⊗_; _◎_; ω; V;
         swap₊; assocl₊; assocr₊; assocl⋆; assocr⋆;
         uniti⋆r; unite⋆r)
open import Pi.Terms using (ctrl; ctrl'; X; CX; CCX; SWAP)
open import Pi.Scalars using (Scalar; _^_; _●_) 
open import Pi.Equivalences 

𝟛 : U
𝟛 = 𝟚 +ᵤ I

f₁ f₂ : 𝟚 ⟷ 𝟚
f₁ = swap₊ ◎ id⟷
f₂ = uniti⋆r ◎ (swap₊ ⊗ id⟷) ◎ unite⋆r

f₁≡f₂ : f₁ ⟷₂ f₂
f₁≡f₂ = {!!}

g₁ g₂ : 𝟛 ⟷ 𝟛
g₁ = assocr₊ ◎ swap₊
g₂ = (swap₊ ⊕ id⟷) ◎ assocr₊ ◎ (id⟷ ⊕ swap₊) ◎ assocl₊

g₁≡g₂ : g₁ ⟷₂ g₂
g₁≡g₂ = {!!}

p₁ p₂ p₃ p₄ p₅ : f₁ ⊕ g₁ ⟷₂ f₂ ⊕ g₂
p₁ = resp⊕⟷₂ f₁≡f₂ g₁≡g₂ 
p₂ = trans⟷₂ hom⊕◎⟷₂ {!!} 
p₃ = {!!} 
p₄ = {!!} 
p₅ = {!!} 

-- (f₁ ⊕ f₂) ◎ (g₁ ⊕ g₂)
