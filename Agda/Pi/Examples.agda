{-# OPTIONS --without-K --exact-split #-}

module Pi.Examples where

open import Pi.Types using (U; I; 𝟚)
open import Pi.Language using (_⟷_; id⟷; _◎_; _⊕_; ω)
open import Pi.Scalars using (-𝟙; i; _^_)
open import Pi.Equivalences 

private
  variable
    t : U
    
-------------------------------------------------------------------------------------
-- Common gates

Scalar : Set
Scalar = I ⟷ I

e^iπ/4 : Scalar
e^iπ/4 = ω ^ 2

Z S T : 𝟚 ⟷ 𝟚
Z = id⟷ ⊕ -𝟙 
S = id⟷ ⊕ i
T = id⟷ ⊕ e^iπ/4

SS≡Z : S ◎ S ⟷₂ Z 
SS≡Z = trans⟷₂ hom◎⊕⟷₂ (resp⊕⟷₂ idl◎l id⟷₂) 


-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
