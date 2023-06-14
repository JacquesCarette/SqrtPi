{-# OPTIONS --without-K --exact-split --safe #-}

module Categorical.SqrtRig where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Level using (_⊔_)

open import Categories.Category -- we need it all
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Utilities using (module Shorthands)
open import Categories.Category.RigCategory

-- A bit of useful kit
module Kit {o ℓ e} {C : Category o ℓ e} {M⊎ M× : Monoidal C} {S⊎ : Symmetric M⊎}
  {S× : Symmetric M×} (R : RigCategory C S⊎ S×) where

  open Category C
  private
    module C = Category C
    module M⊎ = Monoidal M⊎
    module M× = Monoidal M×
    module S⊎ = Symmetric S⊎
    module S× = Symmetric S×

  open M× using (_⊗₀_; _⊗₁_) public
  open M⊎ using () renaming (_⊗₀_ to _⊕₀_; _⊗₁_ to _⊕₁_) public
  open Shorthands M× using (λ⇒; λ⇐; ρ⇒; ρ⇐) public
  
  σ⊕ : ∀ {X Y} → X ⊕₀ Y ⇒ Y ⊕₀ X
  σ⊕ {X} {Y} = S⊎.braiding.⇒.η (X , Y)
  
  0C 1C 2C : Obj
  0C = M⊎.unit
  1C = M×.unit
  2C = 1C ⊕₀ 1C

  Scalar : Set ℓ
  Scalar = C [ 1C , 1C ]
  Endo : {Obj} → Set ℓ
  Endo {a} = C [ a , a ]
    
  -- To make things shorter, define an abbreviation for 1
  𝟙 : Scalar
  𝟙 = C.id

  -- We need an operator for powering of endos (such as scalars)
  infixr 30 _^_
  _^_ : {a : Obj} → Endo {a} → ℕ → Endo
  s ^ zero = C.id
  s ^ (suc zero) = s -- special case to make reasoning less painful
  s ^ suc (suc n) = s ∘ s ^ (suc n)

  -- Scalar multiplication (Definition 4.1)
  infixr 45 _●_
  _●_ : {t₁ t₂ : Obj} → Scalar → C [ t₁ , t₂ ] → C [ t₁ , t₂ ]
  s ● c = λ⇒ ∘ (s ⊗₁ c) ∘ λ⇐

-- Definition 4.2
record SqrtRig {o ℓ e} {C : Category o ℓ e} {M⊎ M× : Monoidal C} {S⊎ : Symmetric M⊎}
  {S× : Symmetric M×} (R : RigCategory C S⊎ S×) : Set (ℓ ⊔ e) where
  open Kit R
  open Category C
    
  field
    ω : Scalar
    V : C [ 2C , 2C ]
    E1 : ω ^ 8 ≈ id
    E2 : V ∘ V ≈ σ⊕
    
  S : C [ 2C , 2C ]
  S = id ⊕₁ (ω ^ 2)
  
  field
    E3 : V ∘ S ∘ V ≈ (ω ^ 2) ● S ∘ V ∘ S
