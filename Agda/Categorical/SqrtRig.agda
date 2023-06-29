{-# OPTIONS --without-K --exact-split --safe #-}

module Categorical.SqrtRig where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_)
open import Level using (_⊔_)

open import Categories.Category -- we need it all
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Utilities using (module Shorthands)
import Categories.Morphism as Mor
open import Categories.Category.RigCategory

-- A bit of useful kit
module Kit {o ℓ e} {C : Category o ℓ e} {M⊎ M× : Monoidal C} {S⊎ : Symmetric M⊎}
  {S× : Symmetric M×} (R : RigCategory C S⊎ S×) where

  open Category C
  open HomReasoning
  open Mor C using (_≅_)
  private
    module C = Category C

  open RigCategory R public -- everything!
  open M× using (_⊗₀_; _⊗₁_) public
  open M⊎ using () renaming (_⊗₀_ to _⊕₀_; _⊗₁_ to _⊕₁_) public
  open Shorthands M× using (λ⇒; λ⇐; ρ⇒; ρ⇐; α⇒; α⇐) public

  module dr {X} {Y} {Z} = _≅_ (distribᵣ {X} {Y} {Z})
    
  σ⊕ : ∀ {X Y} → X ⊕₀ Y ⇒ Y ⊕₀ X
  σ⊕ {X} {Y} = S⊎.braiding.⇒.η (X , Y)
  σ⊗ : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
  σ⊗ {X} {Y} = S×.braiding.⇒.η (X , Y)

  δᵣ⇒ : ∀ {X Y Z} → (X ⊕₀ Y) ⊗₀ Z ⇒ (X ⊗₀ Z) ⊕₀ (Y ⊗₀ Z)
  δᵣ⇒ = dr.from
  δᵣ⇐ : ∀ {X Y Z} → (X ⊗₀ Z) ⊕₀ (Y ⊗₀ Z) ⇒ (X ⊕₀ Y) ⊗₀ Z
  δᵣ⇐ = dr.to
  
  0C 1C 2C : Obj
  0C = M⊎.unit
  1C = M×.unit
  2C = 1C ⊕₀ 1C

  Scalar : Set ℓ
  Scalar = C [ 1C , 1C ]
  Endo : {Obj} → Set ℓ
  Endo {a} = C [ a , a ]
  2×2 : Set ℓ
  2×2 = C [ 2C , 2C ]
    
  -- To make things shorter, define an abbreviation for 1
  𝟙 : Scalar
  𝟙 = C.id

  -- We need an operator for powering of endos (such as scalars)
  infixr 30 _^_
  _^_ : {a : Obj} → Endo {a} → ℕ → Endo
  s ^ zero = C.id
  s ^ (suc zero) = s -- special case to make reasoning less painful
  s ^ suc (suc n) = s ∘ s ^ (suc n)

  -- really, we might as well prove stuff about powering
  -- proving things directly about _^_ is annoying because of the
  -- optimized definition. So take the roundabout route.
  pow : Scalar → ℕ → Scalar
  pow s zero = id
  pow s (suc n) = s ∘ pow s n

  -- note how these are NOT equal on-the-nose, which is the whole
  -- point of having _^_
  ^≈pow : (s : Scalar) (n : ℕ) → s ^ n ≈ pow s n
  ^≈pow s zero = Equiv.refl
  ^≈pow s (suc zero) = Equiv.sym identityʳ
  ^≈pow s (suc (suc n)) = refl⟩∘⟨ ^≈pow s (suc n) 

  pow-add : (s : Scalar) (a b : ℕ) → pow s a ∘ pow s b ≈ pow s (a + b)
  pow-add s zero b = identityˡ
  pow-add s (suc a) b = Equiv.trans assoc (∘-resp-≈ʳ (pow-add s a b))
  
  ^-add : (s : Scalar) (a b : ℕ) → s ^ a ∘ s ^ b ≈ s ^ (a + b)
  ^-add s a b = begin
    s ^ a ∘ s ^ b     ≈⟨ (^≈pow s a ⟩∘⟨ ^≈pow s b) ⟩
    pow s a ∘ pow s b ≈⟨ pow-add s a b ⟩
    pow s (a + b)     ≈˘⟨ ^≈pow s (a + b) ⟩
    s ^ (a + b)   ∎

  ^-cong : {a : Obj} {x y : Endo {a}} → x ≈ y → (n : ℕ) → x ^ n ≈ y ^ n
  ^-cong x≈y zero = Equiv.refl
  ^-cong x≈y (suc zero) = x≈y
  ^-cong x≈y (suc (suc n)) = ∘-resp-≈ x≈y (^-cong x≈y (suc n))
  
  -- Scalar multiplication (Definition 4.1)
  infixr 25 _●_
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
    E3 : V ∘ S ∘ V ≈ ω ^ 2 ● S ∘ V ∘ S

  -- the paper actually works in a Rig Groupoid in some places. Let's start
  -- small to actually express what is in the lemmas
  field
    inv : Scalar → Scalar
    invˡ : (s : Scalar) → inv s ∘ s ≈ 𝟙
    invʳ : (s : Scalar) → s ∘ inv s ≈ 𝟙
