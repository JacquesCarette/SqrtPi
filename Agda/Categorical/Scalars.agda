{-# OPTIONS --without-K --exact-split #-}
-- not --safe right now, as we use postulates because some of the proofs
-- are rather larger, and will be back-filled.

module Categorical.Scalars where

open import Data.Nat using (ℕ; zero; suc)

open import Categories.Category -- we need it all
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Properties using (module Kelly's)
open import Categories.Category.RigCategory

open import Categorical.SqrtRig

-- Everything is over a SqrtRig
module _ {o ℓ e} {C : Category o ℓ e} {M⊎ M× : Monoidal C} {S⊎ : Symmetric M⊎}
  {S× : Symmetric M×} {R : RigCategory C S⊎ S×} (SR : SqrtRig R) where

  open Category C -- all of it
  open HomReasoning
  open SqrtRig SR
  open Kit R
  
  private
    module M⊎ = Monoidal M⊎
    module M× = Monoidal M×
    module S⊎ = Symmetric S⊎
    module S× = Symmetric S×
    open M⊎ renaming (_⊗₀_ to _⊕₀_; _⊗₁_ to _⊕₁_)
    open M×

  -- Define some of our constants.
  i -i -𝟙 : Scalar
  i  = ω ^ 2
  -𝟙 = i ^ 2
  -i = ω ^ 6

  -- coherence of definitions (by associativity of ∘ )
  -i≡-𝟙◎i : -i ≈ -𝟙 ∘ i
  -i≡-𝟙◎i = begin
    ω ^ 6         ≈⟨ sym-assoc ⟩
    i ∘ ω ^ 4     ≈⟨ (refl⟩∘⟨ sym-assoc) ⟩
    i ∘ i ∘ ω ^ 2 ≈⟨ sym-assoc ⟩
    i ^ 2 ∘ ω ^ 2 ∎

  -- short-names for important lemmas
  {-
  -- Before we can even get started, we need some postulates, as the
  -- proofs are quite a lot of pain
  postulate
    uniti₊-coherence : add (M+.uniti⋆ {O}) ⟷₂ add (M+.uniti⋆ {O})
    unite₊-coherence : add (M+.uniti⋆ {O}) ⟷₂ add (M+.uniti⋆ {O})
    uniti⋆-coherence : mult (M×.uniti⋆ {I}) ⟷₂ mult (M×.uniti⋆ {I})
    unite⋆-coherence : mult (M×.uniti⋆ {I}) ⟷₂ mult (M×.uniti⋆ {I})
  -}
  -- Proposition 4.3
  -- (i)
  scalar-comm : {s t : Scalar} → s ∘ t ≈ t ∘ s
  scalar-comm {s} {t} = begin
    s ∘ t ≈⟨ {!!} ⟩
    t ∘ s ∎

  {-
  scalar-inverse : {s t : Scalar} → (s ∘ s ≈ t) → !⟷ s ⟷₂ !⟷ t ◎ s
  scalar-inverse {s} {t} p = {!!}
  -}
