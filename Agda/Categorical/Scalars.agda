{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
-- not --safe right now as we have holes

open import Categories.Category -- we need it all
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.RigCategory
open import Categorical.SqrtRig using (SqrtRig; module Kit)

-- Everything is over a SqrtRig
module Categorical.Scalars {o ℓ e} {C : Category o ℓ e} {M⊎ M× : Monoidal C} {S⊎ : Symmetric M⊎}
  {S× : Symmetric M×} {R : RigCategory C S⊎ S×} (SR : SqrtRig R) where

  open import Level using (Level)

  open import Categories.Category.Monoidal.Properties using (module Kelly's)
  import Categories.Morphism.Reasoning as MR

  open Category C -- all of it
  open HomReasoning
  open MR C
  open SqrtRig SR
  open Kit R
  
  private
    module M⊎ = Monoidal M⊎
    module M× = Monoidal M×
    module S⊎ = Symmetric S⊎
    module S× = Symmetric S×

  -- Define some of our constants.
  i -i -𝟙 : Scalar
  i  = ω ^ 2
  -𝟙 = ω ^ 4
  -i = ω ^ 6

  -- coherence of definitions (by associativity of ∘ )
  -- Lemma 4.4 (i)
  -𝟙²≡𝟙 : -𝟙 ^ 2 ≈ 𝟙
  -𝟙²≡𝟙 = begin
    (ω ^ 4) ∘ ω ^ 4                       ≈⟨ pullʳ (pullʳ assoc) ⟩
    ω ^ 8                                 ≈⟨ E1 ⟩
    𝟙                                     ∎

  i²≡-𝟙 : i ^ 2 ≈ -𝟙
  i²≡-𝟙 = assoc
  
  -i≡-𝟙◎i : -i ≈ -𝟙 ∘ i
  -i≡-𝟙◎i = begin
    ω ^ 6             ≈⟨ pushʳ (pushʳ sym-assoc) ⟩
    ω ^ 4 ∘ ω ^ 2 ∎

  -- short-names for important lemmas
  -- 1. the unitors are equal at the unit (follows from Kelly's Coherence thms)
  -- 2. infrastructure for 'commutative cubes'
  
  -- Proposition 4.3
  -- (i)
  scalar-comm : {s t : Scalar} → s ∘ t ≈ t ∘ s
  scalar-comm {s} {t} = begin
    s ∘ t ≈⟨ {!!} ⟩
    t ∘ s ∎

  {- as this isn't used much, skip it for now.
  scalar-inverse : {s t : Scalar} → (s ∘ s ≈ t) → !⟷ s ⟷₂ !⟷ t ◎ s
  scalar-inverse {s} {t} p = {!!}
  -}

  -- Proposition 4.3 (iv)
  𝟙●f≈f : {A B : Obj} (f : A ⇒ B ) → 𝟙 ● f ≈ f
  𝟙●f≈f f = begin
    λ⇒ ∘ 𝟙 ⊗₁ f ∘ λ⇐ ≈⟨ pullˡ M×.unitorˡ-commute-from ⟩
    (f ∘ λ⇒) ∘ λ⇐    ≈⟨ cancelʳ M×.unitorˡ.isoʳ ⟩
    f               ∎

  -- Proposition 4.3 (v)
  s●t≈s∘t : {s t : Scalar} → s ● t ≈ s ∘ t
  s●t≈s∘t {s} {t} = begin
    λ⇒ ∘ s ⊗₁ t ∘ λ⇐ ≡⟨ {!!} ⟩
    s ∘ t            ∎

  -- Proposition 4.3 (vi)
  ●-distrib-⊕ : {A B C D : Obj} {s : Scalar} {f : A ⇒ B} {g : C ⇒ D} →
    s ● (f ⊕₁ g) ≈ (s ● f) ⊕₁ (s ● g)
  ●-distrib-⊕ {s = s} {f} {g} = {!!}

  -- Proposition 4.3 (vii)
  ●-assocˡ : {A B C : Obj} {s : Scalar} {f : A ⇒ B} {g : B ⇒ C} →
    s ● (g ∘ f) ≈ (s ● g) ∘ f
  ●-assocˡ {s = s} {f} {g} = {!!}

  -- Proposition 4.3 (viii)
  ●-over-∘ : {A B C : Obj} {s : Scalar} {f : A ⇒ B} {g : B ⇒ C} →
     s ● (g ∘ f) ≈ g ∘ (s ● f)
  ●-over-∘ {s = s} {f} {g} = {!!}
