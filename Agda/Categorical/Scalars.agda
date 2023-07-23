{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
-- not --safe right now as we have holes

open import Categories.Category -- we need it all
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.RigCategory
open import Categorical.SqrtRig using (SqrtRig)

-- Everything is over a SqrtRig
module Categorical.Scalars {o ℓ e} {𝒞 : Category o ℓ e} {M⊎ M× : Monoidal 𝒞} {S⊎ : Symmetric M⊎}
  {S× : Symmetric M×} {R : RigCategory 𝒞 S⊎ S×} (SR : SqrtRig R) where

  open import Data.Nat using (ℕ; zero; suc; _+_)
  open import Data.Product using (_,_)

  -- the following are only used in this file, so don't factor out
  import Categories.Category.Monoidal.Braided.Properties as BraidProp
  
  import Categories.Morphism.Reasoning as MR
  
  open MR 𝒞
  open SqrtRig SR
  open BraidProp S×.braided using (module Shorthands; braiding-coherence-inv; inv-braiding-coherence)

  -- Define some of our constants.
  i -i -𝟙 : Scalar
  i  = ω ^ 2
  -𝟙 = ω ^ 4
  -i = ω ^ 6

  -- coherence of definitions (by associativity of ∘ )
  -- Lemma 4.4 (i)
  -- used in CZ²≡id 
  -𝟙²≡𝟙 : -𝟙 ^ 2 ≈ 𝟙
  -𝟙²≡𝟙 = begin
    (ω ^ 4) ∘ ω ^ 4  ≈⟨ pullʳ (pullʳ assoc) ⟩
    ω ^ 8            ≈⟨ E1 ⟩
    𝟙                ∎

  i²≡-𝟙 : i ^ 2 ≈ -𝟙
  i²≡-𝟙 = assoc
  
  -i≡-𝟙◎i : -i ≈ -𝟙 ∘ i
  -i≡-𝟙◎i = begin
    ω ^ 6             ≈⟨ pushʳ (pushʳ sym-assoc) ⟩
    ω ^ 4 ∘ ω ^ 2 ∎

  -i≡i◎-𝟙 : -i ≈ i ∘ -𝟙
  -i≡i◎-𝟙 = sym-assoc

  -i◎i≡𝟙 : -i ∘ i ≈ 𝟙
  -i◎i≡𝟙 = begin
    ω ^ 6 ∘ ω ^ 2 ≈⟨ ^-add ω 6 2 ⟩
    ω ^ 8         ≈⟨ E1 ⟩
    𝟙             ∎

  i⁴≡𝟙 : i ^ 4 ≈ 𝟙
  i⁴≡𝟙 = begin
    i ∘ i ∘ i ∘ i     ≈⟨ sym-assoc ⟩
    (i ∘ i) ∘ (i ∘ i) ≈⟨ i²≡-𝟙 ⟩∘⟨ i²≡-𝟙 ⟩
    -𝟙 ∘ -𝟙           ≈⟨ -𝟙²≡𝟙 ⟩
    𝟙                 ∎

  ω⁸⁺ᵃ≡ωᵃ : {a : ℕ} → ω ^ (8 + a) ≈ ω ^ a
  ω⁸⁺ᵃ≡ωᵃ {a} = begin
    ω ^ (8 + a)   ≈˘⟨ ^-add ω 8 a ⟩
    ω ^ 8 ∘ ω ^ a ≈⟨ E1 ⟩∘⟨refl ○ identityˡ ⟩
    ω ^ a         ∎
  
  -- short-names for important lemmas
  -- 1. the unitors are equal at the unit (follows from Kelly's Coherence thms)
  -- 2. infrastructure for 'commutative cubes'
  
  -- Proposition prop:scalars
  -- (i)
  {- Guess: not needed
  scalar-comm : {s t : Scalar} → s ∘ t ≈ t ∘ s
  scalar-comm {s} {t} = begin
    s ∘ t ≈⟨ {!!} ⟩
    t ∘ s ∎
  -}
  -- (ii)
  {- guess: not needed
  scalar-inverse : {s t : Scalar} → (s ∘ s ≈ t) → inv s ≈ inv t ∘ s
  scalar-inverse {s} {t} p = {!!}
  -}
  -- (iii) (used in C1)
  -- we don't define a right-handed ● so expand out its definition here
  -- depends crucially on braiding behind coherent.
  -- TODO: clean up the proof by using more combinators
  left-right-● : {A B : Obj} {s : Scalar} {f : A ⇒ B} → s ● f ≈ ρ⇒ ∘ f ⊗₁ s ∘ ρ⇐
  left-right-● {s = s} {f} = begin
    λ⇒ ∘ s ⊗₁ f ∘ λ⇐                ≈˘⟨ inv-braiding-coherence ⟩∘⟨ refl⟩∘⟨ ⟺ (switch-tofromˡ σ braiding-coherence-inv) ⟩
    (ρ⇒ ∘ σ⇐) ∘ s ⊗₁ f ∘ (σ⇒ ∘ ρ⇐)  ≈⟨ pullˡ assoc ⟩
    (ρ⇒ ∘ σ⇐ ∘ s ⊗₁ f) ∘ (σ⇒ ∘ ρ⇐) ≈⟨ (refl⟩∘⟨ S×.braiding.⇐.commute (f , s)) ⟩∘⟨refl ⟩
    (ρ⇒ ∘ f ⊗₁ s ∘ σ⇐) ∘ (σ⇒ ∘ ρ⇐)  ≈⟨ pullˡ assoc²' ⟩
    (ρ⇒ ∘ f ⊗₁ s ∘ σ⇐ ∘ σ⇒) ∘ ρ⇐    ≈⟨ (refl⟩∘⟨ elimʳ (S×.braiding.iso.isoˡ _)) ⟩∘⟨refl ⟩
    (ρ⇒ ∘ f ⊗₁ s) ∘ ρ⇐               ≈⟨ assoc ⟩
    ρ⇒ ∘ f ⊗₁ s ∘ ρ⇐                 ∎
    where open Shorthands
  
  -- (iv)
  𝟙●f≈f : {A B : Obj} (f : A ⇒ B ) → 𝟙 ● f ≈ f
  𝟙●f≈f f = begin
    λ⇒ ∘ 𝟙 ⊗₁ f ∘ λ⇐ ≈⟨ pullˡ M×.unitorˡ-commute-from ⟩
    (f ∘ λ⇒) ∘ λ⇐    ≈⟨ cancelʳ M×.unitorˡ.isoʳ ⟩
    f               ∎

  -- lemma for push-scalar-left
  coherence₁' : {A B : Obj} → λ⇒ ⊗₁ id ∘ α⇐ ≈ λ⇒ {A ⊗₀ B}
  coherence₁' = begin
    λ⇒ ⊗₁ id ∘ α⇐ ≈˘⟨ Kelly's.coherence₁ M× ⟩∘⟨refl ⟩
    (λ⇒ ∘ α⇒) ∘ α⇐ ≈⟨ cancelʳ M×.associator.isoʳ ⟩
    λ⇒             ∎

  coherence₁'' : {A B : Obj} → α⇒ {1C} {A} {B} ∘ λ⇐ ⊗₁ id ≈ λ⇐
  coherence₁'' = begin
    α⇒ ∘ λ⇐ ⊗₁ id  ≈˘⟨ refl⟩∘⟨ Kelly's.coherence-inv₁ M× ⟩
    α⇒ ∘ (α⇐ ∘ λ⇐) ≈⟨ cancelˡ M×.associator.isoʳ ⟩
    λ⇐             ∎
    
  -- (v)
  conjugate : {A B : Obj} {s t : Scalar} {f : A ⇒ B} → s ⊗₁ (t ⊗₁ f) ≈ α⇒ ∘ (s ⊗₁ t) ⊗₁ f ∘ α⇐
  conjugate {s = s} {t} {f} = begin
    s ⊗₁ (t ⊗₁ f)             ≈⟨ insertʳ M×.associator.isoʳ ⟩
    (s ⊗₁ (t ⊗₁ f) ∘ α⇒) ∘ α⇐ ≈⟨ pushˡ (Equiv.sym M×.assoc-commute-from) ⟩
    α⇒ ∘ (s ⊗₁ t) ⊗₁ f ∘ α⇐   ∎

  -- used in PXP proof and in push-scalar-left
  scalar-●≈∘ : {s t : Scalar} → s ● t ≈ s ∘ t
  scalar-●≈∘ {s = s} {t} = begin
    λ⇒ ∘ (s ⊗₁ t) ∘ λ⇐             ≈⟨ Kelly's.coherence₃ M× ⟩∘⟨refl ⟩
    ρ⇒ ∘ (s ⊗₁ t) ∘ λ⇐             ≈⟨ refl⟩∘⟨ serialize₁₂ ⟩∘⟨refl ⟩
    ρ⇒ ∘ (s ⊗₁ id ∘ id ⊗₁ t) ∘ λ⇐  ≈⟨ assoc²'' ⟩
    (ρ⇒ ∘ s ⊗₁ id) ∘ id ⊗₁ t ∘ λ⇐  ≈⟨ M×.unitorʳ-commute-from ⟩∘⟨refl ⟩
    (s ∘ ρ⇒) ∘ id ⊗₁ t ∘ λ⇐        ≈˘⟨ refl⟩∘⟨ M×.unitorˡ-commute-to ⟩
    (s ∘ ρ⇒) ∘ λ⇐ ∘ t               ≈˘⟨ (refl⟩∘⟨ Kelly's.coherence₃ M×) ⟩∘⟨refl ⟩ 
    (s ∘ λ⇒) ∘ λ⇐ ∘ t               ≈⟨ cancelInner M×.unitorˡ.isoʳ ⟩
    s ∘ t                            ∎

  hom∘²⊗³ : {A B C D E F G H I : Obj} {f₁ : A ⇒ B} {g₁ : D ⇒ E} {h₁ : G ⇒ H}
    {f₂ : B ⇒ C} {g₂ : E ⇒ F} {h₂ : H ⇒ I} →
     (h₂ ∘ h₁) ⊗₁ (g₂ ∘ g₁) ⊗₁ (f₂ ∘ f₁) ≈ (h₂ ⊗₁ g₂ ⊗₁ f₂) ∘ (h₁ ⊗₁ g₁ ⊗₁ f₁)
  hom∘²⊗³ = refl⟩⊗⟨ M×.⊗.homomorphism ○ M×.⊗.homomorphism

  hom∘³⊗² : {A B C D E F G H : Obj} {f₁ : A ⇒ B} {g₁ : B ⇒ C} {h₁ : C ⇒ D}
    {f₂ : E ⇒ F} {g₂ : F ⇒ G} {h₂ : G ⇒ H} →
     (h₂ ∘ g₂ ∘ f₂) ⊗₁ (h₁ ∘ g₁ ∘ f₁) ≈ (h₂ ⊗₁ h₁) ∘ (g₂ ⊗₁ g₁) ∘ (f₂ ⊗₁ f₁)
  hom∘³⊗² = M×.⊗.homomorphism ○ refl⟩∘⟨ M×.⊗.homomorphism
  
  insert-mid⊗ˡ : {A B C D E F : Obj} {f₁ : A ⇒ B} {g₁ : B ⇒ C} {h₁ : C ⇒ D}
    {g₂ : E ⇒ F} →
    g₂ ⊗₁ (h₁ ∘ g₁ ∘ f₁) ≈ (id ⊗₁ h₁) ∘ (g₂ ⊗₁ g₁) ∘ (id ⊗₁ f₁)
  insert-mid⊗ˡ = ⟺ (identityˡ ○ identityʳ) ⟩⊗⟨refl ○ hom∘³⊗²

  insert-mid⊗ʳ : {A B C D E F : Obj} {f₁ : A ⇒ B} {g₁ : B ⇒ C} {h₁ : C ⇒ D}
    {g₂ : E ⇒ F} →
    (h₁ ∘ g₁ ∘ f₁) ⊗₁ g₂ ≈ (h₁ ⊗₁ id) ∘ (g₁ ⊗₁ g₂) ∘ (f₁ ⊗₁ id)
  insert-mid⊗ʳ = refl⟩⊗⟨ ⟺ (identityˡ ○ identityʳ) ○ hom∘³⊗²
  
  push-scalar-left : {A B : Obj} {s t : Scalar} {f : A ⇒ B} →
    s ● (t ● f) ≈ (s ∘ t) ● f
  push-scalar-left {s = s} {t} {f} = begin
    λ⇒ ∘ s ⊗₁ (λ⇒ ∘ t ⊗₁ f ∘ λ⇐) ∘ λ⇐                 ≈⟨ refl⟩∘⟨ insert-mid⊗ˡ ⟩∘⟨refl ⟩
    λ⇒ ∘ ((id ⊗₁ λ⇒) ∘ s ⊗₁ (t ⊗₁ f) ∘ (id ⊗₁ λ⇐)) ∘ λ⇐ ≈⟨ refl⟩∘⟨ (unitor-coherenceˡ M× ⟩∘⟨ Equiv.refl ⟩∘⟨ ⟺ (cancel-toʳ M×.unitorˡ M×.unitorˡ-commute-to)) ⟩∘⟨refl ⟩
    λ⇒ ∘ (λ⇒ ∘ s ⊗₁ (t ⊗₁ f) ∘ λ⇐) ∘ λ⇐               ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ conjugate ⟩∘⟨refl)) ⟩∘⟨refl ⟩
    λ⇒ ∘ (λ⇒ ∘ (α⇒ ∘ (s ⊗₁ t) ⊗₁ f ∘ α⇐) ∘ λ⇐) ∘ λ⇐  ≈⟨ refl⟩∘⟨ (sym-assoc ⟩∘⟨refl ○ Equiv.sym assoc² ⟩∘⟨refl ⟩∘⟨refl ○ assoc ⟩∘⟨refl ○ assoc ⟩∘⟨refl ○ assoc²' {i = λ⇒ ∘ α⇒} {g = α⇐ ∘ λ⇐} {f = λ⇐} ) ⟩
    λ⇒ ∘ (λ⇒ ∘ α⇒) ∘ (s ⊗₁ t) ⊗₁ f ∘ (α⇐ ∘ λ⇐) ∘ λ⇐  ≈⟨ refl⟩∘⟨ Kelly's.coherence₁ M× ⟩∘⟨ refl⟩∘⟨ Kelly's.coherence-inv₁ M× ⟩∘⟨refl ⟩
    λ⇒ ∘ λ⇒ ⊗₁ id ∘ (s ⊗₁ t) ⊗₁ f ∘ λ⇐ ⊗₁ id ∘ λ⇐    ≈˘⟨ refl⟩∘⟨ assoc²' ⟩
    λ⇒ ∘ (λ⇒ ⊗₁ id ∘ (s ⊗₁ t) ⊗₁ f ∘ λ⇐ ⊗₁ id) ∘ λ⇐  ≈˘⟨ refl⟩∘⟨ insert-mid⊗ʳ ⟩∘⟨refl ⟩
    λ⇒ ∘ (λ⇒ ∘ s ⊗₁ t ∘ λ⇐) ⊗₁ f ∘ λ⇐                 ≡⟨⟩
    λ⇒ ∘ (s ● t) ⊗₁ f ∘ λ⇐                             ≈⟨ refl⟩∘⟨ (scalar-●≈∘ ⟩⊗⟨refl) ⟩∘⟨refl ⟩
    λ⇒ ∘ (s ∘ t) ⊗₁ f ∘ λ⇐                             ∎

  -- (a ∘ (b ∘ c)) ∘ d -> a ∘ b ∘ c ∘ d
  -- useful lemmas to get to PXP
  laplazaXXIII-rhs-inv : {A B : Obj} → (λ⇒ {X = A} ⊕₁ λ⇒ {X = B} ∘ δₗ⇒) ∘ δₗ⇐ ∘ λ⇐ ⊕₁ λ⇐ ≈ id
  laplazaXXIII-rhs-inv = begin
    (λ⇒ ⊕₁ λ⇒ ∘ δₗ⇒) ∘ δₗ⇐ ∘ λ⇐ ⊕₁ λ⇐ ≈⟨ cancelInner dl.isoʳ ⟩
    λ⇒ ⊕₁ λ⇒ ∘ λ⇐ ⊕₁ λ⇐              ≈˘⟨ M⊎.⊗.homomorphism ⟩
    (λ⇒ ∘ λ⇐) ⊕₁ (λ⇒ ∘ λ⇐)           ≈⟨ M×.unitorˡ.isoʳ ⟩⊕⟨ M×.unitorˡ.isoʳ ⟩
    id ⊕₁ id                          ≈⟨ M⊎.⊗.identity ⟩
    id                                ∎

  -- inverse laplazaXXIII
  laplazaXXIII⁻¹ : {A B : Obj} → λ⇐ {X = A ⊕₀ B} ≈ δₗ⇐ ∘ (λ⇐ ⊕₁ λ⇐)
  laplazaXXIII⁻¹ = begin
    λ⇐                                          ≈⟨ insertʳ laplazaXXIII-rhs-inv ⟩
    (λ⇐ ∘ (λ⇒ ⊕₁ λ⇒) ∘ δₗ⇒) ∘ δₗ⇐ ∘ (λ⇐ ⊕₁ λ⇐) ≈˘⟨ (refl⟩∘⟨ laplazaXXIII) ⟩∘⟨refl ⟩
    (λ⇐ ∘ λ⇒) ∘  δₗ⇐ ∘ (λ⇐ ⊕₁ λ⇐)               ≈⟨ elimˡ M×.unitorˡ.isoˡ ⟩
    δₗ⇐ ∘ (λ⇐ ⊕₁ λ⇐)                            ∎
 
  -- (vi)
  -- used in PXP proof 
  ●-distrib-⊕ : {A B C D : Obj} {s : Scalar} {f : A ⇒ B} {g : C ⇒ D} →
    s ● (f ⊕₁ g) ≈ (s ● f) ⊕₁ (s ● g)
  ●-distrib-⊕ {s = s} {f} {g} = begin
    λ⇒ ∘ s ⊗₁ (f ⊕₁ g) ∘ λ⇐                                       ≈⟨ laplazaXXIII ⟩∘⟨ refl⟩∘⟨ laplazaXXIII⁻¹ ⟩
    ((λ⇒ ⊕₁ λ⇒) ∘ δₗ⇒) ∘  s ⊗₁ (f ⊕₁ g) ∘ (δₗ⇐ ∘ (λ⇐ ⊕₁ λ⇐))     ≈⟨ center dl-commute ⟩
    (λ⇒ ⊕₁ λ⇒) ∘ ((s ⊗₁ f) ⊕₁ (s ⊗₁ g) ∘ δₗ⇒) ∘ δₗ⇐ ∘ (λ⇐ ⊕₁ λ⇐) ≈⟨ refl⟩∘⟨ cancelInner dl.isoʳ ⟩
    (λ⇒ ⊕₁ λ⇒) ∘ (s ⊗₁ f) ⊕₁ (s ⊗₁ g) ∘ (λ⇐ ⊕₁ λ⇐)              ≈˘⟨ M⊎.⊗.homomorphism ○ refl⟩∘⟨ M⊎.⊗.homomorphism ⟩
    (λ⇒ ∘ s ⊗₁ f ∘ λ⇐) ⊕₁ (λ⇒ ∘ s ⊗₁ g ∘ λ⇐)                     ∎

  -- (vii)
  -- used in PXP proof
  ●-assocˡ : {A B C : Obj} {s : Scalar} {f : A ⇒ B} {g : B ⇒ C} →
    s ● (g ∘ f) ≈ (s ● g) ∘ f
  ●-assocˡ {s = s} {f} {g} = begin
     λ⇒ ∘ s ⊗₁ (g ∘ f) ∘ λ⇐           ≈˘⟨ refl⟩∘⟨ identityʳ ⟩⊗⟨refl ⟩∘⟨refl ⟩
     λ⇒ ∘ ((s ∘ id) ⊗₁ (g ∘ f)) ∘ λ⇐  ≈⟨ refl⟩∘⟨ M×.⊗.homomorphism ⟩∘⟨refl ⟩
     λ⇒ ∘ ((s ⊗₁ g) ∘ (id ⊗₁ f)) ∘ λ⇐ ≈⟨ refl⟩∘⟨ pullʳ (⟺ M×.unitorˡ-commute-to) ⟩
     λ⇒ ∘ s ⊗₁ g ∘ λ⇐ ∘ f             ≈⟨ pushʳ sym-assoc ⟩
     (λ⇒ ∘ s ⊗₁ g ∘ λ⇐) ∘ f            ∎

  -- often we want the symmetric version
  ●-assocʳ : {A B C : Obj} {s : Scalar} {f : A ⇒ B} {g : B ⇒ C} →
    (s ● g) ∘ f ≈ s ● (g ∘ f)
  ●-assocʳ = ⟺ ●-assocˡ
  
  -- (viii)
  ●-over-∘ : {A B C : Obj} {s : Scalar} {f : A ⇒ B} {g : B ⇒ C} →
     s ● (g ∘ f) ≈ g ∘ (s ● f)
  ●-over-∘ {s = s} {f} {g} = begin
     λ⇒ ∘ s ⊗₁ (g ∘ f) ∘ λ⇐           ≈˘⟨ refl⟩∘⟨ identityˡ ⟩⊗⟨refl ⟩∘⟨refl ⟩
     λ⇒ ∘ ((id ∘ s) ⊗₁ (g ∘ f)) ∘ λ⇐  ≈⟨ refl⟩∘⟨ M×.⊗.homomorphism ⟩∘⟨refl ⟩
     λ⇒ ∘ ((id ⊗₁ g) ∘ (s ⊗₁ f)) ∘ λ⇐ ≈⟨ assoc²'' ⟩
     (λ⇒ ∘ id ⊗₁ g) ∘ s ⊗₁ f ∘ λ⇐     ≈⟨ M×.unitorˡ-commute-from ⟩∘⟨refl ⟩
     (g ∘ λ⇒) ∘ s ⊗₁ f ∘ λ⇐           ≈⟨ assoc ⟩
     g ∘ λ⇒ ∘ s ⊗₁ f ∘ λ⇐   ∎ 


  -----------------------------
  -- extra lemmas that are implicitly assumed currently
  ●-cong : {A B : Obj} {s t : Scalar} {f g : A ⇒ B} → s ≈ t → f ≈ g →
    s ● f ≈ t ● g
  ●-cong s≈t f≈g = refl⟩∘⟨ s≈t ⟩⊗⟨ f≈g ⟩∘⟨refl

  -- used in PXP proof
  ●-congʳ : {A B : Obj} {s : Scalar} {f g : A ⇒ B} → f ≈ g →
    s ● f ≈ s ● g
  ●-congʳ f≈g = ●-cong Equiv.refl f≈g

  ●-congˡ : {A B : Obj} {s t : Scalar} {f : A ⇒ B} → s ≈ t →
    s ● f ≈ t ● f
  ●-congˡ s≈t = ●-cong s≈t Equiv.refl

  ---------------------------------
  -- this should have been pulled out as well
  ⊕-to-●id : {s : Scalar} → s ⊕₁ s ≈ s ● id
  ⊕-to-●id {s = s} = begin
    s ⊕₁ s               ≈˘⟨ identityʳ ⟩⊕⟨ identityʳ ⟩
    (s ∘ id) ⊕₁ (s ∘ id) ≈˘⟨ scalar-●≈∘ ⟩⊕⟨ scalar-●≈∘ ⟩
    (s ● id) ⊕₁ (s ● id) ≈˘⟨ ●-distrib-⊕ ⟩
    s ● (id ⊕₁ id)       ≈⟨ ●-congʳ M⊎.⊗.identity ⟩
    s ● id ∎

  merge-scalars : {s t : Scalar} {A B C : Obj} {g : A ⇒ B} {f : B ⇒ C} →
    (s ● f) ∘ (t ● g) ≈ (s ∘ t) ● (f ∘ g)
  merge-scalars {s = s} {t} {g = g} {f} = begin
    (s ● f) ∘ (t ● g) ≈˘⟨ ●-assocˡ ⟩
    s ● (f ∘ (t ● g)) ≈˘⟨ ●-congʳ ●-over-∘ ⟩
    s ● (t ● (f ∘ g)) ≈⟨ push-scalar-left ⟩
    (s ∘ t) ● (f ∘ g) ∎

  extract-scalar2 : {s t : Scalar} {B C D : Obj} {g : B ⇒ C} {h : C ⇒ D} →
    s ● (h ∘ (t ● g)) ≈ (s ∘ t) ● (h ∘ g)
  extract-scalar2 {s = s} {t} {g = g} {h} = begin
    s ● (h ∘ (t ● g))   ≈˘⟨ ●-congʳ ●-over-∘ ⟩
    s ● (t ● (h ∘ g))   ≈⟨ push-scalar-left ⟩
    (s ∘ t) ● (h ∘ g)   ∎
    
  extract-scalar3 : {s t : Scalar} {A B C D : Obj} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} →
    s ● (h ∘ (t ● g) ∘ f) ≈ (s ∘ t) ● (h ∘ g ∘ f)
  extract-scalar3 {s = s} {t} {f = f} {g} {h} = begin
    s ● (h ∘ (t ● g) ∘ f)   ≈⟨ ●-congʳ (pullˡ (⟺ ●-over-∘) ) ⟩
    s ● (t ● (h ∘ g) ∘ f)   ≈⟨ ●-congʳ ●-assocʳ ⟩
    s ● (t ● ((h ∘ g) ∘ f)) ≈⟨ ●-congʳ (●-congʳ assoc) ⟩
    s ● (t ● (h ∘ g ∘ f))   ≈⟨ push-scalar-left ⟩
    (s ∘ t) ● (h ∘ g ∘ f)   ∎
