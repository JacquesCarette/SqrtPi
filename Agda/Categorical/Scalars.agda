{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
-- not --safe right now as we have holes

open import Categories.Category -- we need it all
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.RigCategory
open import Categorical.SqrtRig using (SqrtRig; module Kit)

-- Everything is over a SqrtRig
module Categorical.Scalars {o ℓ e} {𝒞 : Category o ℓ e} {M⊎ M× : Monoidal 𝒞} {S⊎ : Symmetric M⊎}
  {S× : Symmetric M×} {R : RigCategory 𝒞 S⊎ S×} (SR : SqrtRig R) where

  open import Data.Product using (_,_)
  open import Level using (Level)

  open import Categories.Category.Monoidal.Properties using (module Kelly's)
  import Categories.Category.Monoidal.Braided.Properties as BraidProp
  import Categories.Category.Monoidal.Reasoning as MonR
  import Categories.Morphism.Reasoning as MR
  
  open Category 𝒞 -- all of it
  open HomReasoning
  open MR 𝒞
  open SqrtRig SR
  open Kit R
  open MonR M× using (refl⟩⊗⟨_; _⟩⊗⟨refl; _⟩⊗⟨_; serialize₁₂)
  open MonR M⊎ using () renaming (_⟩⊗⟨_ to _⟩⊕⟨_)
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
    (ρ⇒ ∘ σ⇐) ∘ s ⊗₁ f ∘ (σ⇒ ∘ ρ⇐)  ≈⟨ sym-assoc ○ assoc ⟩∘⟨refl ⟩
    (ρ⇒ ∘ σ⇐ ∘ s ⊗₁ f) ∘ (σ⇒ ∘ ρ⇐) ≈⟨ (refl⟩∘⟨ S×.braiding.⇐.commute (f , s)) ⟩∘⟨refl ⟩
    (ρ⇒ ∘ f ⊗₁ s ∘ σ⇐) ∘ (σ⇒ ∘ ρ⇐)  ≈⟨ sym-assoc ○ assoc²' ⟩∘⟨refl ⟩
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
  inner-● : {A B : Obj} {s t : Scalar} {f : A ⇒ B} →
    s ⊗₁ (λ⇒ ∘ t ⊗₁ f ∘ λ⇐) ≈ λ⇒ ∘ s ⊗₁ (t ⊗₁ f) ∘ λ⇐
  inner-● {s = s} {t} {f} = begin
    s ⊗₁ (λ⇒ ∘ t ⊗₁ f ∘ λ⇐)                             ≈⟨ {!!} ⟩
    (λ⇒ ∘ (s ⊗₁ t) ∘ λ⇐) ⊗₁ (id ∘ f ∘ id)               ≈⟨ {!!} ⟩
    λ⇒ ⊗₁ id ∘ (s ⊗₁ t) ⊗₁ f ∘ λ⇐ ⊗₁ id                 ≈⟨ {!!} ⟩
    λ⇒ ⊗₁ id ∘ (α⇐ ∘ s ⊗₁ (t ⊗₁ f) ∘ α⇒) ∘ λ⇐ ⊗₁ id    ≈⟨ ? ⟩
    (λ⇒ ⊗₁ id ∘ α⇐) ∘ s ⊗₁ (t ⊗₁ f) ∘ (α⇒ ∘ λ⇐ ⊗₁ id)  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ coherence₁'' ⟩
    (λ⇒ ⊗₁ id ∘ α⇐) ∘ s ⊗₁ (t ⊗₁ f) ∘ λ⇐                ≈⟨ coherence₁' ⟩∘⟨refl ⟩
    λ⇒ ∘ s ⊗₁ (t ⊗₁ f) ∘ λ⇐ ∎

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

  hom⊗-3 : {A B : Obj} {s t : Scalar} {f : A ⇒ B} →
   λ⇒ ⊗₁ id ∘ (s ⊗₁ t) ⊗₁ f ∘ λ⇐ ⊗₁ id ≈ (s ● t) ⊗₁ f
  hom⊗-3 {s = s} {t} {f} = begin
    λ⇒ ⊗₁ id ∘ (s ⊗₁ t) ⊗₁ f ∘ λ⇐ ⊗₁ id    ≈˘⟨ refl⟩∘⟨ M×.⊗.homomorphism ⟩
    λ⇒ ⊗₁ id ∘ ((s ⊗₁ t) ∘ λ⇐) ⊗₁ (f ∘ id) ≈˘⟨ M×.⊗.homomorphism ⟩
    (λ⇒ ∘ (s ⊗₁ t) ∘ λ⇐) ⊗₁ (id ∘ f ∘ id)   ≈⟨ refl⟩⊗⟨ (identityˡ ○ identityʳ) ⟩
    (λ⇒ ∘ s ⊗₁ t ∘ λ⇐) ⊗₁ f                 ∎
  
  push-scalar-left : {A B : Obj} {s t : Scalar} {f : A ⇒ B} →
    s ● (t ● f) ≈ (s ∘ t) ● f
  push-scalar-left {s = s} {t} {f} = begin
    λ⇒ ∘ s ⊗₁ (λ⇒ ∘ t ⊗₁ f ∘ λ⇐) ∘ λ⇐                 ≈⟨ refl⟩∘⟨ inner-● ⟩∘⟨refl ⟩
    λ⇒ ∘ (λ⇒ ∘ s ⊗₁ (t ⊗₁ f) ∘ λ⇐) ∘ λ⇐               ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ conjugate ⟩∘⟨refl)) ⟩∘⟨refl ⟩
    λ⇒ ∘ (λ⇒ ∘ (α⇒ ∘ (s ⊗₁ t) ⊗₁ f ∘ α⇐) ∘ λ⇐) ∘ λ⇐  ≈⟨ refl⟩∘⟨ (sym-assoc ⟩∘⟨refl ○ Equiv.sym assoc² ⟩∘⟨refl ⟩∘⟨refl ○ assoc ⟩∘⟨refl ○ assoc ⟩∘⟨refl ○ assoc²' {i = λ⇒ ∘ α⇒} {g = α⇐ ∘ λ⇐} {f = λ⇐} ) ⟩
    λ⇒ ∘ (λ⇒ ∘ α⇒) ∘ (s ⊗₁ t) ⊗₁ f ∘ (α⇐ ∘ λ⇐) ∘ λ⇐  ≈⟨ refl⟩∘⟨ Kelly's.coherence₁ M× ⟩∘⟨ refl⟩∘⟨ Kelly's.coherence-inv₁ M× ⟩∘⟨refl ⟩
    λ⇒ ∘ λ⇒ ⊗₁ id ∘ (s ⊗₁ t) ⊗₁ f ∘ λ⇐ ⊗₁ id ∘ λ⇐    ≈˘⟨ refl⟩∘⟨ assoc²' ⟩
    λ⇒ ∘ (λ⇒ ⊗₁ id ∘ (s ⊗₁ t) ⊗₁ f ∘ λ⇐ ⊗₁ id) ∘ λ⇐  ≈⟨ refl⟩∘⟨ hom⊗-3 ⟩∘⟨refl ⟩
    λ⇒ ∘ (λ⇒ ∘ s ⊗₁ t ∘ λ⇐) ⊗₁ f ∘ λ⇐                 ≈⟨ Equiv.refl ⟩
    λ⇒ ∘ (s ● t) ⊗₁ f ∘ λ⇐                             ≈⟨ refl⟩∘⟨ (scalar-●≈∘ ⟩⊗⟨refl) ⟩∘⟨refl ⟩
    λ⇒ ∘ (s ∘ t) ⊗₁ f ∘ λ⇐                             ∎

-- (a ∘ (b ∘ c)) ∘ d -> a ∘ b ∘ c ∘ d
  -- useful lemmas to get to PXP
  laplazaXXIII-rhs-inv : {A B : Obj} → (λ⇒ {X = A} ⊕₁ λ⇒ {X = B} ∘ δₗ⇒) ∘ δₗ⇐ ∘ λ⇐ ⊕₁ λ⇐ ≈ id
  laplazaXXIII-rhs-inv = begin
    (λ⇒ ⊕₁ λ⇒ ∘ δₗ⇒) ∘ δₗ⇐ ∘ λ⇐ ⊕₁ λ⇐ ≈⟨ cancelInner dl.isoʳ ⟩
    -- the next bit is quite polymorphic so hard to abstract out; later
    λ⇒ ⊕₁ λ⇒ ∘ λ⇐ ⊕₁ λ⇐     ≈˘⟨ M⊎.⊗.homomorphism ⟩
    (λ⇒ ∘ λ⇐) ⊕₁ (λ⇒ ∘ λ⇐)  ≈⟨ M×.unitorˡ.isoʳ ⟩⊕⟨ M×.unitorˡ.isoʳ ⟩
    id ⊕₁ id                 ≈⟨ M⊎.⊗.identity ⟩
    id                       ∎

  -- inverse laplazaXXIII
  laplazaXXIII⁻¹ : {A B : Obj} → λ⇐ {X = A ⊕₀ B} ≈ δₗ⇐ ∘ (λ⇐ ⊕₁ λ⇐)
  laplazaXXIII⁻¹ = begin
    λ⇐                                          ≈⟨ insertʳ laplazaXXIII-rhs-inv ⟩
    (λ⇐ ∘ (λ⇒ ⊕₁ λ⇒) ∘ δₗ⇒) ∘ δₗ⇐ ∘ (λ⇐ ⊕₁ λ⇐) ≈⟨ (refl⟩∘⟨ Equiv.sym laplazaXXIII) ⟩∘⟨refl ⟩
    (λ⇐ ∘ λ⇒) ∘  δₗ⇐ ∘ (λ⇐ ⊕₁ λ⇐)               ≈⟨ elimˡ M×.unitorˡ.isoˡ ⟩
    δₗ⇐ ∘ (λ⇐ ⊕₁ λ⇐)                            ∎
 
  -- (vi)
  -- used in PXP proof 
  ●-distrib-⊕ : {A B C D : Obj} {s : Scalar} {f : A ⇒ B} {g : C ⇒ D} →
    s ● (f ⊕₁ g) ≈ (s ● f) ⊕₁ (s ● g)
  ●-distrib-⊕ {s = s} {f} {g} = begin
    λ⇒ ∘ s ⊗₁ (f ⊕₁ g) ∘ λ⇐                                        ≈⟨ laplazaXXIII ⟩∘⟨ refl⟩∘⟨ laplazaXXIII⁻¹ ⟩
    ((λ⇒ ⊕₁ λ⇒) ∘ δₗ⇒) ∘  s ⊗₁ (f ⊕₁ g) ∘ (δₗ⇐ ∘ (λ⇐ ⊕₁ λ⇐))      ≈⟨ center dl-commute ⟩
    (λ⇒ ⊕₁ λ⇒) ∘  ((s ⊗₁ f) ⊕₁ (s ⊗₁ g) ∘ δₗ⇒) ∘ δₗ⇐ ∘ (λ⇐ ⊕₁ λ⇐) ≈⟨ refl⟩∘⟨ cancelInner dl.isoʳ ⟩
    (λ⇒ ⊕₁ λ⇒) ∘ (s ⊗₁ f) ⊕₁ (s ⊗₁ g) ∘ (λ⇐ ⊕₁ λ⇐)               ≈˘⟨ M⊎.⊗.homomorphism ○ refl⟩∘⟨ M⊎.⊗.homomorphism ⟩
    (λ⇒ ∘ s ⊗₁ f ∘ λ⇐) ⊕₁ (λ⇒ ∘ s ⊗₁ g ∘ λ⇐)                      ∎

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
  ●-assocʳ = Equiv.sym ●-assocˡ
  
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


