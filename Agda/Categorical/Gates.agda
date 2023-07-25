{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
-- add --safe when there are no more holes

open import Categories.Category -- we need it all
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.RigCategory

open import Categorical.SqrtRig

-- Everything is over a SqrtRig
module Categorical.Gates {o ℓ e} {C : Category o ℓ e}
  {M⊎ M× : Monoidal C} {S⊎ : Symmetric M⊎}
  {S× : Symmetric M×} {R : RigCategory C S⊎ S×} (SR : SqrtRig R) where

  open import Data.Product using (_,_)
  open import Level using (Level)

  open import Categories.Category.Monoidal.Interchange.Braided (Symmetric.braided S⊎) using (module swapInner)
  import Categories.Morphism.Reasoning as MR
  
  open import Categorical.Scalars SR

  open SqrtRig SR
  open MR C

  
  X : C [ 2C , 2C ]
  X = σ⊕

  P : Scalar → C [ 2C , 2C ]
  P s = id ⊕₁ s

  -- Note: S was already defined in SqrtRig as (essentially) P i
  Z T H : C [ 2C , 2C ]
  Z = P -𝟙
  T = P ω
  H = ω ● (X ∘ S ∘ V ∘ S ∘ X)

  -- note that this isn't quite what's in the paper, but it is equivalent
  Midswap : {A B C D : Obj} → (A ⊕₀ B) ⊕₀ (C ⊕₀ D) ⇒ (A ⊕₀ C) ⊕₀ (B ⊕₀ D)
  Midswap = swapInner.from

  Mat : {A : Obj} → 2C ⊗₀ A ⇒ A ⊕₀ A
  Mat = (λ⇒ ⊕₁ λ⇒) ∘ δᵣ⇒

  Mat⁻¹ : {A : Obj} → A ⊕₀ A ⇒ 2C ⊗₀ A
  Mat⁻¹ = δᵣ⇐ ∘ λ⇐ ⊕₁ λ⇐
  
  Ctrl : {A : Obj} (m : Endo A) → 2C ⊗₀ A ⇒ 2C ⊗₀ A
  Ctrl m = Mat⁻¹ ∘ (id ⊕₁ m) ∘ Mat

  nCtrl : {A : Obj} (m : Endo A) → 2C ⊗₀ A ⇒ 2C ⊗₀ A
  nCtrl m = Mat⁻¹ ∘ (m ⊕₁ id) ∘ Mat

  -- don't artificially restrict the types
  SWAP : {A B : Obj} → A ⊗₀ B ⇒ B ⊗₀ A
  SWAP = σ⊗
  
  CX CZ : 2C ⊗₀ 2C ⇒ 2C ⊗₀ 2C
  CX = Ctrl X
  CZ = Ctrl Z

  CCX : 2C ⊗₀ 2C ⊗₀ 2C ⇒ 2C ⊗₀ 2C ⊗₀ 2C
  CCX = Ctrl CX

  -- we could, at times, but more general:
  CX′ : {A : Obj} → 2C ⊗₀ (A ⊕₀ A) ⇒ 2C ⊗₀ (A ⊕₀ A)
  CX′ = Ctrl σ⊕

  P′ : {A B : Obj} → Endo B → C [ A ⊕₀ B , A ⊕₀ B ]
  P′ f = id ⊕₁ f
  
  ------------------------------------------------------------------------
  -- Some properties of the above that are implicitly used in the
  -- proofs of the properties (below).
  --
  -- Mat⁻¹ is an inverse to Mat (i.e. was defined to be so.
  Mat-invˡ : {A : Obj} → Mat⁻¹ {A} ∘ Mat ≈ id
  Mat-invˡ = begin
    (δᵣ⇐ ∘ λ⇐ ⊕₁ λ⇐) ∘ (λ⇒ ⊕₁ λ⇒) ∘ δᵣ⇒ ≈⟨ center (Equiv.sym S⊎.⊗.homomorphism ○
                                                     M×.unitorˡ.isoˡ ⟩⊕⟨ M×.unitorˡ.isoˡ)  ⟩
    δᵣ⇐ ∘ id ⊕₁ id ∘ δᵣ⇒                 ≈⟨ refl⟩∘⟨ elimˡ S⊎.⊗.identity ⟩
    δᵣ⇐ ∘ δᵣ⇒                             ≈⟨ dr.isoˡ ⟩
    id                                     ∎

  Mat-invʳ : {A : Obj} → Mat {A} ∘ Mat⁻¹ ≈ id
  Mat-invʳ = begin
    ((λ⇒ ⊕₁ λ⇒) ∘ δᵣ⇒) ∘ δᵣ⇐ ∘ λ⇐ ⊕₁ λ⇐ ≈⟨ center dr.isoʳ ⟩
    λ⇒ ⊕₁ λ⇒ ∘ id ∘ λ⇐ ⊕₁ λ⇐             ≈⟨ refl⟩∘⟨ identityˡ ⟩ 
    λ⇒ ⊕₁ λ⇒ ∘ λ⇐ ⊕₁ λ⇐                  ≈˘⟨ S⊎.⊗.homomorphism ⟩
    (λ⇒ ∘ λ⇐) ⊕₁ (λ⇒ ∘ λ⇐)               ≈⟨ (M×.unitorˡ.isoʳ ⟩⊕⟨ M×.unitorˡ.isoʳ) ○ S⊎.⊗.identity ⟩
    id                                     ∎
  
  ------------------------------------------------------------------------
  -- Properties of Gates (split?)

  -- Lemma lem:gates
  -- (ii)
  -- used in CX²≡id proof
  X²≡id : X ^ 2 ≈ id
  X²≡id = S⊎.commutative

  -- (iii)
  -- used in CZ²≡id proof
  P² : (s : Scalar) → (P s) ^ 2 ≈ P (s ^ 2)
  P² s = begin
    (id ⊕₁ s) ∘ (id ⊕₁ s) ≈˘⟨ S⊎.⊗.homomorphism ⟩
    (id ∘ id) ⊕₁ (s ∘ s)  ≈⟨ identity² ⟩⊕⟨refl ⟩
    id ⊕₁ s ^ 2           ∎

  -- (iv) Show P is invertible for invertible scalars instead of assuming
  P-inv : {s t : Scalar} → t ∘ s ≈ id → P t ∘ P s ≈ id
  P-inv {s = s} {t} ts≈id  = begin
    (id ⊕₁ t) ∘ (id ⊕₁ s) ≈˘⟨ S⊎.⊗.homomorphism ⟩
    (id ∘ id) ⊕₁ (t ∘ s)  ≈⟨ identity² ⟩⊕⟨ ts≈id ⟩
    id ⊕₁ id              ≈⟨ S⊎.⊗.identity ⟩
    id                    ∎

  -- (v)
  -- useful lemma for P-comm
  ⊗ʳ-comm : ∀ {A B} {f g : A ⇒ A} → f ∘ g ≈ g ∘ f → id {B} ⊕₁ f ∘ id ⊕₁ g ≈ id ⊕₁ g ∘ id ⊕₁ f
  ⊗ʳ-comm fg≡gf = ⟺ M⊎.⊗.homomorphism ○ refl⟩⊕⟨ fg≡gf ○ M⊎.⊗.homomorphism
  
  -- used in MatProp: Ctrl-comm (and thus CP-comm)
  P-comm : {s t : Scalar} → s ∘ t ≈ t ∘ s → P s ∘ P t ≈ P t ∘ P s
  P-comm st≡ts = ⊗ʳ-comm st≡ts

  -- (vi)
  PXP : (s : Scalar) → P s ∘ X ∘ P s ≈ s ● X
  PXP s = begin
    (id ⊕₁ s) ∘ X ∘ (id ⊕₁ s)  ≈⟨ refl⟩∘⟨ S⊎.braiding.⇒.commute (id , s) ⟩
    (id ⊕₁ s) ∘ (s ⊕₁ id) ∘ X  ≈⟨ pullˡ (Equiv.sym serialize₂₁-⊕)  ⟩
    (s ⊕₁ s) ∘ X               ≈˘⟨ identityʳ ⟩⊕⟨ identityʳ ⟩∘⟨refl ⟩
    ((s ∘ id) ⊕₁ (s ∘ id)) ∘ X ≈˘⟨ scalar-●≈∘ ⟩⊕⟨ scalar-●≈∘ ⟩∘⟨refl ⟩
    (s ● id ⊕₁ s ● id) ∘ X     ≈˘⟨ ●-distrib-⊕ ⟩∘⟨refl ⟩
    (s ● (id ⊕₁ id)) ∘ X       ≈⟨ ●-assocʳ ⟩
    s ● ((id ⊕₁ id) ∘ X)       ≈⟨ ●-congʳ (elimˡ S⊎.⊗.identity) ⟩
    s ● X                      ∎

  -- (vii)
  XV-comm : X ∘ V ≈ V ∘ X
  XV-comm = begin
    X ∘ V       ≈˘⟨ E2 ⟩∘⟨refl ⟩
    (V ∘ V) ∘ V ≈⟨ assoc ⟩
    V ∘ (V ∘ V) ≈⟨ refl⟩∘⟨ E2 ⟩
    V ∘ X       ∎

  -- lemma that makes (viii) and (ix) the same
  CA∘CB≡id : {o : Obj} {A B : Endo o} → A ∘ B ≈ id → Ctrl A ∘ Ctrl B ≈ id
  CA∘CB≡id {A = A} {B} AB≈id = begin
    (Mat⁻¹ ∘ (id ⊕₁ A) ∘ Mat) ∘ Mat⁻¹ ∘ (id ⊕₁ B) ∘ Mat   ≈⟨ sym-assoc ⟩∘⟨refl ⟩
    ((Mat⁻¹ ∘ (id ⊕₁ A)) ∘ Mat) ∘ Mat⁻¹ ∘ (id ⊕₁ B) ∘ Mat ≈⟨ cancelInner Mat-invʳ ⟩
    (Mat⁻¹ ∘ (id ⊕₁ A)) ∘ (id ⊕₁ B) ∘ Mat                 ≈⟨ center (Equiv.sym S⊎.⊗.homomorphism) ⟩
    Mat⁻¹ ∘ (id ∘ id) ⊕₁ (A ∘ B) ∘ Mat                    ≈⟨ refl⟩∘⟨ identity² ⟩⊕⟨ AB≈id ⟩∘⟨refl ⟩
    Mat⁻¹ ∘ id ⊕₁ id ∘ Mat                                ≈⟨ elim-center S⊎.⊗.identity ⟩
    Mat⁻¹ ∘ Mat                                            ≈⟨ Mat-invˡ ⟩
    id                                                     ∎
    
  -- (viii)
  -- useful on its own, but also in CCX²≡id
  CX²≡id : CX ^ 2 ≈ id
  CX²≡id = CA∘CB≡id X²≡id

  -- First need that Z²≡id (for CZ²≡id)
  Z²≡id : Z ^ 2 ≈ id
  Z²≡id = begin
    P (ω ^ 4) ∘ P (ω ^ 4) ≈⟨ P² (ω ^ 4) ⟩
    P ((ω ^ 4) ^ 2)       ≈⟨ refl⟩⊕⟨ -𝟙²≡𝟙 ⟩
    P 𝟙                   ≈⟨ S⊎.⊗.identity ⟩
    id                    ∎
  
  -- (ix)
  CZ²≡id : CZ ^ 2 ≈ id
  CZ²≡id = CA∘CB≡id Z²≡id

  -- (x)
  CCX²≡id : CCX ^ 2 ≈ id
  CCX²≡id = CA∘CB≡id CX²≡id

  -- (xi)
  XPs : {s t : Scalar} → s ∘ t ≈ id → X ∘ P s ≈ s ● (P t ∘ X)
  XPs {s = s} {t} st≈id = begin
    σ⊕ ∘ (id ⊕₁ s)          ≈⟨ S⊎.braiding.⇒.commute (id , s) ⟩
    (s ⊕₁ id) ∘ X           ≈˘⟨ identityʳ ⟩⊕⟨ st≈id ⟩∘⟨refl ⟩
    (s ∘ id) ⊕₁ (s ∘ t) ∘ X ≈˘⟨ scalar-●≈∘ ⟩⊕⟨ scalar-●≈∘ ⟩∘⟨refl ⟩
    (s ● id) ⊕₁ (s ● t) ∘ X ≈˘⟨ ●-distrib-⊕ ⟩∘⟨refl ⟩
    s ● (id ⊕₁ t) ∘ X       ≈⟨ ●-assocʳ ⟩
    s ● ((id ⊕₁ t) ∘ X)     ∎

  -- the proofs call this (xi) as well...
  PX : {s t : Scalar} → s ∘ t ≈ id → P s ∘ X ≈ s ● (X ∘ P t)
  PX {s = s} {t} st≈id = begin
    (id ⊕₁ s) ∘ σ⊕            ≈˘⟨ st≈id ⟩⊕⟨ identityʳ ⟩∘⟨refl ⟩
    ((s ∘ t) ⊕₁ (s ∘ id)) ∘ X ≈˘⟨ (scalar-●≈∘ ⟩⊕⟨ scalar-●≈∘) ⟩∘⟨refl ⟩
    ((s ● t) ⊕₁ (s ● id)) ∘ X ≈˘⟨ ●-distrib-⊕ ⟩∘⟨refl ⟩
    s ● (t ⊕₁ id) ∘ X         ≈⟨ ●-assocʳ ⟩
    s ● ((t ⊕₁ id) ∘ X)       ≈˘⟨ ●-congʳ (S⊎.braiding.⇒.commute (id , t)) ⟩
    s ● (X ∘ P t)             ∎
    
  -----------------------------------------------------------------------------
  -- Corrolaries that are used in the proofs "inline"
  cong-P : {s t : Scalar} → (s ≈ t) → P s ≈ P t
  cong-P = refl⟩⊕⟨_
  
  S²≡Z : S ∘ S ≈ Z
  S²≡Z = begin
    P i ∘ P i ≈⟨ P² i ⟩
    P (i ^ 2) ≈⟨ cong-P i²≡-𝟙 ⟩
    P -𝟙      ∎

  P∘P : {s t u : Scalar} → s ∘ t ≈ u → P s ∘ P t ≈ P u
  P∘P st≈u = ⟺ S⊎.⊗.homomorphism ○ identity² ⟩⊕⟨ st≈u

  ------------------------------------------------------------------------------
  -- Even more general stuff that should be pulled out
  bottom-cancel : {A B C : Obj} {f : A ⇒ B} {g : B ⇒ A} → f ∘ g ≈ id →
    id {C} ⊗₁ f ∘ id ⊗₁ g ≈ id
  bottom-cancel {f = f} {g} fg≈id = begin
    id ⊗₁ f ∘ id ⊗₁ g    ≈˘⟨ M×.⊗.homomorphism ⟩
    (id ∘ id) ⊗₁ (f ∘ g) ≈⟨ identity² ⟩⊗⟨ fg≈id ⟩
    id ⊗₁ id             ≈⟨ M×.⊗.identity ⟩
    id                   ∎

  top-cancel : {A B C : Obj} {f : A ⇒ B} {g : B ⇒ A} → f ∘ g ≈ id →
    f ⊗₁ id {C} ∘ g ⊗₁ id ≈ id
  top-cancel {f = f} {g} fg≈id = begin
    f ⊗₁ id ∘ g ⊗₁ id    ≈˘⟨ M×.⊗.homomorphism ⟩
    (f ∘ g) ⊗₁ (id ∘ id) ≈⟨ fg≈id ⟩⊗⟨ identity² ⟩
    id ⊗₁ id             ≈⟨ M×.⊗.identity ⟩
    id                   ∎

  VXV≡id : (V ∘ X) ∘ V ≈ id
  VXV≡id = begin
    (V ∘ X) ∘ V ≈˘⟨ XV-comm ⟩∘⟨refl ⟩
    (X ∘ V) ∘ V ≈⟨ pullʳ E2 ⟩
    X ∘ X       ≈⟨ X²≡id ⟩
    id          ∎

  VVX≡id : V ∘ V ∘ X ≈ id
  VVX≡id = pullˡ E2 ○ X²≡id
