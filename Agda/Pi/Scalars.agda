{-# OPTIONS --without-K --exact-split #-}
-- not --safe right now, as we use postulates because some of the proofs
-- are rather larger, and will be back-filled.

module Pi.Scalars where

open import Data.Nat using (ℕ; zero; suc)

open import Pi.Types
open import Pi.Language
open import Pi.Equivalences
open import Pi.TermReasoning

-- To make things shorter, define an abbreviation for 1
𝟙 : I ⟷ I
𝟙 = id⟷

-- We need an operator for powering of scalars
infixr 30 _^_
_^_ : (I ⟷ I) → ℕ → (I ⟷ I)
s ^ zero = 𝟙
s ^ (suc zero) = s -- special case to make reasoning less painful
s ^ suc (suc n) = s ◎ s ^ (suc n)

-- Define some of our constants.
i -i -𝟙 : I ⟷ I
i  = ω ^ 2
-𝟙 = i ^ 2
-i = ω ^ 6

-- coherence; associativity of ◎
-i≡-𝟙◎i : -i ⟷₂ -𝟙 ◎ i
-i≡-𝟙◎i = begin
  ω ^ 6         ≈⟨ assoc◎l ⟩
  i ◎ ω ^ 4     ≈⟨ id⟩◎⟨ assoc◎l ⟩
  i ◎ i ◎ ω ^ 2 ≈⟨ assoc◎l ⟩
  i ^ 2 ◎ ω ^ 2 ∎ 

-- Scalar multiplication (Definition 4.1)
infixr 45 _●_
_●_ : {t₁ t₂ : U} → (I ⟷ I) → (t₁ ⟷ t₂) → t₁ ⟷ t₂
s ● c = uniti⋆l ◎ (s ⊗ c) ◎ unite⋆l
{-
-- Before we can even get started, we need some postulates, as the
-- proofs are quite a lot of pain
postulate
  uniti₊-coherence : add (M+.uniti⋆ {O}) ⟷₂ add (M+.uniti⋆ {O})
  unite₊-coherence : add (M+.uniti⋆ {O}) ⟷₂ add (M+.uniti⋆ {O})
  uniti⋆-coherence : mult (M×.uniti⋆ {I}) ⟷₂ mult (M×.uniti⋆ {I})
  unite⋆-coherence : mult (M×.uniti⋆ {I}) ⟷₂ mult (M×.uniti⋆ {I})
  
-- Proposition 4.3
-- (i)
scalar-comm : {s t : I ⟷ I} → s ◎ t ⟷₂ t ◎ s
scalar-comm {s} {t} = begin
  s ◎ t ≈⟨ {!!} ⟩
  t ◎ s ∎

scalar-inverse : {s t : I ⟷ I} → (s ◎ s ⟷₂ t) → !⟷ s ⟷₂ !⟷ t ◎ s
scalar-inverse {s} {t} p = {!!}
-}
