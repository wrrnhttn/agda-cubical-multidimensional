{-# OPTIONS --cubical #-}
module Multidimensional.Data.Dir.Base where

open import Cubical.Core.Primitives

-- "Direction" type for determining direction in spatial structures.
-- We interpret ↓ as 0 and ↑ as 1 when used in numerals in
-- numerical types.
data Dir : Type₀ where
  ↓ : Dir
  ↑ : Dir

caseDir : ∀ {ℓ} → {A : Type ℓ} → (ad au : A) → Dir → A
caseDir ad au ↓ = ad
caseDir ad au ↑ = au
