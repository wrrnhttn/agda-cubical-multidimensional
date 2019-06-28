{-# OPTIONS --cubical #-}

module Multidimensional.Data.Dir.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty

open import Cubical.Relation.Nullary

open import Multidimensional.Data.Dir.Base

¬↓≡↑ : ¬ ↓ ≡ ↑
¬↓≡↑ eq = subst (caseDir Dir ⊥) eq ↓

¬↑≡↓ : ¬ ↑ ≡ ↓
¬↑≡↓ eq = subst (caseDir ⊥ Dir) eq ↓
