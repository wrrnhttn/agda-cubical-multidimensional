{-# OPTIONS --cubical --no-exact-split --safe #-}
module Multidimensional.Data.Extra.Nat.Base where

open import Cubical.Data.Nat

sucn : (n : ℕ) → (ℕ → ℕ)
sucn n = iter n suc
