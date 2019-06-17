{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Relation.Nullary
open import Direction

module NNat where

sucn : (n : ℕ) → (ℕ → ℕ)
sucn n = iter n suc

data NPos (n : ℕ) : Type₀ where
  npos1 : NPos n
  x⇀ : DirNum n → NPos n → NPos n
  
sucNPos : ∀ {n} → NPos n → NPos n
sucNPos {zero} npos1      = x⇀ tt npos1
sucNPos {zero} (x⇀ tt x) = x⇀ tt (sucNPos x)
sucNPos {suc n} npos1     = x⇀ (one-n (suc n)) npos1
sucNPos {suc n} (x⇀ d x) with (max? d)
...            | (yes _) = x⇀ (zero-n (suc n)) (sucNPos x)
...            | (no _)  = x⇀ (next d) x

NPos→ℕ : ∀ r → NPos r → ℕ
NPos→ℕ zero npos1 = suc zero
NPos→ℕ zero (x⇀ tt x) = suc (NPos→ℕ zero x)
NPos→ℕ (suc r) npos1 = suc zero
NPos→ℕ (suc r) (x⇀ d x) = 
  sucn (DirNum→ℕ d) (doublesℕ (suc r) (NPos→ℕ (suc r) x))
