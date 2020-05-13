{-# OPTIONS --cubical #-}

-- a place for scratch work and experiments

module Multidimensional.Experimental where

open import Multidimensional.Data.NNat


open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary

-- base n representations of nats

m<sucm : ∀ m → m < suc m
m<sucm zero = zero , snd zero-≤
m<sucm (suc m) = suc-≤-suc (m<sucm m)

_≤?_ : (x y : ℕ) → Dec (x ≤ y)
zero ≤? y = yes zero-≤
suc x ≤? zero = no λ sx≤zero → ¬-<-zero ((<≤-trans (m<sucm x) sx≤zero))
suc x ≤? suc y with x ≤? y
... | yes x≤y =  yes (suc-≤-suc x≤y)
... | no x≰y =  no λ sx≤sy → x≰y (pred-≤-pred sx≤sy) -- want x≰y -> sx≰sy

base-n : ∀ (r : ℕ) → ℕ → List (Fin r)
base-n r zero = []
base-n r (suc n) = {!!}
