{-# OPTIONS --cubical #-}

module Multidimensional.Data.NNat.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.Data.Bool

open import Cubical.Relation.Nullary

open import Multidimensional.Data.Extra.Nat
open import Multidimensional.Data.Dir
open import Multidimensional.Data.DirNum

data N (r : ℕ) : Type₀ where
  bn : DirNum r → N r
  xr : DirNum r → N r → N r

-- should define induction principle for N r
  
-- we have 2ⁿ "unary" constructors, analogous to BNat with 2¹ (b0 and b1)
-- rename n to r
-- this likely introduces inefficiencies compared
-- to BinNat, with the max? check etc.
sucN : ∀ {n} → N n → N n
sucN {zero} (bn tt) = xr tt (bn tt)
sucN {zero} (xr tt x) = xr tt (sucN x)
sucN {suc n} (bn (↓ , ds)) = (bn (↑ , ds))
sucN {suc n} (bn (↑ , ds)) with max? ds
... | no _ = (bn (↓ , next ds))
... | yes _ = xr (zero-n (suc n)) (bn (one-n (suc n)))
sucN {suc n} (xr d x) with max? d
... | no _ = xr (next d) x
... | yes _ = xr (zero-n (suc n)) (sucN x)

sucnN : {r : ℕ} → (n : ℕ) → (N r → N r)
sucnN n = iter n sucN

doubleN : (r : ℕ) → N r → N r
doubleN zero (bn tt) = bn tt
doubleN zero (xr d x) = sucN (sucN (doubleN zero x))
doubleN (suc r) (bn x) with zero-n? x
... | yes _    = bn x
            -- bad:
... | no _ = caseBool (bn (doubleDirNum (suc r) x)) (xr (zero-n (suc r)) (bn x)) (doubleable-n? x)
-- ... | no _  | doubleable  = {!bn (doubleDirNum x)!}
-- ... | no _  | notdoubleable = xr (zero-n (suc r)) (bn x)
doubleN (suc r) (xr x x₁) = sucN (sucN (doubleN (suc r) x₁))

doublesN : (r : ℕ) → ℕ → N r → N r
doublesN r zero m = m
doublesN r (suc n) m = doublesN r n (doubleN r m)

N→ℕ : (r : ℕ) (x : N r) → ℕ
N→ℕ zero (bn tt) = zero
N→ℕ zero (xr tt x) = suc (N→ℕ zero x)
N→ℕ (suc r) (bn x) = DirNum→ℕ x
N→ℕ (suc r) (xr d x) = sucn (DirNum→ℕ d) (doublesℕ (suc r) (N→ℕ (suc r) x))

ℕ→N : (r : ℕ) → (n : ℕ) → N r
ℕ→N r zero = bn (zero-n r)
ℕ→N zero (suc n) = xr tt (ℕ→N zero n)
ℕ→N (suc r) (suc n) = sucN (ℕ→N (suc r) n)
