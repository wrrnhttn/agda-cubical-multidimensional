{-# OPTIONS --cubical #-}
module Multidimensional.Data.DirNum.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat

open import Multidimensional.Data.Dir

-- Dependent "directional numerals":
-- for natural n, obtain 2ⁿ "numerals".
-- This is basically a little-endian binary notation.
-- NOTE: Would an implementation of DirNum with dependent vectors be preferable
--       over using products?
DirNum : ℕ → Type₀
DirNum zero = Unit
DirNum (suc n) = Dir × (DirNum n)

-- give the next numeral, cycling back to 0
-- in case of 2ⁿ - 1
next : ∀ {n} → DirNum n → DirNum n
next {zero} tt = tt
next {suc n} (↓ , ds) = (↑ , ds)
next {suc n} (↑ , ds) = (↓ , next ds)

prev : ∀ {n} → DirNum n → DirNum n
prev {zero} tt = tt
prev {suc n} (↓ , ds) = (↓ , prev ds)
prev {suc n} (↑ , ds) = (↓ , ds)

zero-n : (n : ℕ) → DirNum n
zero-n zero = tt
zero-n (suc n) = (↓ , zero-n n)

one-n : (n : ℕ) → DirNum n
one-n zero = tt
one-n (suc n) = (↑ , zero-n n)

-- numeral for 2ⁿ - 1
max-n : (n : ℕ) → DirNum n
max-n zero = tt
max-n (suc n) = (↑ , max-n n)

-- -- TODO: rename
-- embed-next : (r : ℕ) → DirNum r → DirNum (suc r)
-- embed-next zero tt = (↓ , tt)
-- embed-next (suc r) (d , ds) with zero-n? ds
-- ... | no _ = (d , embed-next r ds)
-- ... | yes _ = (d , zero-n (suc r))

sucDoubleDirNum+ : (r : ℕ) → DirNum r → DirNum (suc r)
sucDoubleDirNum+ r x = (↑ , x)

-- bad name, since this is doubling "to" suc r
doubleDirNum+ : (r : ℕ) → DirNum r → DirNum (suc r)
doubleDirNum+ r x = (↓ , x)

dropLeast : {r : ℕ} → DirNum (suc r) → DirNum r
dropLeast {zero} d = tt
dropLeast {suc r} (x , x₁) = x₁

dropMost : {r : ℕ} → DirNum (suc r) → DirNum r
dropMost {zero} d = tt
dropMost {suc zero} (x , (x₁ , x₂)) = (x₁ , x₂)
dropMost {suc (suc r)} (x , x₁) = (x , dropMost x₁)

-- need to prove property about doubleable
--doubleDirNum : (r : ℕ) (d : DirNum r) → doubleable-n? {r} d ≡ true → DirNum r
-- bad? is not correct when not "doubleable"
-- possibly should view as operations in residue classes?
doubleDirNum : (r : ℕ) (d : DirNum r) → DirNum r
doubleDirNum zero d  = tt
doubleDirNum (suc r) d  = doubleDirNum+ r (dropMost {r} d)
-- doubleDirNum zero d doubleable = ⊥-elim (false≢true doubleable)
-- doubleDirNum (suc r) d doubleable = doubleDirNum+ r (dropMost {r} d)
