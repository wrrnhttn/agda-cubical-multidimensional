{-# OPTIONS --cubical --no-exact-split --safe #-}
module Multidimensional.Data.Extra.Nat.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Empty

open import Cubical.Relation.Nullary

open import Multidimensional.Data.Extra.Nat.Base

sucnsuc : (n m : ℕ) → sucn n (suc m) ≡ suc (sucn n m)
sucnsuc zero m = refl
sucnsuc (suc n) m = 
    sucn (suc n) (suc m) ≡⟨ refl ⟩
    suc (sucn n (suc m)) ≡⟨ cong suc (sucnsuc n m) ⟩ 
    suc (suc (sucn n m)) ∎

doublePred : (n : ℕ) → doubleℕ (predℕ n) ≡ predℕ (predℕ (doubleℕ n))
doublePred zero = refl
doublePred (suc n) = refl

sucPred : (n : ℕ) → ¬ (n ≡ zero) → suc (predℕ n) ≡ n
sucPred zero 0≠0 = ⊥-elim (0≠0 refl)
sucPred (suc n) sucn≠0 = refl

doubleDoubles : (n m : ℕ) → doubleℕ (doublesℕ n m) ≡ doublesℕ (suc n) m
doubleDoubles zero m = refl
doubleDoubles (suc n) m = doubleDoubles n (doubleℕ m)

doublePos : (n : ℕ) → ¬ (n ≡ 0) → ¬ (doubleℕ n ≡ 0)
doublePos zero 0≠0 = ⊥-elim (0≠0 refl)
doublePos (suc n) sn≠0 = snotz

doublesPos : (n m : ℕ) → ¬ (m ≡ 0) → ¬ (doublesℕ n m ≡ 0)
doublesPos zero m m≠0 = m≠0
doublesPos (suc n) m m≠0 = doublesPos n (doubleℕ m) (doublePos m (m≠0))

predDoublePos : (n : ℕ) → ¬ (n ≡ 0) → ¬ (predℕ (doubleℕ n)) ≡ 0
predDoublePos zero n≠0 = ⊥-elim (n≠0 refl)
predDoublePos (suc n) sn≠0 = snotz

doubleDoublesOne≠0 : (n : ℕ) → ¬ (doubleℕ (doublesℕ n (suc zero)) ≡ 0)
doubleDoublesOne≠0 zero = snotz
doubleDoublesOne≠0 (suc n) = doublePos (doublesℕ n 2) (doublesPos n 2 (snotz))

predDoubleDoublesOne≠0 : (n : ℕ) → ¬ (predℕ (doubleℕ (doublesℕ n (suc zero))) ≡ 0)
predDoubleDoublesOne≠0 zero = snotz
predDoubleDoublesOne≠0 (suc n) = predDoublePos (doublesℕ n 2) (doublesPos n 2 snotz)

doublesZero : (n : ℕ) → doublesℕ n zero ≡ zero
doublesZero zero = refl
doublesZero (suc n) = doublesZero n

doubleSucn : (i n : ℕ) →  doubleℕ (sucn i n) ≡ sucn (doubleℕ i) (doubleℕ n)
doubleSucn zero n = refl
doubleSucn (suc i) n = 
    suc (suc (doubleℕ (sucn i n)))
  ≡⟨ cong (λ z → suc (suc z)) (doubleSucn i n) ⟩ 
    suc (suc (sucn (doubleℕ i) (doubleℕ n)))
  ≡⟨ refl ⟩ 
    suc (sucn (suc (doubleℕ i)) (doubleℕ n))
  ≡⟨ cong suc refl ⟩ 
    sucn (suc (suc (doubleℕ i))) (doubleℕ n)
  ∎

doublesSucn : (i n m : ℕ) → doublesℕ n (sucn i m) ≡ sucn (doublesℕ n i) (doublesℕ n m)
doublesSucn i zero m = refl
doublesSucn i (suc n) m = 
    doublesℕ n (doubleℕ (sucn i m))
  ≡⟨  cong (doublesℕ n) (doubleSucn i m) ⟩ 
    doublesℕ n (sucn (doubleℕ i) (doubleℕ m))
  ≡⟨ doublesSucn (doubleℕ i) n (doubleℕ m) ⟩ 
     sucn (doublesℕ n (doubleℕ i)) (doublesℕ n (doubleℕ m))
  ∎

-- 2^n * (m + 2) =
doublesSucSuc : (n m : ℕ) → doublesℕ n (suc (suc m)) ≡ sucn (doublesℕ (suc n) 1) (doublesℕ n m)
doublesSucSuc zero m = refl
doublesSucSuc (suc n) m = 
    doublesℕ (suc n) (suc (suc m))
  ≡⟨ refl ⟩
    doublesℕ n (sucn 4 (doubleℕ m))
  ≡⟨ doublesSucn 4 n (doubleℕ m) ⟩ 
    sucn (doublesℕ n 4) (doublesℕ n (doubleℕ m))
  ∎


n+n≡2n : (n : ℕ) → sucn n n ≡ doubleℕ n
n+n≡2n zero = refl
n+n≡2n (suc n) = 
    sucn (suc n) (suc n)
  ≡⟨ sucnsuc (suc n) n ⟩
    suc (sucn (suc n) n)
  ≡⟨ refl ⟩ 
   suc (suc (sucn n n))
  ≡⟨ cong (λ z → suc (suc z)) (n+n≡2n n) ⟩ 
   suc (suc (doubleℕ n))
  ∎

is-zero? : (n : ℕ) → Dec (n ≡ 0)
is-zero? zero = yes refl
is-zero? (suc n) = no snotz

--open import Cubical.Foundations.Logic
-- open import Cubical.Relation.Nullary

-- nonzero-is-suc : (n : ℕ) → ¬ (n ≡ 0) → ∃[ m ] (n ≡ suc m)
-- nonzero-is-suc n n≠0 = ?
nonzero-is-suc : (n : ℕ) → ¬ (n ≡ 0) → Σ[ m ∈ ℕ ] (n ≡ suc m)
nonzero-is-suc zero n≠0 = ⊥-elim (n≠0 refl)
nonzero-is-suc (suc n) n≠0 = (n , refl)
