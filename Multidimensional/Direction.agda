{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Prod

module Direction where

-- some nat things. move to own module?



sucn : (n : ℕ) → (ℕ → ℕ)
sucn n = iter n suc

doublePred : (n : ℕ) → doubleℕ (predℕ n) ≡ predℕ (predℕ (doubleℕ n))
doublePred zero = refl
doublePred (suc n) = refl

-- doubleDoublesPred : (n : ℕ) → doublesℕ n 1 ≡ 
-- doubleDoublesPred zero = refl
-- doubleDoublesPred (suc n) = {!!}

sucPred : (n : ℕ) → ¬ (n ≡ zero) → suc (predℕ n) ≡ n
sucPred zero 0≠0 = ⊥-elim (0≠0 refl)
sucPred (suc n) sucn≠0 = refl

predSucSuc : (n : ℕ) → ¬ (predℕ (suc (suc n)) ≡ 0)
predSucSuc n = snotz

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

-- 2^n(m+1) = (2^n)m + 2^n
-- doublesSuc : (n m : ℕ) → doublesℕ n (suc m) ≡ sucn (doublesℕ n 1) (doublesℕ n m)
-- doublesSuc zero m = refl
-- doublesSuc (suc n) m = 
--     doublesℕ n (suc (suc (doubleℕ m)))
--   ≡⟨ doublesSuc n (suc (doubleℕ m)) ⟩ 
--     sucn (doublesℕ n 1) (doublesℕ n (suc (doubleℕ m)))
--   ≡⟨ cong (λ z → sucn (doublesℕ n 1) z) (doublesSuc n (doubleℕ m)) ⟩ 
--      sucn (doublesℕ n 1) (sucn (doublesℕ n 1) (doublesℕ n (doubleℕ m)))
--    ≡⟨ sucnDoubles n (doublesℕ n (doubleℕ m)) ⟩ 
--      sucn (doublesℕ n 2) (doublesℕ n (doubleℕ m))
--    ∎
--    where
--      sucnDoubles : (n m : ℕ) → sucn (doublesℕ n 1) (sucn (doublesℕ n 1) m) ≡ sucn (doublesℕ n 2) m
--      sucnDoubles zero m = refl
--      sucnDoubles (suc n) m = 
--          sucn (doublesℕ n 2) (sucn (doublesℕ n 2) m)
--        ≡⟨ sym (sucnDoubles n (sucn (doublesℕ n 2) m)) ⟩ 
--          sucn (doublesℕ n 1) (sucn (doublesℕ n 1) (sucn (doublesℕ n 2) m))
--        ≡⟨ {!!} ⟩ {!!}

-- 2 * (i + n) = 2*i + 2*n
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
  where
   



  

-- predDoubles : (n m : ℕ) → ¬ (n ≡ 0) → ¬ (m ≡ 0) → ¬ (predℕ (doublesℕ n m)) ≡ 0
-- predDoubles zero m n≠0 m≠0 = ⊥-elim (n≠0 refl)
-- predDoubles (suc n) m sn≠0 m≠0 = {!!}

-- "Direction" type for determining direction in spatial structures.
-- We interpret ↓ as 0 and ↑ as 1 when used in numerals in
-- numerical types.
data Dir : Type₀ where
  ↓ : Dir
  ↑ : Dir

caseDir : ∀ {ℓ} → {A : Type ℓ} → (ad au : A) → Dir → A
caseDir ad au ↓ = ad
caseDir ad au ↑ = au

¬↓≡↑ : ¬ ↓ ≡ ↑
¬↓≡↑ eq = subst (caseDir Dir ⊥) eq ↓

¬↑≡↓ : ¬ ↑ ≡ ↓
¬↑≡↓ eq = subst (caseDir ⊥ Dir) eq ↓

-- Dependent "directional numerals":
-- for natural n, obtain 2ⁿ "numerals".
-- This is basically a little-endian binary notation.
-- NOTE: Would an implementation of DirNum with dependent vectors be preferable
--       over using products?
DirNum : ℕ → Type₀
DirNum zero = Unit
DirNum (suc n) = Dir × (DirNum n)

sucDoubleDirNum : (r : ℕ) → DirNum r → DirNum (suc r)
sucDoubleDirNum r x = (↑ , x)

doubleDirNum : (r : ℕ) → DirNum r → DirNum (suc r)
doubleDirNum r x = (↓ , x)


DirNum→ℕ : ∀ {n} → DirNum n → ℕ
DirNum→ℕ {zero} tt = zero
DirNum→ℕ {suc n} (↓ , d) = doublesℕ (suc zero) (DirNum→ℕ d)
DirNum→ℕ {suc n} (↑ , d) = suc (doublesℕ (suc zero) (DirNum→ℕ d))

double-lemma : ∀ {r} → (d : DirNum r) →
                doubleℕ (DirNum→ℕ d) ≡ DirNum→ℕ (doubleDirNum r d)
double-lemma {r} d = refl

¬↓,d≡↑,d′ : ∀ {n} → ∀ (d d′ : DirNum n) → ¬ (↓ , d) ≡ (↑ , d′)
¬↓,d≡↑,d′ {n} d d′ ↓,d≡↑,d′ = ¬↓≡↑ (cong proj₁ ↓,d≡↑,d′)

¬↑,d≡↓,d′ : ∀ {n} → ∀ (d d′ : DirNum n) → ¬ (↑ , d) ≡ (↓ , d′)
¬↑,d≡↓,d′ {n} d d′ ↑,d≡↓,d′ = ¬↑≡↓ (cong proj₁ ↑,d≡↓,d′)

-- dropping least significant bit preserves equality
dropLeast≡ : ∀ {n} → ∀ (ds ds′ : DirNum n) (d : Dir)
              → ((d , ds) ≡ (d , ds′)) → ds ≡ ds′
dropLeast≡ {n} ds ds′ d d,ds≡d,ds′ = cong proj₂ d,ds≡d,ds′

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

zero-n→0 : ∀ {r} → DirNum→ℕ (zero-n r) ≡ zero
zero-n→0 {zero} = refl
zero-n→0 {suc r} = 
    doubleℕ (DirNum→ℕ (zero-n r))
  ≡⟨ cong doubleℕ (zero-n→0 {r}) ⟩
    doubleℕ zero
  ≡⟨ refl ⟩
    zero
  ∎


zero-n? : ∀ {n} → (x : DirNum n) → Dec (x ≡ zero-n n)
zero-n? {zero} tt = yes refl
zero-n? {suc n} (↓ , ds) with zero-n? ds
... | no ds≠zero-n = no (λ y →
                            ds≠zero-n (dropLeast≡ ds (zero-n n) ↓ y))
... | yes ds≡zero-n = yes (cong (λ y → (↓ , y)) ds≡zero-n)
zero-n? {suc n} (↑ , ds) = no ((¬↑,d≡↓,d′ ds (zero-n n)))

zero-n≡0 : {r : ℕ} → DirNum→ℕ (zero-n r) ≡ zero
zero-n≡0{zero} = refl
zero-n≡0 {suc r} = 
    doubleℕ (DirNum→ℕ {r} (zero-n r))
  ≡⟨ cong doubleℕ (zero-n≡0 {r}) ⟩ 
   0
  ∎

one-n : (n : ℕ) → DirNum n
one-n zero = tt
one-n (suc n) = (↑ , zero-n n)

-- numeral for 2ⁿ - 1
max-n : (n : ℕ) → DirNum n
max-n zero = tt
max-n (suc n) = (↑ , max-n n)

max→ℕ : (r : ℕ) → DirNum→ℕ (max-n r) ≡ predℕ (doublesℕ r 1)
max→ℕ zero = refl
max→ℕ (suc r) = 
    suc (doubleℕ (DirNum→ℕ (max-n r)))
  ≡⟨ cong (λ z → suc (doubleℕ z)) (max→ℕ r) ⟩
    suc (doubleℕ (predℕ (doublesℕ r 1)))
  ≡⟨ cong suc (doublePred (doublesℕ r 1)) ⟩ 
    suc (predℕ (predℕ (doubleℕ (doublesℕ r 1))))
  ≡⟨ cong (λ z → suc (predℕ (predℕ z))) (doubleDoubles r 1) ⟩ 
    suc (predℕ (predℕ (doublesℕ (suc r) 1)))
  ≡⟨ refl ⟩ 
    suc (predℕ (predℕ (doublesℕ r 2)))
  ≡⟨ sucPred (predℕ (doublesℕ r 2)) H ⟩ 
    predℕ (doublesℕ r 2)
  ∎
  where
    G : (r : ℕ) → doubleℕ (doublesℕ r 1) ≡ doublesℕ r 2
    G zero = refl
    G (suc r) = doubleℕ (doublesℕ r 2) ≡⟨ doubleDoubles r 2 ⟩
                 doublesℕ (suc r) 2 ≡⟨ refl ⟩ doublesℕ r (doubleℕ 2) ∎
    H : ¬ predℕ (doublesℕ r 2) ≡ zero
    H = λ h → (predDoublePos (doublesℕ r 1) (doublesPos r 1 snotz)
        ((
          predℕ (doubleℕ (doublesℕ r 1)) ≡⟨ cong predℕ (G r) ⟩
          predℕ (doublesℕ r 2) ≡⟨ h ⟩
          0 ∎
         ))) 
    

max? : ∀ {n} → (x : DirNum n) → Dec (x ≡ max-n n)
max? {zero} tt = yes refl
max? {suc n} (↓ , ds) = no ((¬↓,d≡↑,d′ ds (max-n n)))
max? {suc n} (↑ , ds) with max? ds
... | yes ds≡max-n = yes (
          (↑ , ds)
        ≡⟨ cong (λ x → (↑ , x)) ds≡max-n ⟩ 
          (↑ , max-n n)
        ∎
      )
... | no ¬ds≡max-n = no (λ d,ds≡d,max-n →
                            ¬ds≡max-n ((dropLeast≡ ds (max-n n) ↑ d,ds≡d,max-n)))

maxn+1≡↑maxn : ∀ n → max-n (suc n) ≡ (↑ , (max-n n))
maxn+1≡↑maxn n = refl

maxr≡pred2ʳ : (r : ℕ) (d : DirNum r) →
           d ≡ max-n r → DirNum→ℕ d ≡ predℕ (doublesℕ r (suc zero))
maxr≡pred2ʳ zero d d≡max = refl
maxr≡pred2ʳ (suc r) (↓ , ds) d≡max = ⊥-elim ((¬↓,d≡↑,d′ ds (max-n r)) d≡max) 
maxr≡pred2ʳ (suc r) (↑ , ds) d≡max = 
     suc (doubleℕ (DirNum→ℕ ds))
   ≡⟨ cong (λ x → suc (doubleℕ x)) (maxr≡pred2ʳ r ds ds≡max) ⟩
     suc (doubleℕ (predℕ (doublesℕ r (suc zero)))) -- 2*(2^r - 1) + 1 = 2^r+1 - 1
   ≡⟨ cong suc (doublePred (doublesℕ r (suc zero))) ⟩ 
     suc (predℕ (predℕ (doubleℕ (doublesℕ r (suc zero)))))
   ≡⟨ sucPred (predℕ (doubleℕ (doublesℕ r (suc zero)))) (
              (predDoublePos (doublesℕ r (suc zero)) ((doublesPos r 1 snotz)))) ⟩
     predℕ (doubleℕ (doublesℕ r (suc zero)))
   ≡⟨ cong predℕ (doubleDoubles r (suc zero)) ⟩
     predℕ (doublesℕ (suc r) 1)
   ≡⟨ refl ⟩
     predℕ (doublesℕ r 2) -- 2^r*2 - 1 = 2^(r+1) - 1
   ∎
  where
    ds≡max : ds ≡ max-n r
    ds≡max = dropLeast≡ ds (max-n r) ↑ d≡max

-- TODO: rename
embed-next : (r : ℕ) → DirNum r → DirNum (suc r)
embed-next zero tt = (↓ , tt)
embed-next (suc r) (d , ds) with zero-n? ds
... | no _ = (d , embed-next r ds)
... | yes _ = (d , zero-n (suc r))

-- embed-next-thm : (r : ℕ) (d : DirNum r) → DirNum→ℕ d ≡ DirNum→ℕ (embed-next r d)
-- embed-next-thm zero d = refl
-- embed-next-thm (suc r) (d , ds) with zero-n? ds
-- ... | no _ = {!!}
-- ... | yes _ = {!!}

-- TODO: rename?
nextsuc-lemma : (r : ℕ) (x : DirNum r) →
         ¬ ((sucDoubleDirNum r x) ≡ max-n (suc r)) → ¬ (x ≡ max-n r)
nextsuc-lemma zero tt ¬H = ⊥-elim (¬H refl)
nextsuc-lemma (suc r) (↓ , x) ¬H = ¬↓,d≡↑,d′ x (max-n r)
nextsuc-lemma (suc r) (↑ , x) ¬H =
  λ h → ¬H (H (dropLeast≡ x (max-n r) ↑ h)) --⊥-elim (¬H H)
  where
    H : (x ≡ max-n r) →
         sucDoubleDirNum (suc r) (↑ , x) ≡ (↑ , (↑ , max-n r))
    H x≡maxnr = 
        sucDoubleDirNum (suc r) (↑ , x)
      ≡⟨ cong (λ y → sucDoubleDirNum (suc r) (↑ , y)) x≡maxnr ⟩
        sucDoubleDirNum (suc r) (↑ , max-n r)
      ≡⟨ refl ⟩ 
        (↑ , (↑ , max-n r))
      ∎


next≡suc : (r : ℕ) (x : DirNum r) →
            ¬ (x ≡ max-n r) → DirNum→ℕ (next x) ≡ suc (DirNum→ℕ x)
next≡suc zero tt ¬x≡maxnr = ⊥-elim (¬x≡maxnr refl)
next≡suc (suc r) (↓ , x) ¬x≡maxnr = refl
next≡suc (suc r) (↑ , x) ¬x≡maxnr = 
    doubleℕ (DirNum→ℕ (next x))
  ≡⟨ cong doubleℕ (next≡suc r x (nextsuc-lemma r x ¬x≡maxnr)) ⟩
    doubleℕ (suc (DirNum→ℕ x))
  ≡⟨ refl ⟩ 
    suc (suc (doubleℕ (DirNum→ℕ x)))
  ∎

-- doublesuclemma : (r : ℕ) (x : DirNum (suc r)) →
--          doubleℕ (DirNum→ℕ (next x)) ≡ suc (suc (doubleℕ (DirNum→ℕ x)))
-- doublesuclemma zero (↓ , x₁) = refl
-- doublesuclemma zero (↑ , x₁) = {!!}
-- doublesuclemma (suc r) x = {!!}
  --     doubleℕ (DirNum→ℕ (next x))
  -- ≡⟨ cong doubleℕ (next≡suc r x ¬x≡maxnr) ⟩
  --   doubleℕ (suc (DirNum→ℕ x))
  -- ≡⟨ refl ⟩ 
  --   suc (suc (doubleℕ (DirNum→ℕ x)))
  -- ∎
