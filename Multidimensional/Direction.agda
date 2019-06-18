{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Prod

module Direction where

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
-- This is basically a big-endian binary notation.
-- NOTE: Would an implementation of DirNum with dependent vectors be preferable
--       over using products?
DirNum : ℕ → Type₀
DirNum zero = Unit
DirNum (suc n) = Dir × (DirNum n)

sucDoubleDirNum : (r : ℕ) → DirNum r → DirNum (suc r)
sucDoubleDirNum r x = (↑ , x)

DirNum→ℕ : ∀ {n} → DirNum n → ℕ
DirNum→ℕ {zero} tt = zero
DirNum→ℕ {suc n} (↓ , d) = doublesℕ (suc zero) (DirNum→ℕ d)
DirNum→ℕ {suc n} (↑ , d) = suc (doublesℕ (suc zero) (DirNum→ℕ d))

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
