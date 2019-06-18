{-# OPTIONS --cubical #-}

open import Cubical.Core.Glue
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.BinNat
open import Cubical.Relation.Nullary
open import Direction

module NNat where
-- much of this is based directly on the
-- BinNat module in the Cubical Agda library

sucn : (n : ℕ) → (ℕ → ℕ)
sucn n = iter n suc

data BNat : Type₀ where
  b0 : BNat
  b1 : BNat
  x0 : BNat → BNat
  x1 : BNat → BNat

sucBNat : BNat → BNat
sucBNat b0 = b1
sucBNat b1 = x0 b1
sucBNat (x0 bs) = x1 bs
sucBNat (x1 bs) = x0 (sucBNat bs)

BNat→ℕ : BNat → ℕ
BNat→ℕ b0 = 0
BNat→ℕ b1 = 1
BNat→ℕ (x0 x) = doubleℕ (BNat→ℕ x)
BNat→ℕ (x1 x) = suc (doubleℕ (BNat→ℕ x))

-- BNat→Binℕ : BNat → Binℕ
-- BNat→Binℕ pos0 = binℕ0
-- BNat→Binℕ pos1 = binℕpos pos1
-- BNat→Binℕ (x0 x) = {!binℕpos (x0 binℕpos (BNat→Binℕ x))!}
-- BNat→Binℕ (x1 x) = {!!}

BNat→ℕsucBNat : (b : BNat) → BNat→ℕ (sucBNat b) ≡ suc (BNat→ℕ b)
BNat→ℕsucBNat b0 = refl
BNat→ℕsucBNat b1 = refl
BNat→ℕsucBNat (x0 b) = refl
BNat→ℕsucBNat (x1 b) = λ i → doubleℕ (BNat→ℕsucBNat b i)

ℕ→BNat : ℕ → BNat
ℕ→BNat zero = b0
ℕ→BNat (suc zero) = b1
ℕ→BNat (suc (suc n)) = sucBNat (ℕ→BNat (suc n))

ℕ→BNatSuc : ∀ n → ℕ→BNat (suc n) ≡ sucBNat (ℕ→BNat n)
ℕ→BNatSuc zero = refl
ℕ→BNatSuc (suc n) = refl

bNatInd : {P : BNat → Type₀} → P b0 → ((b : BNat) → P b → P (sucBNat b)) → (b : BNat) → P b
-- prove later...

BNat→ℕ→BNat : (b : BNat) → ℕ→BNat (BNat→ℕ b) ≡ b
BNat→ℕ→BNat b = bNatInd refl hs b
  where
  hs : (b : BNat) → ℕ→BNat (BNat→ℕ b) ≡ b → ℕ→BNat (BNat→ℕ (sucBNat b)) ≡ sucBNat b
  hs b hb = 
      ℕ→BNat (BNat→ℕ (sucBNat b))
    ≡⟨ cong ℕ→BNat (BNat→ℕsucBNat b) ⟩ 
      ℕ→BNat (suc (BNat→ℕ b))
    ≡⟨ ℕ→BNatSuc (BNat→ℕ b) ⟩ 
      sucBNat (ℕ→BNat (BNat→ℕ b))
    ≡⟨ cong sucBNat hb ⟩ 
      sucBNat b
    ∎

ℕ→BNat→ℕ : (n : ℕ) → BNat→ℕ (ℕ→BNat n) ≡ n
ℕ→BNat→ℕ zero = refl
ℕ→BNat→ℕ (suc n) = 
    BNat→ℕ (ℕ→BNat (suc n))
  ≡⟨ cong BNat→ℕ (ℕ→BNatSuc n) ⟩ 
    BNat→ℕ (sucBNat (ℕ→BNat n))
  ≡⟨ BNat→ℕsucBNat (ℕ→BNat n) ⟩ 
    suc (BNat→ℕ (ℕ→BNat n))
  ≡⟨ cong suc (ℕ→BNat→ℕ n) ⟩ 
    suc n
  ∎

BNat≃ℕ : BNat ≃ ℕ
BNat≃ℕ = isoToEquiv (iso BNat→ℕ ℕ→BNat ℕ→BNat→ℕ BNat→ℕ→BNat)

BNat≡ℕ : BNat ≡ ℕ
BNat≡ℕ = ua BNat≃ℕ





---- generalize bnat:

data N (r : ℕ) : Type₀ where
  bn : DirNum r → N r
  xr : DirNum r → N r → N r
  
-- we have 2ⁿ "unary" constructors, analogous to BNat with 2¹ (b0 and b1)
-- rename n to r
sucN : ∀ {n} → N n → N n
sucN {zero} (bn tt) = xr tt (bn tt)
sucN {zero} (xr tt x) = xr tt (sucN x)
sucN {suc n} (bn (↓ , ds)) = (bn (↑ , ds))
sucN {suc n} (bn (↑ , ds)) with max? ds
... | no _ = (bn (↓ , next ds))
... | yes _ = xr (zero-n (suc n)) (bn (max-n (suc n)))
sucN {suc n} (xr d x) with max? d
... | no _ = xr (next d) x
... | yes _ = xr (zero-n (suc n)) (sucN x)

N→ℕ : (r : ℕ) (x : N r) → ℕ
N→ℕ zero (bn tt) = zero
N→ℕ zero (xr tt x) = suc (N→ℕ zero x)
N→ℕ (suc r) (bn x) = DirNum→ℕ x
N→ℕ (suc r) (xr d x) = sucn (DirNum→ℕ d) (doublesℕ (suc r) (N→ℕ (suc r) x))

N→ℕsucN : (r : ℕ) (x : N r) → N→ℕ r (sucN x) ≡ suc (N→ℕ r x)
N→ℕsucN zero (bn tt) = refl
N→ℕsucN zero (xr tt x) = 
    suc (N→ℕ zero (sucN x))
  ≡⟨ cong suc (N→ℕsucN zero x) ⟩ 
    suc (suc (N→ℕ zero x))
  ∎
N→ℕsucN (suc r) (bn (↓ , x)) = refl
N→ℕsucN (suc r) (bn (↑ , x)) with max? x
... | no _ = {!!}
... | yes _ = {!!}
N→ℕsucN (suc r) (xr x x₁) = {!!}


ℕ→N : (r : ℕ) → (n : ℕ) → N r
ℕ→N r zero = bn (zero-n r)
ℕ→N zero (suc n) = xr tt (ℕ→N zero n)
ℕ→N (suc r) (suc n) = sucN (ℕ→N (suc r) n)

ℕ→Nsuc : (r : ℕ) (n : ℕ) → ℕ→N r (suc n) ≡ sucN (ℕ→N r n)

N→ℕ→N : (r : ℕ) → (x : N r) → ℕ→N r (N→ℕ r x) ≡ x
N→ℕ→N r x = {!!}

ℕ→N→ℕ : (r : ℕ) → (n : ℕ) → N→ℕ r (ℕ→N r n) ≡ n
ℕ→N→ℕ zero zero = refl
ℕ→N→ℕ (suc r) zero = 
    doubleℕ (DirNum→ℕ (zero-n r))
  ≡⟨ cong doubleℕ (zero-n≡0 {r}) ⟩ 
    doubleℕ zero
  ≡⟨ refl ⟩ 
    zero
  ∎
ℕ→N→ℕ zero (suc n) = cong suc (ℕ→N→ℕ zero n)
ℕ→N→ℕ (suc r) (suc n) = 
    N→ℕ (suc r) (sucN (ℕ→N (suc r) n))
  ≡⟨ N→ℕsucN (suc r) (ℕ→N (suc r) n) ⟩ 
    suc (N→ℕ (suc r) (ℕ→N (suc r) n))
  ≡⟨ cong suc (ℕ→N→ℕ (suc r) n) ⟩ 
    suc n
  ∎




N≃ℕ : (r : ℕ) → N r ≃ ℕ
N≃ℕ r = isoToEquiv (iso (N→ℕ r) (ℕ→N r) (ℕ→N→ℕ r) (N→ℕ→N r))

N≡ℕ : (r : ℕ) → N r ≡ ℕ
N≡ℕ r = ua (N≃ℕ r)



---- pos approach:

data NPos (n : ℕ) : Type₀ where
  npos1 : NPos n
  x⇀ : DirNum n → NPos n → NPos n
  
sucNPos : ∀ {n} → NPos n → NPos n
sucNPos {zero} npos1      = x⇀ tt npos1
sucNPos {zero} (x⇀ tt x) = x⇀ tt (sucNPos x)
sucNPos {suc n} npos1     = x⇀ (next (one-n (suc n))) npos1
sucNPos {suc n} (x⇀ d x) with (max? d)
...            | (no _)  = x⇀ (next d) x
...            | (yes _) = x⇀ (zero-n (suc n)) (sucNPos x)

-- some examples for sanity check

2₂ : NPos 1
2₂ = x⇀ (↓ , tt) npos1

3₂ : NPos 1
3₂ = x⇀ (↑ , tt) npos1

4₂ : NPos 1
4₂ = x⇀ (↓ , tt) (x⇀ (↓ , tt) npos1)

2₄ : NPos 2
2₄ = x⇀ (↓ , (↑ , tt)) npos1 -- how does this make sense?

3₄ : NPos 2
3₄ = x⇀ (↑ , (↑ , tt)) npos1 -- how does this make sense?

-- sucnpos1≡x⇀one-n : ∀ {r} → sucNPos npos1 ≡ x⇀ (one-n r) npos1
-- sucnpos1≡x⇀one-n {zero} = refl
-- sucnpos1≡x⇀one-n {suc r} = {!!}

-- sucnposx⇀zero-n≡x⇀one-n : ∀ {r} {p} → sucNPos (x⇀ (zero-n r) p) ≡ x⇀ (one-n r) p
-- sucnposx⇀zero-n≡x⇀one-n {zero} {npos1} = {!!}
-- sucnposx⇀zero-n≡x⇀one-n {zero} {x⇀ x p} = {!!}
-- sucnposx⇀zero-n≡x⇀one-n {suc r} {p} = refl

nPosInd : ∀ {r} {P : NPos r → Type₀} →
            P npos1 →
            ((p : NPos r) → P p → P (sucNPos p)) →
            (p : NPos r) →
            P p
nPosInd {r} {P} h1 hs ps = f ps
  where
     H :  (p : NPos r) → P (x⇀ (zero-n r) p) → P (x⇀ (zero-n r) (sucNPos p))
     --H p hx0p = hs (x⇀ (one-n r) p) (hs (x⇀ (zero-n r) p) hx0p)

     f : (ps : NPos r) → P ps
     f npos1 = h1
     f (x⇀ d ps) with (max? d)
     ... | (no _) = {!nPosInd (hs npos1 h1) H ps!}
     ... | (yes _) = {!hs (x⇀ (zero-n r) ps) (nPosInd (hs npos1 h1) H ps)!}
  
-- nPosInd {zero} {P} h1 hs ps = f ps
--   where
--   H : (p : NPos zero) → P (x⇀ (zero-n zero) p) → P (x⇀ (zero-n zero) (sucNPos p))
--   H p hx0p = hs (x⇀ tt (x⇀ (zero-n zero) p)) (hs (x⇀ (zero-n zero) p) hx0p)

--   f : (ps : NPos zero) → P ps
--   f npos1 = h1
--   f (x⇀ tt ps) = nPosInd (hs npos1 h1) H ps
-- nPosInd {suc r} {P} h1 hs ps = f ps
--   where
--   H : (p : NPos (suc r)) → P (x⇀ (zero-n (suc r)) p) → P (x⇀ (zero-n (suc r)) (sucNPos p))
--   --H p hx0p = hs (x⇀ (one-n r) p) (hs (x⇀ (zero-n r) p) hx0p)

--   f : (ps : NPos (suc r)) → P ps
--   f npos1 = h1
--   f (x⇀ d ps) = {!!}

NPos→ℕ : ∀ r → NPos r → ℕ
NPos→ℕ zero npos1 = suc zero
NPos→ℕ zero (x⇀ tt x) = suc (NPos→ℕ zero x)
NPos→ℕ (suc r) npos1 = suc zero
NPos→ℕ (suc r) (x⇀ d x) with max? d
... | no _ = sucn (DirNum→ℕ (next d)) (doublesℕ (suc r) (NPos→ℕ (suc r) x))
... | yes _ = sucn (DirNum→ℕ (next d)) (doublesℕ (suc r) (suc (NPos→ℕ (suc r) x)))
-- NPos→ℕ (suc r) (x⇀ d x) = 
--   sucn (DirNum→ℕ d) (doublesℕ (suc r) (NPos→ℕ (suc r) x))

NPos→ℕsucNPos : ∀ r → (p : NPos r) → NPos→ℕ r (sucNPos p) ≡ suc (NPos→ℕ r p)
NPos→ℕsucNPos zero npos1 = refl
NPos→ℕsucNPos zero (x⇀ d p) = cong suc (NPos→ℕsucNPos zero p)
NPos→ℕsucNPos (suc r) npos1 = {!!}
    sucn (doubleℕ (DirNum→ℕ (zero-n r))) (doublesℕ r 2)
  ≡⟨ cong (λ y → sucn y (doublesℕ r 2)) (zero-n→0) ⟩
    sucn (doubleℕ zero) (doublesℕ r 2)
  ≡⟨ refl ⟩ 
    doublesℕ r 2
  ≡⟨ {!!} ⟩ {!!}
NPos→ℕsucNPos (suc r) (x⇀ d p) with max? d
... | no _ = {!!}
... | yes _ = {!!}

-- zero≠NPos→ℕ : ∀ {r} → (p : NPos r) → ¬ (zero ≡ NPos→ℕ r p)
-- zero≠NPos→ℕ {r} p = {!!}

ℕ→NPos : ∀ r → ℕ → NPos r
ℕ→NPos zero zero = npos1
ℕ→NPos zero (suc zero) = npos1
ℕ→NPos zero (suc (suc n)) = sucNPos (ℕ→NPos zero (suc n))
ℕ→NPos (suc r) zero = npos1
ℕ→NPos (suc r) (suc zero) = npos1
ℕ→NPos (suc r) (suc (suc n)) = sucNPos (ℕ→NPos (suc r) (suc n))

lemma : ∀ {r} → (ℕ→NPos r (NPos→ℕ r npos1)) ≡ npos1
lemma {zero} = refl
lemma {suc r} = refl

NPos→ℕ→NPos : ∀ r → (p : NPos r) → ℕ→NPos r (NPos→ℕ r p) ≡ p
NPos→ℕ→NPos r p = nPosInd lemma hs p
  where
  hs : (p : NPos r) → ℕ→NPos r (NPos→ℕ r p) ≡ p → ℕ→NPos r (NPos→ℕ r (sucNPos p)) ≡ (sucNPos p)
  hs p hp = 
      ℕ→NPos r (NPos→ℕ r (sucNPos p))
    ≡⟨ {!!} ⟩ 
      ℕ→NPos r (suc (NPos→ℕ r p))
    ≡⟨ {!!} ⟩ 
      sucNPos (ℕ→NPos r (NPos→ℕ r p))
    ≡⟨ cong sucNPos hp ⟩ 
      sucNPos p
    ∎


-- note: the cases for zero and suc r are almost identical
-- (why) does this need to split?
ℕ→NPos→ℕ : ∀ r → (n : ℕ) → NPos→ℕ r (ℕ→NPos r (suc n)) ≡ (suc n)
ℕ→NPos→ℕ zero zero = refl
ℕ→NPos→ℕ zero (suc n) = 
      NPos→ℕ zero (sucNPos (ℕ→NPos zero (suc n)))
    ≡⟨ {!!} ⟩ 
      suc (NPos→ℕ zero (ℕ→NPos zero (suc n)))
    ≡⟨ cong suc (ℕ→NPos→ℕ zero n) ⟩ 
      suc (suc n)
    ∎
ℕ→NPos→ℕ (suc r) zero = refl
ℕ→NPos→ℕ (suc r) (suc n) = 
    NPos→ℕ (suc r) (sucNPos (ℕ→NPos (suc r) (suc n)))
  ≡⟨ {!!} ⟩ 
    suc (NPos→ℕ (suc r) (ℕ→NPos (suc r) (suc n)))
  ≡⟨ cong suc (ℕ→NPos→ℕ (suc r) n) ⟩ 
    suc (suc n)
  ∎



