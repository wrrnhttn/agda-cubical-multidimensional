{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Relation.Nullary
open import Direction

module NNat where
-- much of this is based directly on the
-- BinNat module in the Cubical Agda library

sucn : (n : ℕ) → (ℕ → ℕ)
sucn n = iter n suc

data NPos (n : ℕ) : Type₀ where
  npos1 : NPos n
  x⇀ : DirNum n → NPos n → NPos n
  
sucNPos : ∀ {n} → NPos n → NPos n
sucNPos {zero} npos1      = x⇀ (zero-n zero) npos1
sucNPos {zero} (x⇀ tt x) = x⇀ tt (sucNPos x)
sucNPos {suc n} npos1     = x⇀ (zero-n (suc n)) npos1
sucNPos {suc n} (x⇀ d x) with (max? d)
...            | (no _)  = x⇀ (next d) x
...            | (yes _) = x⇀ (zero-n (suc n)) (sucNPos x)

sucnpos1≡x⇀zero-n : ∀ {r} → sucNPos npos1 ≡ x⇀ (zero-n r) npos1
sucnpos1≡x⇀zero-n {zero} = refl
sucnpos1≡x⇀zero-n {suc r} = refl

sucnposx⇀zero-n≡x⇀one-n : ∀ {r} {p} → sucNPos (x⇀ (zero-n r) p) ≡ x⇀ (one-n r) p
sucnposx⇀zero-n≡x⇀one-n {zero} {npos1} = {!!}
sucnposx⇀zero-n≡x⇀one-n {zero} {x⇀ x p} = {!!}
sucnposx⇀zero-n≡x⇀one-n {suc r} {p} = refl

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
NPos→ℕ (suc r) (x⇀ d x) = 
  sucn (DirNum→ℕ d) (doublesℕ (suc r) (NPos→ℕ (suc r) x))

-- zero≠NPos→ℕ : ∀ {r} → (p : NPos r) → ¬ (zero ≡ NPos→ℕ r p)
-- zero≠NPos→ℕ {r} p = {!!}

ℕ→NPos : ∀ r → ℕ → NPos r
ℕ→NPos r zero = npos1
ℕ→NPos zero (suc zero) = npos1
ℕ→NPos zero (suc (suc n)) = sucNPos (ℕ→NPos zero (suc n))
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



