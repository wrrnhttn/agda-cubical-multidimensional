{-# OPTIONS --cubical #-}

module Multidimensional.Data.NNat.Properties where

open import Cubical.Core.Glue

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.Data.Empty
open import Cubical.Data.Unit

open import Cubical.Relation.Nullary

open import Multidimensional.Data.Extra.Nat
open import Multidimensional.Data.Dir
open import Multidimensional.Data.DirNum
open import Multidimensional.Data.NNat.Base

N→ℕsucN : (r : ℕ) (x : N r) → N→ℕ r (sucN x) ≡ suc (N→ℕ r x)
N→ℕsucN zero (bn tt) = refl
N→ℕsucN zero (xr tt x) = 
    suc (N→ℕ zero (sucN x))
  ≡⟨ cong suc (N→ℕsucN zero x) ⟩ 
    suc (suc (N→ℕ zero x))
  ∎
N→ℕsucN (suc r) (bn (↓ , d)) = refl
N→ℕsucN (suc r) (bn (↑ , d)) with max? d
... | no d≠max = 
          doubleℕ (DirNum→ℕ (next d))
        ≡⟨ cong doubleℕ (next≡suc r d d≠max)  ⟩ 
          doubleℕ (suc (DirNum→ℕ d))
        ∎
... | yes d≡max = -- this can probably be shortened by not reducing down to zero
          sucn (doubleℕ (DirNum→ℕ (zero-n r)))
            (doublesℕ r (suc (suc (doubleℕ (doubleℕ (DirNum→ℕ (zero-n r)))))))
        ≡⟨ cong (λ x → sucn (doubleℕ x) (doublesℕ r (suc (suc (doubleℕ (doubleℕ x)))))) (zero-n→0 {r}) ⟩ 
          sucn (doubleℕ zero) (doublesℕ r (suc (suc (doubleℕ (doubleℕ zero)))))
        ≡⟨ refl ⟩
          doublesℕ (suc r) (suc zero) -- 2^(r+1)
        ≡⟨ sym (doubleDoubles r 1) ⟩
          doubleℕ (doublesℕ r (suc zero)) --2*2^r
        ≡⟨ sym (sucPred (doubleℕ (doublesℕ r (suc zero))) (doubleDoublesOne≠0 r)) ⟩
          suc (predℕ (doubleℕ (doublesℕ r (suc zero))))
        ≡⟨ cong suc (sym (sucPred (predℕ (doubleℕ (doublesℕ r (suc zero)))) (predDoubleDoublesOne≠0 r))) ⟩
          suc (suc (predℕ (predℕ (doubleℕ (doublesℕ r (suc zero))))))
        ≡⟨ cong (λ x → suc (suc x)) (sym (doublePred (doublesℕ r (suc zero)))) ⟩
          suc (suc (doubleℕ (predℕ (doublesℕ r (suc zero)))))
        ≡⟨ cong (λ x → suc (suc (doubleℕ x))) (sym (maxr≡pred2ʳ r d d≡max)) ⟩
          suc (suc (doubleℕ (DirNum→ℕ d))) -- 2*(2^r - 1) + 2 = 2^(r+1) - 2 + 2 = 2^(r+1)
        ∎
N→ℕsucN (suc r) (xr (↓ , d) x) = refl
N→ℕsucN (suc r) (xr (↑ , d) x) with max? d
... | no d≠max = 
          sucn (doubleℕ (DirNum→ℕ (next d)))
           (doublesℕ r (doubleℕ (N→ℕ (suc r) x)))
        ≡⟨ cong (λ y → sucn (doubleℕ y) (doublesℕ r (doubleℕ (N→ℕ (suc r) x)))) (next≡suc r d d≠max) ⟩ 
          sucn (doubleℕ (suc (DirNum→ℕ d)))
           (doublesℕ r (doubleℕ (N→ℕ (suc r) x)))
        ≡⟨ refl ⟩ 
          suc
           (suc
            (iter (doubleℕ (DirNum→ℕ d)) suc
            (doublesℕ r (doubleℕ (N→ℕ (suc r) x)))))
        ∎
... | yes d≡max = 
        sucn (doubleℕ (DirNum→ℕ (zero-n r)))
        (doublesℕ r (doubleℕ (N→ℕ (suc r) (sucN x))))
      ≡⟨ cong (λ z → sucn (doubleℕ z) (doublesℕ r (doubleℕ (N→ℕ (suc r) (sucN x))))) (zero-n≡0 {r}) ⟩ 
        sucn (doubleℕ zero)
        (doublesℕ r (doubleℕ (N→ℕ (suc r) (sucN x))))
      ≡⟨ refl ⟩ 
        doublesℕ r (doubleℕ (N→ℕ (suc r) (sucN x)))
      ≡⟨ cong (λ x → doublesℕ r (doubleℕ x)) (N→ℕsucN (suc r) x)  ⟩ 
        doublesℕ r (doubleℕ (suc (N→ℕ (suc r) x)))
      ≡⟨ refl ⟩ 
        doublesℕ r (suc (suc (doubleℕ (N→ℕ (suc r) x)))) -- 2^r * (2x + 2) = 2^(r+1)x + 2^(r+1)
      ≡⟨ doublesSucSuc r (doubleℕ (N→ℕ (suc r) x)) ⟩ 
        sucn (doublesℕ (suc r) 1) -- _ + 2^(r+1)
         (doublesℕ (suc r) (N→ℕ (suc r) x)) --  2^(r+1)x + 2^(r+1)
      ≡⟨ H r (doublesℕ (suc r) (N→ℕ (suc r) x)) ⟩
        suc
         (suc
          (sucn (doubleℕ (predℕ (doublesℕ r 1))) -- _ + 2(2^r - 1) + 2
           (doublesℕ (suc r) (N→ℕ (suc r) x))))
      ≡⟨ refl ⟩
        suc
         (suc
          (sucn (doubleℕ (predℕ (doublesℕ r 1)))
           (doublesℕ r (doubleℕ (N→ℕ (suc r) x)))))
      ≡⟨ cong (λ z → suc (suc (sucn (doubleℕ z) (doublesℕ r (doubleℕ (N→ℕ (suc r) x)))))) (sym (max→ℕ r))  ⟩
         suc
         (suc
          (sucn (doubleℕ (DirNum→ℕ (max-n r)))
           (doublesℕ r (doubleℕ (N→ℕ (suc r) x)))))
      ≡⟨ cong (λ z → suc (suc (sucn (doubleℕ (DirNum→ℕ z)) (doublesℕ r (doubleℕ (N→ℕ (suc r) x)))))) (sym (d≡max)) ⟩
         suc
         (suc
          (sucn (doubleℕ (DirNum→ℕ d))
           (doublesℕ r (doubleℕ (N→ℕ (suc r) x))))) -- (2^r*2x + (2*(2^r - 1))) + 2 = 2^(r+1)x + 2^(r+1)
      ∎
      where
        -- this lemma is silly, should prove some better helper lemmas
        H : (n m : ℕ) → sucn (doublesℕ (suc n) 1) m ≡ suc (suc (sucn (doubleℕ (predℕ (doublesℕ n 1))) m))
        H zero m = refl
        H (suc n) m = 
            sucn (doublesℕ n 4) m ≡⟨ cong (λ z → sucn z m) (doublesSucSuc n 2) ⟩ 
            sucn (sucn (doublesℕ (suc n) 1) (doublesℕ n 2)) m ≡⟨ refl ⟩ 
            sucn (sucn (doublesℕ n 2) (doublesℕ  n 2)) m ≡⟨ {!!} ⟩ 
            sucn (doubleℕ (doublesℕ n 2)) m ≡⟨ {!!} ⟩
            {!!} ≡⟨ {!!} ⟩
            suc (suc (predℕ (predℕ (sucn (doubleℕ (doublesℕ n 2)) m)))) ≡⟨ {!!} ⟩
            suc
             (suc
              (sucn (predℕ (predℕ (doubleℕ (doublesℕ n 2))))
               m))                                       ≡⟨ cong (λ z → suc (suc (sucn z m)))
                                                            (sym (doublePred (doublesℕ n 2))) ⟩
            suc (suc (sucn (doubleℕ (predℕ (doublesℕ n 2))) m)) ∎

ℕ→Nsuc : (r : ℕ) (n : ℕ) → ℕ→N r (suc n) ≡ sucN (ℕ→N r n)
ℕ→Nsuc zero zero = refl
ℕ→Nsuc zero (suc n) with is-zero? n
... | yes n=0 = 
        xr tt (xr tt (ℕ→N 0 n))      ≡⟨ cong (λ z → xr tt (xr tt (ℕ→N 0 z)))
                                             n=0 ⟩
        xr tt (sucN (ℕ→N zero zero)) ≡⟨ cong (λ z → xr tt (sucN (ℕ→N zero z)))
                                             (sym n=0) ⟩
        xr tt (sucN (ℕ→N zero n))    ∎
... | no n≠0 = 
        xr tt (xr tt (ℕ→N 0 n))   ≡⟨ refl ⟩ 
        xr tt (ℕ→N zero (suc n)) ≡⟨ cong (λ z → xr tt z) (ℕ→Nsuc zero n) ⟩ 
        xr tt (sucN (ℕ→N 0 n))   ∎
ℕ→Nsuc (suc r) n = refl

ℕ→Nsucn : (r : ℕ) (n m : ℕ) → ℕ→N r (sucn n m) ≡ sucnN n (ℕ→N r m)
ℕ→Nsucn zero zero m = refl
ℕ→Nsucn zero (suc n) zero = {!!}
ℕ→Nsucn zero (suc n) (suc m) = {!!}
ℕ→Nsucn (suc r) zero m = refl
ℕ→Nsucn (suc r) (suc n) zero = {!!}
ℕ→Nsucn (suc r) (suc n) (suc m) = {!!}

NℕNlemma : (r : ℕ) (d : DirNum r) → ℕ→N r (DirNum→ℕ d) ≡ bn d
NℕNlemma zero tt = refl
NℕNlemma (suc r) (↓ , ds) = 
    ℕ→N (suc r) (doubleℕ (DirNum→ℕ ds))
  ≡⟨ {!!} ⟩ {!!}
NℕNlemma (suc r) (↑ , ds) = {!!}

N→ℕ→N : (r : ℕ) → (x : N r) → ℕ→N r (N→ℕ r x) ≡ x
N→ℕ→N zero (bn tt) = refl
N→ℕ→N zero (xr tt x) = cong (xr tt) (N→ℕ→N zero x)
N→ℕ→N (suc r) (bn (↓ , ds)) = 
    ℕ→N (suc r) (doubleℕ (DirNum→ℕ ds))
  ≡⟨ cong (λ x → ℕ→N (suc r) x) (double-lemma ds) ⟩ 
    ℕ→N (suc r) (DirNum→ℕ {suc r} (↓ , ds))
  ≡⟨ NℕNlemma (suc r) (↓ , ds) ⟩ 
    bn (↓ , ds)
  ∎
N→ℕ→N (suc r) (bn (↑ , ds)) = 
    sucN (ℕ→N (suc r) (doubleℕ (DirNum→ℕ ds)))
  ≡⟨ cong (λ x → sucN (ℕ→N (suc r) x)) (double-lemma ds) ⟩ 
    sucN (ℕ→N (suc r) (DirNum→ℕ {suc r} (↓ , ds)))
  ≡⟨ cong sucN (NℕNlemma (suc r) (↓ , ds)) ⟩ 
    sucN (bn (↓ , ds))
  ≡⟨ refl ⟩
    bn (↑ , ds)
  ∎
N→ℕ→N (suc r) (xr (↓ , ds) x) = 
     ℕ→N (suc r)
      (sucn (doubleℕ (DirNum→ℕ ds))
       (doublesℕ r (doubleℕ (N→ℕ (suc r) x))))
   ≡⟨ cong (λ z → ℕ→N (suc r) (sucn z (doublesℕ r (doubleℕ (N→ℕ (suc r) x))))) (double-lemma ds)  ⟩ 
      ℕ→N (suc r)
      (sucn (DirNum→ℕ {suc r} (↓ , ds))
       (doublesℕ r (doubleℕ (N→ℕ (suc r) x))))
   ≡⟨ refl ⟩
     ℕ→N (suc r)
      (sucn (DirNum→ℕ {suc r} (↓ , ds))
       (doublesℕ (suc r) (N→ℕ (suc r) x)))
   ≡⟨ ℕ→Nsucn (suc r) (DirNum→ℕ {suc r} (↓ , ds)) (doublesℕ (suc r) (N→ℕ (suc r) x)) ⟩
     sucnN (DirNum→ℕ {suc r} (↓ , ds))
      (ℕ→N (suc r) (doublesℕ (suc r) (N→ℕ (suc r) x)))
   ≡⟨ cong (λ z → sucnN (DirNum→ℕ {suc r} (↓ , ds)) z) (H (suc r) (suc r) (N→ℕ (suc r) x)) ⟩
     sucnN (DirNum→ℕ {suc r} (↓ , ds))
      (doublesN (suc r) (suc r) (ℕ→N (suc r) (N→ℕ (suc r) x)))
   ≡⟨ cong (λ z → sucnN (DirNum→ℕ {suc r} (↓ , ds)) (doublesN (suc r) (suc r) z)) (N→ℕ→N (suc r) x) ⟩
     sucnN (DirNum→ℕ {suc r} (↓ , ds))
      (doublesN (suc r) (suc r) x)
   ≡⟨ G (suc r) (↓ , ds) x snotz ⟩
     xr (↓ , ds) x ∎
   where
     H : (r m n : ℕ) → ℕ→N r (doublesℕ m n) ≡ doublesN r m (ℕ→N r n)
     H r m n = {!!}
     G : (r : ℕ) (d : DirNum r) (x : N r) → ¬ (r ≡ 0) → sucnN (DirNum→ℕ {r} d) (doublesN r r x) ≡ xr d x
     G zero d x 0≠0 = ⊥-elim (0≠0 refl)
     G (suc r) d (bn x) r≠0 = {!!}
     G (suc r) d (xr x x₁) r≠0 = {!!}
N→ℕ→N (suc r) (xr (↑ , ds) x) with max? ds
... | no ds≠max = 
          sucN
          (ℕ→N (suc r)
           (sucn (doubleℕ (DirNum→ℕ ds))
            (doublesℕ r (doubleℕ (N→ℕ (suc r) x)))))
        ≡⟨ sym (ℕ→Nsuc (suc r)
                (sucn (doubleℕ (DirNum→ℕ ds)) (doublesℕ r (doubleℕ (N→ℕ (suc r) x)))))
         ⟩ 
           ℕ→N (suc r)
           (suc (sucn (doubleℕ (DirNum→ℕ ds)) (doublesℕ r (doubleℕ (N→ℕ (suc r) x)))))
        ≡⟨ refl ⟩ 
           ℕ→N (suc r)
           (suc (sucn (doubleℕ (DirNum→ℕ ds)) (doublesℕ (suc r) (N→ℕ (suc r) x))))
        ≡⟨ cong (λ z → ℕ→N (suc r) z)
                (sym (sucnsuc (doubleℕ (DirNum→ℕ ds)) (doublesℕ (suc r) (N→ℕ (suc r) x))))
         ⟩ 
           ℕ→N (suc r)
           (sucn (doubleℕ (DirNum→ℕ ds)) (suc (doublesℕ (suc r) (N→ℕ (suc r) x))))
         ≡⟨ ℕ→Nsucn (suc r) (doubleℕ (DirNum→ℕ ds)) (suc (doublesℕ (suc r) (N→ℕ (suc r) x))) ⟩ 
           sucnN (doubleℕ (DirNum→ℕ ds)) (ℕ→N (suc r) (suc (doublesℕ (suc r) (N→ℕ (suc r) x))))
         ≡⟨ cong (λ z → sucnN (doubleℕ (DirNum→ℕ ds)) z)
                  (ℕ→Nsuc (suc r) (doublesℕ (suc r) (N→ℕ (suc r) x)))
          ⟩
           --   (2^(r+1)*x + 1) + 2*ds
           -- = 2*(2^r*x + ds) + 1
           -- = 2*(
           sucnN (doubleℕ (DirNum→ℕ ds)) (sucN (ℕ→N (suc r) (doublesℕ (suc r) (N→ℕ (suc r) x))))
         ≡⟨ {!!} ⟩ {!!}
... | yes ds≡max = {!!}

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
