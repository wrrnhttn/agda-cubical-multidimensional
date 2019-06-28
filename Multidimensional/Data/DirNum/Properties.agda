{-# OPTIONS --cubical #-}
module Multidimensional.Data.DirNum.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Prod
open import Cubical.Data.Bool
open import Cubical.Data.Nat

open import Cubical.Relation.Nullary

open import Multidimensional.Data.Dir
open import Multidimensional.Data.DirNum.Base
open import Multidimensional.Data.Extra.Nat


double-lemma : ∀ {r} → (d : DirNum r) →
               doubleℕ (DirNum→ℕ d) ≡ DirNum→ℕ (doubleDirNum+ r d)
double-lemma {r} d = refl

¬↓,d≡↑,d′ : ∀ {n} → ∀ (d d′ : DirNum n) → ¬ (↓ , d) ≡ (↑ , d′)
¬↓,d≡↑,d′ {n} d d′ ↓,d≡↑,d′ = ¬↓≡↑ (cong proj₁ ↓,d≡↑,d′)

¬↑,d≡↓,d′ : ∀ {n} → ∀ (d d′ : DirNum n) → ¬ (↑ , d) ≡ (↓ , d′)
¬↑,d≡↓,d′ {n} d d′ ↑,d≡↓,d′ = ¬↑≡↓ (cong proj₁ ↑,d≡↓,d′)


-- dropping least significant bit preserves equality
-- TODO: this was copied over from Direction.agda ; redefine using DropLeast
dropLeast≡ : ∀ {n} → ∀ (ds ds′ : DirNum n) (d : Dir)
              → ((d , ds) ≡ (d , ds′)) → ds ≡ ds′
dropLeast≡ {n} ds ds′ d d,ds≡d,ds′ = cong proj₂ d,ds≡d,ds′

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

-- x is doubleable as a DirNum precisely when x's most significant bit is 0
-- this should return a Dec
doubleable-n? : {n : ℕ} → (x : DirNum n) → Bool
doubleable-n? {zero} tt = false
doubleable-n? {suc n} (x , x₁) with zero-n? x₁
... | yes _ = true
... | no _ = doubleable-n? x₁

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

