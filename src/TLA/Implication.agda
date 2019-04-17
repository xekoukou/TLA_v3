module TLA.Implication {ℓ} {A : Set ℓ} where

open import TLA.Core
import TLA.Common as C
import TLA.CoreP {ℓ} {A} as Cp
import TLA.Closure {ℓ} {A} as Cls
import TLA.Stuttering {ℓ} {A} as Stt

import Level as L
import Relation.Binary.PropositionalEquality as P
import Relation.Binary.HeterogeneousEquality as H
open import Data.Fin using (Fin ; toℕ ; inject≤ ; cast ; fromℕ≤)
open import Data.Fin.Properties using (toℕ-inject≤ ; inject≤-refl
                                      ; inject≤-irrelevant
                                      ; inject≤-idempotent
                                      ; toℕ-fromℕ≤)
open import Data.Nat using (ℕ ; _+_ ; zero ; suc ; _≤_ ; _⊔_ ; _≤″_ ; _<_ ; s≤s ; z≤n ; _≤?_ ; ≤-pred)
open import Data.Nat.Properties using (m≤m⊔n ; n≤m⊔n ; ≤⇒≤″ ; +-comm ; +-assoc
                                      ; n≤m+n ; ≤-trans ; +-suc ; n≤1+n ; ≰⇒> ; ≤-reflexive ; ≤-step
                                      ; ≤-antisym ; ≰⇒≥ ; ≤-refl)
open import Data.Product  
open import Data.Empty
open import Data.Sum
open import Relation.Nullary
open import Data.List using (List ; [] ; _∷_ ; tabulate ; lookup ; filter ; length )
open import Data.List.Properties using (∷-injective ; ∷-injectiveˡ ; length-tabulate ; lookup-tabulate)
import Function as F

open import LTL.Core
open import LTL.Stateless hiding (_⇒_)




-- ⟶ᶠ

lemma-15 : {PA PB : BSet {ℓ} A} → ⊨ ((Cl PA ⟶ᶠ Cl PB) ⟶ (Cl PA ⟶ Cl PB))
lemma-15 {PA} {PB} a pimpl (sq , sq∈PA , lm) = h4  where
  h1 = Cls.lemma-10 a sq lm
  f  = proj₁ h1
  rl = proj₁ (proj₂ h1)
  eq = proj₂ (proj₂ h1)
  ssq = subSeq sq f rl
  h2 = λ m → pimpl ((ssq m) , Cls.lemma-11 PA (ssq m) (sq∈PA (f m)) , eq m)
  nsq = λ m → proj₁ (h2 m)
  neq = λ m → proj₂ (proj₂ (h2 m))
  nsqs∈ᶠⁱPB : (nsq stoSeqᶠⁱ) s∈ᶠⁱ PB
  nsqs∈ᶠⁱPB m = Cls.lemma-13 (nsq m) (proj₁ (proj₂ (h2 m))) m
  h3 : Limitᶠⁱ a (nsq stoSeqᶠⁱ)
  h3 _ = neq _
  h4 = Cls.lemma-19 a (nsq stoSeqᶠⁱ) h3 nsqs∈ᶠⁱPB

-- ⟶ᶠ


lemma-23 : {PA PB : BSet {ℓ} A} → ⊨ ((PA ⟶ᶠ⁺ PB) ⟶ (PA ⟶ᶠ PB))
lemma-23 {PA} {PB} a f x = Cp.lemma-3 a {PB} (n≤1+n _) (f x)

-- -▹ 

lemma-16 : {PA PB : BSet {ℓ} A} → ⊨ ((PA -▹ PB) ≣ ((Cl PA -▹ Cl PB) & (PA ⟶ PB)))
lemma-16 {PA} {PB} a = h1 , h2 where
  h1 : ((PA -▹ PB) ⟶ ((Cl PA -▹ Cl PB) & (PA ⟶ PB))) a
  h1 (impl , pimpl) = (h11 , h12) , impl where
    h11 : (Cl PA ⟶ Cl PB) a
    h11 (sq , sq∈PA , lm)
      = nsq , nsq∈PB , h115 where
      h111 = Cls.lemma-10 a sq lm
      f = proj₁ h111
      rl = proj₁ (proj₂ h111)
      sbsq = subSeq sq f rl
      eq = proj₂ (proj₂ h111)
      h112 = Cls.lemma-9 a sq lm f rl
      h113 = λ m → pimpl ((sbsq m) , (sq∈PA (f m)) , eq m) 
      nsq : Seq A
      nsq m = proj₁ (h113 m)
      nsq∈PB : nsq s∈ PB
      nsq∈PB m = proj₁ (proj₂ (h113 m))
      nsqeq : (m : ℕ) → [ (nsq m) ᵖ∥ m ≡ᶠ a ᵖ∥ m ]∥
      nsqeq m = proj₂ (proj₂ (h113 m))
      h114 = Cls.lemma-7 sbsq nsq λ k fn → P.trans (eq k fn) (P.sym (nsqeq k fn))
      h115 = Cls.lemma-6 a {sbsq} {nsq} h112 h114
    h12 : (∀{m} → (a ᵖ∥ m) ∈ᶠ (Cl PA) → (a ᵖ∥ m) ∈ᶠ (Cl PB))
    h12 {m} a∈ClPA = Cls.lemma-12 PB a h122 where
      h121 = Cls.lemma-14 {P = PA} a∈ClPA
      h122 = pimpl h121
  h2 : (((Cl PA -▹ Cl PB) & (PA ⟶ PB)) ⟶ (PA -▹ PB)) a
  h2 ((cimpl , pimpl) , impl) = impl , (λ x → Cls.lemma-14 (pimpl (Cls.lemma-12 PA a x)))



-- -▹⁺

-- TODO The proof is identical with lemma-3 . Maybe generalize both into one.
lemma-17 : {PA PB : BSet {ℓ} A} → ⊨ ((PA -▹⁺ PB) ≣ ((Cl PA -▹⁺ Cl PB) & (PA ⟶ PB)))
lemma-17 {PA} {PB} a = h1 , h2 where
  h1 : ((PA -▹⁺ PB) ⟶ ((Cl PA -▹⁺ Cl PB) & (PA ⟶ PB))) a
  h1 (impl , pimpl) = (h11 , h12) , impl where
    h11 : (Cl PA ⟶ Cl PB) a
    h11 (sq , sq∈PA , lm)
      = nsq , nsq∈PB , h115 where
      h111 = Cls.lemma-10 a sq lm
      f = proj₁ h111
      rl = proj₁ (proj₂ h111)
      sbsq = subSeq sq f rl
      eq = proj₂ (proj₂ h111)
      h112 = Cls.lemma-9 a sq lm f rl
      h113 = λ m → pimpl ((sbsq m) , (sq∈PA (f m)) , eq m) 
      nsq : Seq A
      nsq m = proj₁ (h113 m)
      nsq∈PB : nsq s∈ PB
      nsq∈PB m = proj₁ (proj₂ (h113 m))
      nsqeq : (m : ℕ) → [ (nsq m) ᵖ∥ m ≡ᶠ a ᵖ∥ m ]∥
      nsqeq m = Cp.lemma-2 (nsq m) a (n≤1+n m) (proj₂ (proj₂ (h113 m)))
      h114 = Cls.lemma-7 sbsq nsq λ k fn → P.trans (eq k fn) (P.sym (nsqeq k fn))
      h115 = Cls.lemma-6 a {sbsq} {nsq} h112 h114
    h12 : (∀{m} → (a ᵖ∥ m) ∈ᶠ (Cl PA) → (a ᵖ∥ (suc m)) ∈ᶠ (Cl PB))
    h12 {m} a∈ClPA = Cls.lemma-12 PB a h122 where
      h121 = Cls.lemma-14 {P = PA} a∈ClPA
      h122 = pimpl h121
  h2 : (((Cl PA -▹⁺ Cl PB) & (PA ⟶ PB)) ⟶ (PA -▹⁺ PB)) a
  h2 ((cimpl , pimpl) , impl) = impl , (λ x → Cls.lemma-14 (pimpl (Cls.lemma-12 PA a x)))


-- This depends on the decidability of property PB on finite prefixes
-- which must be decidable if the each element is decidable. TODO
-- It also requires that PA is non-empty.
lemma-18 : {PA PB : BSet {ℓ} A}
           → (d : ∀ m (a : A ʷ∥ m) → Dec (a ∈ᶠ PB))
           → P¬∅ PA
           → ⊨ ((Cl PA -▹⁺ PB) ≣ ((PB -▹ Cl PA) -▹ PB))
lemma-18 {PA} {PB} d (s¬∅ , s¬∅∈PA) a = h1 , h2 where
  h1 : ((Cl PA -▹⁺ PB) ⟶ ((PB -▹ Cl PA) -▹ PB)) a
  h1 (impl , pimpl) = h11 , h12 where
    h11 : ((PB -▹ Cl PA) ⟶ PB) a
    h11 (im , pim) = impl h113 where
      h111 : (a toSeqᶠⁱ) s∈ᶠⁱ (Cl PA)
      h111 zero = Cp.lemma-1 a (s¬∅ , (Cls.lemma-11 PA s¬∅ s¬∅∈PA))
      h111 (suc m) = pim (pimpl (h111 m))
      h112 : (a toSeqᶠⁱ) s∈ᶠⁱ PA
      h112 n = Cls.lemma-14 (h111 n)
      h114 : Limit a (λ m → proj₁ (h112 m))
      h114 m = m , λ k → Cp.lemma-2 (proj₁ (h112 (k + m))) a (n≤m+n k m) (proj₂ (proj₂ (h112 (k + m))))
      h113 : a ∈ Cl PA
      h113 = (λ m → proj₁ (h112 m)) , (λ k → proj₁ (proj₂ (h112 k))) , h114
    h12 : ((PB -▹ Cl PA) ⟶ᶠ PB) a
    h12 {zero} (s , s∈-> , eq) = Cp.lemma-3 a _≤_.z≤n h122 where
      h121 = Cp.lemma-1 a {Cl PA} (s¬∅ , (Cls.lemma-11 PA s¬∅ s¬∅∈PA))
      h122 = pimpl h121
    h12 {suc k} (s , s∈-> , eq) = pimpl h124 where
      h121 = h12 {k} (s , s∈-> , Cp.lemma-2 s a (n≤1+n k) eq)
      h122 = Cp.lemma-20 a s k h121 λ fn → P.sym (Cp.lemma-2 s a (n≤1+n k) eq fn)
      h123 = (proj₂ s∈->) h122
      h124 = Cp.lemma-20 s a k h123 (Cp.lemma-2 s a (n≤1+n k) eq)
  h2 : (((PB -▹ Cl PA) -▹ PB) ⟶ (Cl PA -▹⁺ PB)) a
  h2 (impl , pimpl) = h21 , h22 where
    h21 : (Cl PA ⟶ PB) a
    h21 a∈ClPA = impl ((λ _ → a∈ClPA) , λ _ → a , a∈ClPA , λ fn → P.refl)
    h22 : (Cl PA ⟶ᶠ⁺ PB) a
    h22 {m} a∈ᶠClPA@(s , s∈∁lPA , eq)
      = F.case (d (suc m) (a ᵖ∥ (suc m))) of
          λ { (yes p) → p
          ; (no ¬p) → ⊥-elim (¬p (pimpl (a , ((h221 ¬p
                             , h222 ¬p) , λ fn → P.refl))))} where
        h221 : ¬ (a ᵖ∥ (suc m) ∈ᶠ PB) → (PB ⟶ Cl PA) a
        h221 ¬p x = ⊥-elim (¬p (a , x , (λ x₁ → P.refl)))
        h222 : ¬ (a ᵖ∥ (suc m) ∈ᶠ PB) → (PB ⟶ᶠ Cl PA) a
        h222 ¬p {k} x = F.case (k ≤? m) of
          λ { (yes q) → Cp.lemma-3 a q a∈ᶠClPA
            ; (no ¬q) → let e = ≰⇒> ¬q
                        in ⊥-elim (¬p (Cp.lemma-3 a e x))}


lemma-21 : {PA PB : BSet {ℓ} A}
           → ⊨ ((Cl PA -▹ Cl PB) ≣ (Cl (Cl PA -▹ Cl PB)))
lemma-21 {PA} {PB} a = h1 , h2 where
  h1 : ((Cl PA -▹ Cl PB) ⟶ (Cl (Cl PA -▹ Cl PB))) a
  h1 = Cls.lemma-11 (Cl PA -▹ Cl PB) a
  h2 : ((Cl (Cl PA -▹ Cl PB)) ⟶ (Cl PA -▹ Cl PB)) a
  h2 (s , s∈-▹ , lm) = h22 , h21 where
    h21 : (Cl PA ⟶ᶠ Cl PB) a
    h21 {k} x = h214 where
      h211 = lm k
      n = proj₁ h211
      eq = (proj₂ h211) 0
      h212 = Cp.lemma-20 a (s n) k x (Cp.symᶠ eq)
      h213 = (proj₂ (s∈-▹ _)) h212
      h214 = Cp.lemma-20 (s n) a k h213 eq
    h22 : (Cl PA ⟶ Cl PB) a
    h22 = lemma-15 {PA} {PB} a h21

lemma-22 : {PA PB : BSet {ℓ} A}
           → ⊨ ((Cl PA -▹⁺ Cl PB) ≣ (Cl (Cl PA -▹⁺ Cl PB)))
lemma-22 {PA} {PB} a = h1 , h2 where
  h1 : ((Cl PA -▹⁺ Cl PB) ⟶ (Cl (Cl PA -▹⁺ Cl PB))) a
  h1 = Cls.lemma-11 (Cl PA -▹⁺ Cl PB) a
  h2 : ((Cl (Cl PA -▹⁺ Cl PB)) ⟶ (Cl PA -▹⁺ Cl PB)) a
  h2  (s , s∈-▹ , lm) = h22 , h21 where
    h21 : (Cl PA ⟶ᶠ⁺ Cl PB) a
    h21 {k} x = h214 where
      h211 = lm (suc k)
      n = proj₁ h211
      eq = (proj₂ h211) 0
      h212 = Cp.lemma-20 a (s n) k x (Cp.lemma-2 a (s n) (n≤1+n _) (Cp.symᶠ eq))
      h213 = (proj₂ (s∈-▹ _)) h212
      h214 = Cp.lemma-20 (s n) a (suc k) h213 eq
    h22 : (Cl PA ⟶ Cl PB) a
    h22 = lemma-15 {PA} {PB} a (lemma-23 {Cl PA} {Cl PB} a h21)

lemma-24 : {PA PB PC : BSet {ℓ} A}
           → ⊨ (Cl PC ⟶ (Cl PA -▹ Cl PB)) → ⊨ ((Cl PC & Cl PA) ⟶ Cl PB)
lemma-24 {PA} {PB} {PC} f a (x , y) = proj₁ (f a x) y

-- Cp.lemma-25 : {PA PB PC : BSet {ℓ} A}
--            → ⊨ ((Cl PC & Cl PA) ⟶ Cl PB) → ⊨ (Cl PC ⟶ (Cl PA -▹ Cl PB)) 
-- Cp.lemma-25 {PA} {PB} {PC} f a x = h1 , h2 where
--   h1 : (Cl PA ⟶ Cl PB) a
--   h1 y = f a (x , y)
--   h2 : (Cl PA ⟶ᶠ Cl PB) a
--   h2 (s , s∈ClPA , eq) = {!!} 
