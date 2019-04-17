module TLA.Closure {ℓ} {A : Set ℓ} where

open import TLA.Core
import TLA.Common as C
import TLA.CoreP {ℓ} {A} as Cp

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


-- LIMITS

-- The constant seqeuence of an element "a" converges to "a".
lemma-4 : {A : Set ℓ} → (a : A ʷ) → Limit {ℓ} a ⟨ a ⟩
lemma-4 = λ a m → m , (λ x x₁ → P.refl)

-- Two sequences that converge to the same limit also converge to each other.
lemma-5 : {A : Set ℓ} → (lm : A ʷ) → {seqa seqb : Seq A} → Limit lm seqa → Limit lm seqb → LimitSq seqa seqb
lemma-5 lp {seqa} {seqb} lma lmb m
  = max , h1 where
      na = proj₁ (lma m)
      eqa = proj₂ (lma m)
      nb = proj₁ (lmb m)
      eqb = proj₂ (lmb m)
      max = na ⊔ nb
      h1 : ∀ k → [ ((seqa (k + max)) ᵖ∥ m) ≡ᶠ ((seqb (k + max)) ᵖ∥ m) ]∥
      h1 k = P.subst₂ (λ a b → [ ((seqa a) ᵖ∥ m) ≡ᶠ ((seqb b) ᵖ∥ m) ]∥)
                      (P.sym (proj₂ h11)) (P.sym (proj₂ h12)) (h13 (proj₁ h11) (proj₁ h12)) where
        h11 : ∃ λ z → k + max P.≡ z + na
        h11 = let q = m≤m⊔n na nb
                  w = P.sym (P.trans (+-comm _ na) (_≤″_.proof (≤⇒≤″ q)))
              in k + _ , P.trans (P.cong (λ z → k + z) w) (P.sym (+-assoc k _ na))
        h12 : ∃ λ z → k + max P.≡ z + nb
        h12 = let q = n≤m⊔n na nb
                  w = P.sym (P.trans (+-comm _ nb) (_≤″_.proof (≤⇒≤″ q)))
              in k + _ , P.trans (P.cong (λ z → k + z) w) (P.sym (+-assoc k _ nb))
        h13 : ∀ z1 z2 → [ ((seqa (z1 + na)) ᵖ∥ m) ≡ᶠ ((seqb (z2 + nb)) ᵖ∥ m) ]∥
        h13 z1 z2 fn = P.trans (eqa z1 fn) (P.sym (eqb z2 fn))

-- If one sequence converges to a point a and another sequence, that other sequence
-- then converges to the same limit.
lemma-6 : {A : Set ℓ} → (lm : A ʷ) → {seqa seqb : Seq A} → Limit lm seqa → LimitSq seqa seqb → Limit lm seqb
lemma-6 lm {seqa} {seqb} lma lmsq m
  = max , h1 where
      na = proj₁ (lma m)
      eqa = proj₂ (lma m)
      nsq = proj₁ (lmsq m)
      eqsq = proj₂ (lmsq m)
      max = na ⊔ nsq
      h1 : ∀ k → [ ((seqb (k + max)) ᵖ∥ m) ≡ᶠ (lm ᵖ∥ m) ]∥
      h1 k fn = P.trans (P.cong (λ z → ((seqb z) ᵖ∥ m) fn) (proj₂ h12)) (h13 fn) where
        h11 : ∃ λ z → k + max P.≡ z + na
        h11 = let q = m≤m⊔n na nsq
                  w = P.sym (P.trans (+-comm _ na) (_≤″_.proof (≤⇒≤″ q)))
              in k + _ , P.trans (P.cong (λ z → k + z) w) (P.sym (+-assoc k _ na))
        h12 : ∃ λ z → k + max P.≡ z + nsq
        h12 = let q = n≤m⊔n na nsq
                  w = P.sym (P.trans (+-comm _ nsq) (_≤″_.proof (≤⇒≤″ q)))
              in k + _ , P.trans (P.cong (λ z → k + z) w) (P.sym (+-assoc k _ nsq))
        h13 : [ ((seqb ((proj₁ h12) + nsq)) ᵖ∥ m) ≡ᶠ (lm ᵖ∥ m) ]∥
        h13 fn = P.trans (P.sym (eqsq (proj₁ h12) fn)) (P.trans h131 (eqa (proj₁ h11) fn)) where
          h131 : _
          h131 = P.cong (λ z → seqa z (toℕ fn)) (P.trans (P.sym (proj₂ h12)) (proj₂ h11))

-- The condition of this lemma is always possible (by taking a subsequence)
-- and it simplifies the proofs considerably.
lemma-7 : (seqa seqb : Seq A)
          → LimitSqᶠⁱ (seqa  stoSeqᶠⁱ) (seqb  stoSeqᶠⁱ)
          → LimitSq seqa seqb
lemma-7 seqa seqb f m = m , λ k → Cp.lemma-2 (seqa (k + m)) (seqb (k + m)) (n≤m+n k m) (f (k + m))

lemma-8 : (seq : Seq A) → (a : A ʷ)
          → Limitᶠⁱ a (seq  stoSeqᶠⁱ)
          → Limit a seq
lemma-8 seq a f m = m , λ k → Cp.lemma-2 (seq (k + m)) a (n≤m+n k m) (f (k + m))


-- If a sequence converges to a limit, then all this subsequences also converge to the same limit.
lemma-9 : {A : Set ℓ} → (lm : A ʷ) → (seqa : Seq A) → Limit lm seqa
           → (f : ℕ → ℕ) → (rl : ∀ k → f k < f (suc k)) → Limit lm (subSeq seqa f rl)
lemma-9 lp seqa lm f rl m = nf , λ k → let e = P.trans (+-comm _ n) (_≤″_.proof (≤⇒≤″ (eqf k)))
                                        in P.subst (λ z → [ (seqa z) ᵖ∥ m ≡ᶠ lp ᵖ∥ m ]∥) e (eq _) where
  n = proj₁ (lm m)
  eq = proj₂ (lm m)
  h1 = C.lemma-1 f rl n
  nf = proj₁ h1
  eqf = proj₂ h1
  
-- There exists a subsequence that respects the conditions of lemma-7
lemma-10 : {A : Set ℓ} → (lm : A ʷ) → (seqa : Seq A) → Limit lm seqa
           → ∃ λ f → Σ (∀ k → f k < f (suc k)) (λ rl → let sq = subSeq seqa f rl
                                                       in Limitᶠⁱ lm (sq stoSeqᶠⁱ))
lemma-10 lp seqa lm
  = f , rl , (λ { zero → proj₂ (lm zero) 0
                ; (suc k) → h1 k}) where
  f : ℕ → ℕ
  f zero = n where
    n = proj₁ (lm 0)
  f (suc m) = (suc (f m)) ⊔ n where
    n = proj₁ (lm (suc m))
  rl : ∀ k → f k < f (suc k)
  rl k = m≤m⊔n (suc (f k)) (proj₁ (lm (suc k)))
  h1 : (k : ℕ) → [ (subSeq seqa f rl (suc k)) ᵖ∥ (suc k) ≡ᶠ lp ᵖ∥ (suc k) ]∥
  h1 k = h12 h13 where
    n = proj₁ (lm (suc k))
    h11 = P.trans (+-comm _ n) (_≤″_.proof (≤⇒≤″ (n≤m⊔n (suc (f k)) n)))
    h12 = P.subst (λ z → [ (seqa z) ᵖ∥ (suc k) ≡ᶠ lp ᵖ∥ (suc k) ]∥) h11
    h13 = (proj₂ (lm (suc k))) _
  
-- Closures

lemma-11 : {A : Set ℓ} → (P : BSet A) → ⊨ (P ⟶ Cl P)
lemma-11 P a a∈P = ⟨ a ⟩ , ⟨ a∈P ⟩ , lemma-4 a

lemma-12 : {A : Set ℓ} → (P : BSet A) → ⊨ (P ⟶ᶠ Cl P)
lemma-12 P a (sa , sa∈P , eq) = sa , (lemma-11 P sa sa∈P) , eq

lemma-13 : ∀{A} → {P : BSet {ℓ} A} → (a : A ʷ) → a ∈ Cl P → ∀ m → a ᵖ∥ m ∈ᶠ P
lemma-13 a (seq , seq∈P , lm) m
  = let n , eq = lm m
    in seq n , seq∈P n , eq zero

lemma-14 : ∀{A} → {P : BSet {ℓ} A} → ∀{m} → {a : A ʷ∥ m} → a ∈ᶠ Cl P → a ∈ᶠ P
lemma-14 {_} {P} {m} {a} (s , s∈ClP , eq)
  = let (sp , sp∈P , eqP) = lemma-13 {_} {P} s s∈ClP m
    in sp , sp∈P , λ fn → P.trans (eqP fn) (eq fn)


lemma-19 : {P : BSet {ℓ} A} → (a : A ʷ) → (seq : Seqᶠⁱ A)
           → Limitᶠⁱ a seq → seq s∈ᶠⁱ P → a ∈ Cl P
lemma-19 a seq lm sq∈ᶠⁱP = nsq , nsq∈P , lemma-8 nsq a h1 where
  nsq = λ m → proj₁ (sq∈ᶠⁱP m)
  nsq∈P = λ m → proj₁ (proj₂ (sq∈ᶠⁱP m))
  eq = λ m → proj₂ (proj₂ (sq∈ᶠⁱP m))
  h1 : Limitᶠⁱ a (nsq stoSeqᶠⁱ)
  h1 m fn = P.trans (eq m fn) (lm m fn)
