module TLA.CoreP where

open import TLA.Core

import Level as L
import Relation.Binary.PropositionalEquality as P
open import Data.Fin using (Fin ; toℕ ; inject≤)
open import Data.Fin.Properties using (toℕ-inject≤)
open import Data.Nat using (ℕ ; _+_ ; zero ; suc ; _≤_ ; _⊔_ ; _≤″_ ; _<_ ; s≤s)
open import Data.Nat.Properties using (m≤m⊔n ; n≤m⊔n ; ≤⇒≤″ ; +-comm ; +-assoc ; n≤m+n ; ≤-trans ; +-suc ; n≤1+n)
open import Data.Product
open import LTL.Core
open import LTL.Stateless hiding (_⇒_)

module _ {ℓ} where

-- PREFIXES

-- If we have proved equality of prefixes at length m , then equality is true for smaller prefixes.
  lemma-6 : {A : Set ℓ} → (a b : A ʷ) → ∀ {m n} → n ≤ m
            → [ prefix a m ≡ᶠ prefix b m ]∥ → [ prefix a n ≡ᶠ prefix b n ]∥
  lemma-6 a b nltm rst fn = q where
    w = rst (inject≤ fn nltm)
    q = P.subst (λ z → (a ≡ b) z) (toℕ-inject≤ fn nltm) w

-- LIMITS

-- The constant seqeuence of an element "a" converges to "a".
  lemma-1 : {A : Set ℓ} → (a : A ʷ) → Limit {ℓ} a ⟨ a ⟩
  lemma-1 = λ a m → m , (λ x x₁ → P.refl)

-- Two sequences that converge to the same limit also converge to each other.
  lemma-7 : {A : Set ℓ} → (lm : A ʷ) → {seqa seqb : Seq A} → Limit lm seqa → Limit lm seqb → LimitSq seqa seqb
  lemma-7 lp {seqa} {seqb} lma lmb m
    = max , h1 where
        na = proj₁ (lma m)
        eqa = proj₂ (lma m)
        nb = proj₁ (lmb m)
        eqb = proj₂ (lmb m)
        max = na ⊔ nb
        h1 : ∀ k → [ (prefix (seqa (k + max)) m) ≡ᶠ (prefix (seqb (k + max)) m) ]∥
        h1 k = P.subst₂ (λ a b → [ (prefix (seqa a) m) ≡ᶠ (prefix (seqb b) m) ]∥)
                        (P.sym (proj₂ h11)) (P.sym (proj₂ h12)) (h13 (proj₁ h11) (proj₁ h12)) where
          h11 : ∃ λ z → k + max P.≡ z + na
          h11 = let q = m≤m⊔n na nb
                    w = P.sym (P.trans (+-comm _ na) (_≤″_.proof (≤⇒≤″ q)))
                in k + _ , P.trans (P.cong (λ z → k + z) w) (P.sym (+-assoc k _ na))
          h12 : ∃ λ z → k + max P.≡ z + nb
          h12 = let q = n≤m⊔n na nb
                    w = P.sym (P.trans (+-comm _ nb) (_≤″_.proof (≤⇒≤″ q)))
                in k + _ , P.trans (P.cong (λ z → k + z) w) (P.sym (+-assoc k _ nb))
          h13 : ∀ z1 z2 → [ (prefix (seqa (z1 + na)) m) ≡ᶠ (prefix (seqb (z2 + nb)) m) ]∥
          h13 z1 z2 fn = P.trans (eqa z1 fn) (P.sym (eqb z2 fn))

-- If one sequence converges to a point a and another sequence, that other sequence
-- then converges to the same limit.
  lemma-8 : {A : Set ℓ} → (lm : A ʷ) → {seqa seqb : Seq A} → Limit lm seqa → LimitSq seqa seqb → Limit lm seqb
  lemma-8 lm {seqa} {seqb} lma lmsq m
    = max , h1 where
        na = proj₁ (lma m)
        eqa = proj₂ (lma m)
        nsq = proj₁ (lmsq m)
        eqsq = proj₂ (lmsq m)
        max = na ⊔ nsq
        h1 : ∀ k → [ (prefix (seqb (k + max)) m) ≡ᶠ (prefix lm m) ]∥
        h1 k fn = P.trans (P.cong (λ z → prefix (seqb z) m fn) (proj₂ h12)) (h13 fn) where
          h11 : ∃ λ z → k + max P.≡ z + na
          h11 = let q = m≤m⊔n na nsq
                    w = P.sym (P.trans (+-comm _ na) (_≤″_.proof (≤⇒≤″ q)))
                in k + _ , P.trans (P.cong (λ z → k + z) w) (P.sym (+-assoc k _ na))
          h12 : ∃ λ z → k + max P.≡ z + nsq
          h12 = let q = n≤m⊔n na nsq
                    w = P.sym (P.trans (+-comm _ nsq) (_≤″_.proof (≤⇒≤″ q)))
                in k + _ , P.trans (P.cong (λ z → k + z) w) (P.sym (+-assoc k _ nsq))
          h13 : [ (prefix (seqb ((proj₁ h12) + nsq)) m) ≡ᶠ (prefix lm m) ]∥
          h13 fn = P.trans (P.sym (eqsq (proj₁ h12) fn)) (P.trans h131 (eqa (proj₁ h11) fn)) where
            h131 : _
            h131 = P.cong (λ z → seqa z (toℕ fn)) (P.trans (P.sym (proj₂ h12)) (proj₂ h11))

-- The condition of this lemma is always possible (by taking a subsequence)
-- and it simplifies the proofs considerably.
  lemma-9 : {A : Set ℓ} → (seqa seqb : Seq A)
            → (∀ k → [ prefix (seqa k) k ≡ᶠ prefix (seqb k) k ]∥)
            → LimitSq seqa seqb
  lemma-9 seqa seqb f m = m , λ k → lemma-6 (seqa (k + m)) (seqb (k + m)) (n≤m+n k m) (f (k + m))

-- Add this to the standard library.
  lemma-11 : (f : ℕ → ℕ) → (rl : ∀ k → f k < f (suc k)) → ∀ m → ∃ λ n → ∀ k → m ≤ f (k + n) 
  lemma-11 f rl zero = zero , (λ k → _≤_.z≤n)
  lemma-11 f rl (suc m)
    = let n , eq = lemma-11 f rl m
      in suc n , λ k → let q = +-suc k n
                       in ≤-trans (s≤s (eq k)) (P.subst (λ z → suc (f (k + n)) ≤ f z) (P.sym q) (rl (k + n))) 


-- Add this to the standard library.
  lemma-13 : (f : ℕ → ℕ) → (rl : ∀ k → f k < f (suc k)) → ∀ k → k ≤ f k
  lemma-13 f rl zero = _≤_.z≤n
  lemma-13 f rl (suc k) = ≤-trans (s≤s (lemma-13 f rl k)) (rl k)

-- If a sequence converges to a limit, then all this subsequences also converge to the same limit.
  lemma-10 : {A : Set ℓ} → (lm : A ʷ) → (seqa : Seq A) → Limit lm seqa
             → (f : ℕ → ℕ) → (rl : ∀ k → f k < f (suc k)) → Limit lm (subSeq seqa f rl)
  lemma-10 lp seqa lm f rl m = nf , λ k → let e = P.trans (+-comm _ n) (_≤″_.proof (≤⇒≤″ (eqf k)))
                                          in P.subst (λ z → [ prefix (seqa z) m ≡ᶠ prefix lp m ]∥) e (eq _) where
    n = proj₁ (lm m)
    eq = proj₂ (lm m)
    h1 = lemma-11 f rl n
    nf = proj₁ h1
    eqf = proj₂ h1
    
-- There exists a subsequence that respects the conditions of lemma-9
  lemma-12 : {A : Set ℓ} → (lm : A ʷ) → (seqa : Seq A) → Limit lm seqa
             → ∃ λ f → Σ (∀ k → f k < f (suc k)) (λ rl → let sq = subSeq seqa f rl
                                                         in (∀ k → [ prefix (sq k) k ≡ᶠ prefix lm k ]∥))
  lemma-12 lp seqa lm
    = f , rl , (λ { zero → proj₂ (lm zero) 0
                  ; (suc k) → h1 k}) where
    f : ℕ → ℕ
    f zero = n where
      n = proj₁ (lm 0)
    f (suc m) = (suc (f m)) ⊔ n where
      n = proj₁ (lm (suc m))
    rl : ∀ k → f k < f (suc k)
    rl k = m≤m⊔n (suc (f k)) (proj₁ (lm (suc k)))
    h1 : (k : ℕ) → [ prefix (subSeq seqa f rl (suc k)) (suc k) ≡ᶠ prefix lp (suc k) ]∥
    h1 k = h12 h13 where
      n = proj₁ (lm (suc k))
      h11 = P.trans (+-comm _ n) (_≤″_.proof (≤⇒≤″ (n≤m⊔n (suc (f k)) n)))
      h12 = P.subst (λ z → [ prefix (seqa z) (suc k) ≡ᶠ prefix lp (suc k) ]∥) h11
      h13 = (proj₂ (lm (suc k))) _
    
-- Closures

  lemma-2 : {A : Set ℓ} → (P : Property A) → Tautology (P ⟶ Cl P)
  lemma-2 P a a∈P = ⟨ a ⟩ , ⟨ a∈P ⟩ , lemma-1 a

  lemma-14 : {A : Set ℓ} → (P : Property A) → Tautology (P ⟶ᶠ Cl P)
  lemma-14 P a (sa , sa∈P , eq) = sa , (lemma-2 P sa sa∈P) , eq
  
  lemma-5 : ∀{A} → {P : Property {ℓ} A} → (a : A ʷ) → a ∈ Cl P → ∀ m → prefix a m ∈ᶠ P
  lemma-5 a (seq , seq∈P , lm) m
    = let n , eq = lm m
      in seq n , seq∈P n , eq zero

  lemma-4 : ∀{A} → {P : Property {ℓ} A} → ∀{m} → {a : A ʷ∥ m} → a ∈ᶠ Cl P → a ∈ᶠ P
  lemma-4 {_} {P} {m} {a} (s , s∈ClP , eq)
    = let (sp , sp∈P , eqP) = lemma-5 {_} {P} s s∈ClP m
      in sp , sp∈P , λ fn → P.trans (eqP fn) (eq fn)


-- -▹ 

  lemma-3 : ∀{A} → {PA PB : Property {ℓ} A} → Tautology ((PA -▹ PB) ≣ ((Cl PA -▹ Cl PB) & (PA ⟶ PB)))
  lemma-3 {A} {PA} {PB} a = h1 , h2 where
    h1 : ((PA -▹ PB) ⟶ ((Cl PA -▹ Cl PB) & (PA ⟶ PB))) a
    h1 (impl , pimpl) = (h11 , h12) , impl where
      h11 : (Cl PA ⟶ Cl PB) a
      h11 (sq , sq∈PA , lm)
        = nsq , nsq∈PB , h115 where
        h111 = lemma-12 a sq lm
        f = proj₁ h111
        rl = proj₁ (proj₂ h111)
        sbsq = subSeq sq f rl
        eq = proj₂ (proj₂ h111)
        h112 = lemma-10 a sq lm f rl
        h113 = λ m → pimpl ((sbsq m) , (sq∈PA (f m)) , eq m) 
        nsq : Seq A
        nsq m = proj₁ (h113 m)
        nsq∈PB : nsq s∈ PB
        nsq∈PB m = proj₁ (proj₂ (h113 m))
        nsqeq : (m : ℕ) → [ prefix (nsq m) m ≡ᶠ prefix a m ]∥
        nsqeq m = proj₂ (proj₂ (h113 m))
        h114 = lemma-9 sbsq nsq λ k fn → P.trans (eq k fn) (P.sym (nsqeq k fn))
        h115 = lemma-8 a {sbsq} {nsq} h112 h114
      h12 : (∀{m} → (prefix a m) ∈ᶠ (Cl PA) → (prefix a m) ∈ᶠ (Cl PB))
      h12 {m} a∈ClPA = lemma-14 PB a h122 where
        h121 = lemma-4 {P = PA} a∈ClPA
        h122 = pimpl h121
    h2 : (((Cl PA -▹ Cl PB) & (PA ⟶ PB)) ⟶ (PA -▹ PB)) a
    h2 ((cimpl , pimpl) , impl) = impl , (λ x → lemma-4 (pimpl (lemma-14 PA a x)))



-- -▹⁺

-- TODO The proof is identical with lemma-3 . Maybe generalize both into one.
  lemma-15 : ∀{A} → {PA PB : Property {ℓ} A} → Tautology ((PA -▹⁺ PB) ≣ ((Cl PA -▹⁺ Cl PB) & (PA ⟶ PB)))
  lemma-15 {A} {PA} {PB} a = h1 , h2 where
    h1 : ((PA -▹⁺ PB) ⟶ ((Cl PA -▹⁺ Cl PB) & (PA ⟶ PB))) a
    h1 (impl , pimpl) = (h11 , h12) , impl where
      h11 : (Cl PA ⟶ Cl PB) a
      h11 (sq , sq∈PA , lm)
        = nsq , nsq∈PB , h115 where
        h111 = lemma-12 a sq lm
        f = proj₁ h111
        rl = proj₁ (proj₂ h111)
        sbsq = subSeq sq f rl
        eq = proj₂ (proj₂ h111)
        h112 = lemma-10 a sq lm f rl
        h113 = λ m → pimpl ((sbsq m) , (sq∈PA (f m)) , eq m) 
        nsq : Seq A
        nsq m = proj₁ (h113 m)
        nsq∈PB : nsq s∈ PB
        nsq∈PB m = proj₁ (proj₂ (h113 m))
        nsqeq : (m : ℕ) → [ prefix (nsq m) m ≡ᶠ prefix a m ]∥
        nsqeq m = lemma-6 (nsq m) a (n≤1+n m) (proj₂ (proj₂ (h113 m)))
        h114 = lemma-9 sbsq nsq λ k fn → P.trans (eq k fn) (P.sym (nsqeq k fn))
        h115 = lemma-8 a {sbsq} {nsq} h112 h114
      h12 : (∀{m} → (prefix a m) ∈ᶠ (Cl PA) → (prefix a (suc m)) ∈ᶠ (Cl PB))
      h12 {m} a∈ClPA = lemma-14 PB a h122 where
        h121 = lemma-4 {P = PA} a∈ClPA
        h122 = pimpl h121
    h2 : (((Cl PA -▹⁺ Cl PB) & (PA ⟶ PB)) ⟶ (PA -▹⁺ PB)) a
    h2 ((cimpl , pimpl) , impl) = impl , (λ x → lemma-4 (pimpl (lemma-14 PA a x)))



  lemma-16 : ∀{A} → {PA PB : Property {ℓ} A} → Tautology ((Cl PA -▹⁺ PB) ≣ ((PB -▹ Cl PA) -▹ PB))
  lemma-16 {A} {PA} {PB} a = {!!} where
    h1 : ((Cl PA -▹⁺ PB) ⟶ ((PB -▹ Cl PA) -▹ PB)) a
    h1 = {!!}
    h2 : (((PB -▹ Cl PA) -▹ PB) ⟶ (Cl PA -▹⁺ PB)) a
    h2 = {!!}
