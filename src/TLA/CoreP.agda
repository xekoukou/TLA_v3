module TLA.CoreP where

open import TLA.Core
import TLA.Common as C

import Level as L
import Relation.Binary.PropositionalEquality as P
open import Data.Fin using (Fin ; toℕ ; inject≤)
open import Data.Fin.Properties using (toℕ-inject≤)
open import Data.Nat using (ℕ ; _+_ ; zero ; suc ; _≤_ ; _⊔_ ; _≤″_ ; _<_ ; s≤s ; _≤?_)
open import Data.Nat.Properties using (m≤m⊔n ; n≤m⊔n ; ≤⇒≤″ ; +-comm ; +-assoc
                                      ; n≤m+n ; ≤-trans ; +-suc ; n≤1+n ; ≰⇒> )
open import Data.Product  
open import Data.Empty
open import Relation.Nullary
open import Function

open import LTL.Core
open import LTL.Stateless hiding (_⇒_)

module _ {ℓ} where


-- Properties

  lemma-1 : {A : Set ℓ} → (a : A ʷ) → {P : Property A} → P¬∅ P → prefix a 0 ∈ᶠ P
  lemma-1 a (s , s∈P ) = s , s∈P , (λ ())


-- PREFIXES

-- If we have proved equality of prefixes at length m , then equality is true for smaller prefixes.
  lemma-2 : {A : Set ℓ} → (a b : A ʷ) → ∀ {m n} → n ≤ m
            → [ prefix a m ≡ᶠ prefix b m ]∥ → [ prefix a n ≡ᶠ prefix b n ]∥
  lemma-2 a b nltm rst fn = q where
    w = rst (inject≤ fn nltm)
    q = P.subst (λ z → (a ≡ b) z) (toℕ-inject≤ fn nltm) w

  lemma-3 : ∀{m n} → {A : Set ℓ} → (a : A ʷ) → {P : Property A} → n ≤ m
             → prefix a m ∈ᶠ P → prefix a n ∈ᶠ P
  lemma-3 a n≤m (s , s∈P , eq) = s , s∈P , (lemma-2 s a n≤m eq)

-- _∈ᶠ_

  lemma-20 : {A : Set ℓ} → (a b : A ʷ) → {P : Property A}
             → ∀ m → prefix a m ∈ᶠ P → [ prefix a m ≡ᶠ prefix b m ]∥
             → prefix b m ∈ᶠ P
  lemma-20 a b m pa∈ᶠP eq
    = (proj₁ pa∈ᶠP) , ((proj₁ (proj₂ pa∈ᶠP))
                      , λ fn → P.trans (proj₂ (proj₂ pa∈ᶠP) fn) (eq fn))

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
  lemma-6 : {A : Set ℓ} → (lm : A ʷ) → {seqa seqb : Seq A} → Limit lm seqa → LimitSq seqa seqb → Limit lm seqb
  lemma-6 lm {seqa} {seqb} lma lmsq m
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
  lemma-7 : {A : Set ℓ} → (seqa seqb : Seq A)
            → LimitSqᶠⁱ (seqa  stoSeqᶠⁱ) (seqb  stoSeqᶠⁱ)
            → LimitSq seqa seqb
  lemma-7 seqa seqb f m = m , λ k → lemma-2 (seqa (k + m)) (seqb (k + m)) (n≤m+n k m) (f (k + m))

  lemma-8 : {A : Set ℓ} → (seq : Seq A) → (a : A ʷ)
            → Limitᶠⁱ a (seq  stoSeqᶠⁱ)
            → Limit a seq
  lemma-8 seq a f m = m , λ k → lemma-2 (seq (k + m)) a (n≤m+n k m) (f (k + m))
  

-- If a sequence converges to a limit, then all this subsequences also converge to the same limit.
  lemma-9 : {A : Set ℓ} → (lm : A ʷ) → (seqa : Seq A) → Limit lm seqa
             → (f : ℕ → ℕ) → (rl : ∀ k → f k < f (suc k)) → Limit lm (subSeq seqa f rl)
  lemma-9 lp seqa lm f rl m = nf , λ k → let e = P.trans (+-comm _ n) (_≤″_.proof (≤⇒≤″ (eqf k)))
                                          in P.subst (λ z → [ prefix (seqa z) m ≡ᶠ prefix lp m ]∥) e (eq _) where
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
    h1 : (k : ℕ) → [ prefix (subSeq seqa f rl (suc k)) (suc k) ≡ᶠ prefix lp (suc k) ]∥
    h1 k = h12 h13 where
      n = proj₁ (lm (suc k))
      h11 = P.trans (+-comm _ n) (_≤″_.proof (≤⇒≤″ (n≤m⊔n (suc (f k)) n)))
      h12 = P.subst (λ z → [ prefix (seqa z) (suc k) ≡ᶠ prefix lp (suc k) ]∥) h11
      h13 = (proj₂ (lm (suc k))) _
    
-- Closures

  lemma-11 : {A : Set ℓ} → (P : Property A) → Tautology (P ⟶ Cl P)
  lemma-11 P a a∈P = ⟨ a ⟩ , ⟨ a∈P ⟩ , lemma-4 a

  lemma-12 : {A : Set ℓ} → (P : Property A) → Tautology (P ⟶ᶠ Cl P)
  lemma-12 P a (sa , sa∈P , eq) = sa , (lemma-11 P sa sa∈P) , eq
  
  lemma-13 : ∀{A} → {P : Property {ℓ} A} → (a : A ʷ) → a ∈ Cl P → ∀ m → prefix a m ∈ᶠ P
  lemma-13 a (seq , seq∈P , lm) m
    = let n , eq = lm m
      in seq n , seq∈P n , eq zero

  lemma-14 : ∀{A} → {P : Property {ℓ} A} → ∀{m} → {a : A ʷ∥ m} → a ∈ᶠ Cl P → a ∈ᶠ P
  lemma-14 {_} {P} {m} {a} (s , s∈ClP , eq)
    = let (sp , sp∈P , eqP) = lemma-13 {_} {P} s s∈ClP m
      in sp , sp∈P , λ fn → P.trans (eqP fn) (eq fn)


  lemma-19 : ∀{A} → {P : Property {ℓ} A} → (a : A ʷ) → (seq : Seqᶠⁱ A)
             → Limitᶠⁱ a seq → seq s∈ᶠⁱ P → a ∈ Cl P
  lemma-19 a seq lm sq∈ᶠⁱP = nsq , nsq∈P , lemma-8 nsq a h1 where
    nsq = λ m → proj₁ (sq∈ᶠⁱP m)
    nsq∈P = λ m → proj₁ (proj₂ (sq∈ᶠⁱP m))
    eq = λ m → proj₂ (proj₂ (sq∈ᶠⁱP m))
    h1 : Limitᶠⁱ a (nsq stoSeqᶠⁱ)
    h1 m fn = P.trans (eq m fn) (lm m fn)

-- ⟶ᶠ

  lemma-15 : ∀{A} → {PA PB : Property {ℓ} A} → Tautology ((Cl PA ⟶ᶠ Cl PB) ⟶ (Cl PA ⟶ Cl PB))
  lemma-15 {_} {PA} {PB} a pimpl (sq , sq∈PA , lm) = h4  where
    h1 = lemma-10 a sq lm
    f  = proj₁ h1
    rl = proj₁ (proj₂ h1)
    eq = proj₂ (proj₂ h1)
    ssq = subSeq sq f rl
    h2 = λ m → pimpl ((ssq m) , lemma-11 PA (ssq m) (sq∈PA (f m)) , eq m)
    nsq = λ m → proj₁ (h2 m)
    neq = λ m → proj₂ (proj₂ (h2 m))
    nsqs∈ᶠⁱPB : (nsq stoSeqᶠⁱ) s∈ᶠⁱ PB
    nsqs∈ᶠⁱPB m = lemma-13 (nsq m) (proj₁ (proj₂ (h2 m))) m
    h3 : Limitᶠⁱ a (nsq stoSeqᶠⁱ)
    h3 _ = neq _
    h4 = lemma-19 a (nsq stoSeqᶠⁱ) h3 nsqs∈ᶠⁱPB


-- -▹ 

  lemma-16 : ∀{A} → {PA PB : Property {ℓ} A} → Tautology ((PA -▹ PB) ≣ ((Cl PA -▹ Cl PB) & (PA ⟶ PB)))
  lemma-16 {A} {PA} {PB} a = h1 , h2 where
    h1 : ((PA -▹ PB) ⟶ ((Cl PA -▹ Cl PB) & (PA ⟶ PB))) a
    h1 (impl , pimpl) = (h11 , h12) , impl where
      h11 : (Cl PA ⟶ Cl PB) a
      h11 (sq , sq∈PA , lm)
        = nsq , nsq∈PB , h115 where
        h111 = lemma-10 a sq lm
        f = proj₁ h111
        rl = proj₁ (proj₂ h111)
        sbsq = subSeq sq f rl
        eq = proj₂ (proj₂ h111)
        h112 = lemma-9 a sq lm f rl
        h113 = λ m → pimpl ((sbsq m) , (sq∈PA (f m)) , eq m) 
        nsq : Seq A
        nsq m = proj₁ (h113 m)
        nsq∈PB : nsq s∈ PB
        nsq∈PB m = proj₁ (proj₂ (h113 m))
        nsqeq : (m : ℕ) → [ prefix (nsq m) m ≡ᶠ prefix a m ]∥
        nsqeq m = proj₂ (proj₂ (h113 m))
        h114 = lemma-7 sbsq nsq λ k fn → P.trans (eq k fn) (P.sym (nsqeq k fn))
        h115 = lemma-6 a {sbsq} {nsq} h112 h114
      h12 : (∀{m} → (prefix a m) ∈ᶠ (Cl PA) → (prefix a m) ∈ᶠ (Cl PB))
      h12 {m} a∈ClPA = lemma-12 PB a h122 where
        h121 = lemma-14 {P = PA} a∈ClPA
        h122 = pimpl h121
    h2 : (((Cl PA -▹ Cl PB) & (PA ⟶ PB)) ⟶ (PA -▹ PB)) a
    h2 ((cimpl , pimpl) , impl) = impl , (λ x → lemma-14 (pimpl (lemma-12 PA a x)))



-- -▹⁺

-- TODO The proof is identical with lemma-3 . Maybe generalize both into one.
  lemma-17 : ∀{A} → {PA PB : Property {ℓ} A} → Tautology ((PA -▹⁺ PB) ≣ ((Cl PA -▹⁺ Cl PB) & (PA ⟶ PB)))
  lemma-17 {A} {PA} {PB} a = h1 , h2 where
    h1 : ((PA -▹⁺ PB) ⟶ ((Cl PA -▹⁺ Cl PB) & (PA ⟶ PB))) a
    h1 (impl , pimpl) = (h11 , h12) , impl where
      h11 : (Cl PA ⟶ Cl PB) a
      h11 (sq , sq∈PA , lm)
        = nsq , nsq∈PB , h115 where
        h111 = lemma-10 a sq lm
        f = proj₁ h111
        rl = proj₁ (proj₂ h111)
        sbsq = subSeq sq f rl
        eq = proj₂ (proj₂ h111)
        h112 = lemma-9 a sq lm f rl
        h113 = λ m → pimpl ((sbsq m) , (sq∈PA (f m)) , eq m) 
        nsq : Seq A
        nsq m = proj₁ (h113 m)
        nsq∈PB : nsq s∈ PB
        nsq∈PB m = proj₁ (proj₂ (h113 m))
        nsqeq : (m : ℕ) → [ prefix (nsq m) m ≡ᶠ prefix a m ]∥
        nsqeq m = lemma-2 (nsq m) a (n≤1+n m) (proj₂ (proj₂ (h113 m)))
        h114 = lemma-7 sbsq nsq λ k fn → P.trans (eq k fn) (P.sym (nsqeq k fn))
        h115 = lemma-6 a {sbsq} {nsq} h112 h114
      h12 : (∀{m} → (prefix a m) ∈ᶠ (Cl PA) → (prefix a (suc m)) ∈ᶠ (Cl PB))
      h12 {m} a∈ClPA = lemma-12 PB a h122 where
        h121 = lemma-14 {P = PA} a∈ClPA
        h122 = pimpl h121
    h2 : (((Cl PA -▹⁺ Cl PB) & (PA ⟶ PB)) ⟶ (PA -▹⁺ PB)) a
    h2 ((cimpl , pimpl) , impl) = impl , (λ x → lemma-14 (pimpl (lemma-12 PA a x)))


-- This depends on the decidability of property PB on finite prefixes
-- which must be decidable if the each element is decidable. TODO
-- It also requires that PA is non-empty.
  lemma-18 : ∀{A} → {PA PB : Property {ℓ} A}
             → (d : ∀ m (a : A ʷ∥ m) → Dec (a ∈ᶠ PB))
             → P¬∅ PA
             → Tautology ((Cl PA -▹⁺ PB) ≣ ((PB -▹ Cl PA) -▹ PB))
  lemma-18 {A} {PA} {PB} d (s¬∅ , s¬∅∈PA) a = h1 , h2 where
    h1 : ((Cl PA -▹⁺ PB) ⟶ ((PB -▹ Cl PA) -▹ PB)) a
    h1 (impl , pimpl) = h11 , h12 where
      h11 : ((PB -▹ Cl PA) ⟶ PB) a
      h11 (im , pim) = impl h113 where
        h111 : (a toSeqᶠⁱ) s∈ᶠⁱ (Cl PA)
        h111 zero = lemma-1 a (s¬∅ , (lemma-11 PA s¬∅ s¬∅∈PA))
        h111 (suc m) = pim (pimpl (h111 m))
        h112 : (a toSeqᶠⁱ) s∈ᶠⁱ PA
        h112 n = lemma-14 (h111 n)
        h114 : Limit a (λ m → proj₁ (h112 m))
        h114 m = m , λ k → lemma-2 (proj₁ (h112 (k + m))) a (n≤m+n k m) (proj₂ (proj₂ (h112 (k + m))))
        h113 : a ∈ Cl PA
        h113 = (λ m → proj₁ (h112 m)) , (λ k → proj₁ (proj₂ (h112 k))) , h114
      h12 : ((PB -▹ Cl PA) ⟶ᶠ PB) a
      h12 {zero} (s , s∈-> , eq) = lemma-3 a _≤_.z≤n h122 where
        h121 = lemma-1 a {Cl PA} (s¬∅ , (lemma-11 PA s¬∅ s¬∅∈PA))
        h122 = pimpl h121
      h12 {suc k} (s , s∈-> , eq) = pimpl h124 where
        h121 = h12 {k} (s , s∈-> , lemma-2 s a (n≤1+n k) eq)
        h122 = lemma-20 a s k h121 λ fn → P.sym (lemma-2 s a (n≤1+n k) eq fn)
        h123 = (proj₂ s∈->) h122
        h124 = lemma-20 s a k h123 (lemma-2 s a (n≤1+n k) eq)
    h2 : (((PB -▹ Cl PA) -▹ PB) ⟶ (Cl PA -▹⁺ PB)) a
    h2 (impl , pimpl) = h21 , h22 where
      h21 : (Cl PA ⟶ PB) a
      h21 a∈ClPA = impl ((λ _ → a∈ClPA) , λ _ → a , a∈ClPA , λ fn → P.refl)
      h22 : (Cl PA ⟶ᶠ⁺ PB) a
      h22 {m} a∈ᶠClPA@(s , s∈∁lPA , eq)
        = case (d (suc m) (prefix a (suc m))) of
            λ { (yes p) → p
            ; (no ¬p) → ⊥-elim (¬p (pimpl (a , ((h221 ¬p
                               , h222 ¬p) , λ fn → P.refl))))} where
          h221 : ¬ (prefix a (suc m) ∈ᶠ PB) → (PB ⟶ Cl PA) a
          h221 ¬p x = ⊥-elim (¬p (a , x , (λ x₁ → P.refl)))
          h222 : ¬ (prefix a (suc m) ∈ᶠ PB) → (PB ⟶ᶠ Cl PA) a
          h222 ¬p {k} x = case (k ≤? m) of
            λ { (yes q) → lemma-3 a q a∈ᶠClPA
              ; (no ¬q) → let e = ≰⇒> ¬q
                          in ⊥-elim (¬p (lemma-3 a e x))}


