module TLA.CoreP {ℓ} {A : Set ℓ} where

open import TLA.Core
import TLA.Common as C

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


-- BSets

lemma-1 : (a : A ʷ) → {P : BSet A} → P¬∅ P → a ᵖ∥ 0 ∈ᶠ P
lemma-1 a (s , s∈P ) = s , s∈P , (λ ())

--Finite Ordering

lemma-45 :  ∀{m} → (a : A ʷ∥ m)
            → a ≤ᶠ a
lemma-45 a = ≤-refl , (λ fn → P.sym (P.cong a (inject≤-refl fn ≤-refl)))

lemma-29 :  ∀{m n k} 
            → (a : A ʷ∥ m) → (b : A ʷ∥ n) → (c : A ʷ∥ k)
            → (a ≤ᶠ b) → (b ≤ᶠ c) → (a ≤ᶠ c)
lemma-29 a b c (m≤n , altb) (n≤k , bltc)
  =   (≤-trans m≤n n≤k)
    , (λ fn → P.trans (altb fn) ((P.trans (bltc (inject≤ fn m≤n)) (P.cong c (inject≤-idempotent fn m≤n n≤k ((≤-trans m≤n n≤k))))))) where

lemma-40 :  ∀{m n} → {a : A ʷ∥ m} → {b : A ʷ∥ n}
            → (a ≤ᶠ b) → (b ≤ᶠ a) → a ≅ᶠ b
lemma-40 {b = b} (rl1 , rlf1) (rl2 , rlf2)
  = (≤-antisym rl1 rl2) , rl1 , rlf1


lemma-42 :  ∀{m n k}
            → (a : A ʷ∥ m) → (b : A ʷ∥ n) → (c : A ʷ∥ k)
            → (a ≤ᶠ c) → (b ≤ᶠ c) → (a ≤ᶠ b) ⊎ (b ≤ᶠ a)
lemma-42 {m} {n} a b c (rl1 , altc) (rl2 , bltc) with (m ≤? n)
... | yes p
  = inj₁ (  p
          , λ fn → P.trans (altc fn)
                   (P.trans (P.sym (P.cong c ((inject≤-idempotent fn p rl2 rl1))))
                            (P.sym (bltc (inject≤ fn p)))))
... | no ¬p
  = let p = ≰⇒≥ ¬p
    in inj₂ ( p 
             , λ fn → P.trans (bltc fn)
                              (P.trans (P.cong c (P.sym (inject≤-idempotent fn p rl1 rl2)))
                                       (P.sym (altc (inject≤ fn p)))))

-- Heterogeneous Finite equality


lemma-44 :  ∀{m} → (a : A ʷ∥ m)
            → a ≅ᶠ a
lemma-44 {m} a = P.refl , lemma-45 a

lemma-41 :  ∀{m n} → {a : A ʷ∥ n} → {b : A ʷ∥ m}
            → a ≅ᶠ b → b ≅ᶠ a
lemma-41 {m} {.m} {a} {b} (P.refl , rl , rlf) = P.refl , h1 where
  h1 : (b ≤ᶠ a)
  h1 =   rl
       , λ fn → P.trans (P.cong b (P.sym (inject≤-refl fn rl)))
                        (P.trans (P.sym (rlf fn))
                                 (P.cong a (P.sym (inject≤-refl fn rl))))


lemma-43 :  ∀{m n k} → {a : A ʷ∥ n} → {b : A ʷ∥ m} → {c : A ʷ∥ k}
            → a ≅ᶠ b → b ≅ᶠ c → a ≅ᶠ c
lemma-43 {_} {_} {_} {a} {b} {c} (eq1 , rlf1) (eq2 , rlf2) = P.trans eq1 eq2 , lemma-29 a b c rlf1 rlf2


lemma-39 :  ∀{n} → {a : A ʷ∥ n} → {b : A ʷ∥ n}
            → a ≅ᶠ b →  [ a ≡ᶠ b ]∥
lemma-39 {_} {_} {b} (P.refl , (rl , eq)) fn = P.trans (eq fn) (P.cong b (inject≤-refl fn rl))


-- PREFIXES

lemma-37 :  ∀{n} → {a : A ʷ} → [ (○ a) ᵖ∥ n ≡ᶠ ○ᶠ (a ᵖ∥ (suc n)) ]∥
lemma-37 {n} {a} fn = P.refl

-- If we have proved equality of prefixes at length m , then equality is true for smaller prefixes.
lemma-2 : (a b : A ʷ) → ∀ {m n} → n ≤ m
          → [ a ᵖ∥ m ≡ᶠ b ᵖ∥ m ]∥ → [ a ᵖ∥ n ≡ᶠ b ᵖ∥ n ]∥
lemma-2 a b nltm rst fn = q where
  w = rst (inject≤ fn nltm)
  q = P.subst (λ z → (a ≡ b) z) (toℕ-inject≤ fn nltm) w

lemma-3 : ∀{m n} → (a : A ʷ) → {P : BSet A} → n ≤ m
           → a ᵖ∥ m ∈ᶠ P → a ᵖ∥ n ∈ᶠ P
lemma-3 a n≤m (s , s∈P , eq) = s , s∈P , (lemma-2 s a n≤m eq)

-- _∈ᶠ_

lemma-20 : {A : Set ℓ} → (a b : A ʷ) → {P : BSet A}
           → ∀ m → a ᵖ∥ m ∈ᶠ P → [ a ᵖ∥ m ≡ᶠ b ᵖ∥ m ]∥
           → b ᵖ∥ m ∈ᶠ P
lemma-20 a b m pa∈ᶠP eq
  = (proj₁ pa∈ᶠP) , ((proj₁ (proj₂ pa∈ᶠP))
                    , λ fn → P.trans (proj₂ (proj₂ pa∈ᶠP) fn) (eq fn))

-- _≡ᶠ_

symᶠ : ∀{m} → {C : Set ℓ} → {a b : C ʷ∥ m} → [ a ≡ᶠ b ]∥ → [ b ≡ᶠ a ]∥
symᶠ x fn = P.sym (x fn)
