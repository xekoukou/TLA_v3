module TLA.Stuttering {ℓ} {A : Set ℓ} where

open import TLA.Core
import TLA.CoreP {ℓ} {A} as Cp

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
                                      ; <⇒≤ ; <⇒≢ )
open import Data.Product  
open import Data.Empty
open import Relation.Nullary
open import Data.List using (List ; [] ; _∷_ ; tabulate ; lookup ; filter ; length )
open import Data.List.Properties using (∷-injective ; ∷-injectiveˡ ; length-tabulate ; lookup-tabulate)
import Function as F

open import LTL.Core
open import LTL.Stateless hiding (_⇒_)



-- Stuttering

module _ {dec : ∀ (x y : A) → Dec (x P.≡ y)} where
  open St {ℓ} {A} {dec}

-- Finite Stuttering

  lemma-41 :  ∀{n} → {a : A ʷ} → ♮ᶠ (○ᶠ (a ᵖ∥ (suc (suc n)))) P.≡ ♮ᶠ ((○ a) ᵖ∥ (suc n))
  lemma-41 = P.refl

  lemma-35 : ∀{m} → {a : A ʷ∥ (suc m)} → a Fin.zero P.≡ proj₂ (♮ᶠ a) Fin.zero
  lemma-35 {zero} {a} = P.refl
  lemma-35 {suc m} {a} with dec (a Fin.zero) (proj₂ (♮ᶠ {m} (○ᶠ a)) Fin.zero)
  lemma-35 {suc m} {a} | yes p = p
  lemma-35 {suc m} {a} | no ¬p = P.refl

  lemma-34 :  ∀{m} → (a : A ʷ∥ (suc m))
              → let na = proj₂ (♮ᶠ a)
                in [ ⟨ ¬_ ⟩∥ $ᶠ (Stutterᶠ na) ]∥
  lemma-34 {suc m} a fn x with ♮ᶠ {m} (○ᶠ a) | lemma-34 {m} (○ᶠ a)
  ... | n , b | t with dec (a Fin.zero) (b Fin.zero)
  ... | yes p = t fn x
  lemma-34 {suc m} a Fin.zero x | n , b | t | no ¬p = ⊥-elim (¬p x)
  lemma-34 {suc m} a (Fin.suc fn) x | n , b | t | no ¬p = t fn x 


  lemma-33 :  ∀{m n} → {a : A ʷ} → (rl : m ≤ n)
              → let na = ♮ᶠ (a ᵖ∥ (suc m))
                    nb = ♮ᶠ (a ᵖ∥ (suc n))
                in ∃ λ rl → [ (proj₂ na ≤ᶠ proj₂ nb) rl ]∥
  lemma-33 {.0} {zero} {a} z≤n = s≤s z≤n , λ fn → P.cong a (P.sym (toℕ-inject≤ fn (s≤s z≤n)))
  lemma-33 {zero} {suc n} {a} rl with ♮ᶠ (○ᶠ (a ᵖ∥ suc (suc n)))
  ... | n2 , b with dec (a 0) (b Fin.zero)
  ... | yes p = (s≤s z≤n) , (λ { Fin.zero → p})
  ... | no ¬p = (s≤s z≤n) , (λ { Fin.zero → P.refl}) 
  lemma-33 {suc m} {suc n} {a} (s≤s rl) with ♮ᶠ (○ᶠ (a ᵖ∥ suc (suc n))) | ♮ᶠ (○ᶠ (a ᵖ∥ suc (suc m)))
                                     | lemma-33 {m} {n} {○ a} rl
  ... | n1 , b1 | n2 , b2  | t with dec (a 0) (b1 Fin.zero) | dec (a 0) (b2 Fin.zero)
  ... | yes p1 | yes p2 = t
  ... | no p1 | no p2 = (s≤s (proj₁ t)) , (λ { Fin.zero → P.refl
                                             ; (Fin.suc fn) → proj₂ t fn})
  ... | yes p1 | no p2 = ⊥-elim (p2 (P.trans p1 (P.sym (proj₂ t Fin.zero))))
  ... | no p1 | yes p2 = ⊥-elim (p1 (P.trans p2 (proj₂ t Fin.zero)))


-- Can this proof be simplified ?
  lemma-40 :  ∀{m} → ∀ n → {a : A ʷ}
              → let k = proj₁ (♮ᶠ (a ᵖ∥ (suc n)))
                in m ≤ k → ∃ (λ e → m P.≡ proj₁ (♮ᶠ (a ᵖ∥ (suc e))))
  lemma-40 {.0} zero {a} z≤n = zero , P.refl
  lemma-40 {0} (suc n) {a} rl = zero , P.refl
  lemma-40 {suc m} (suc n) {a} rl with dec (a 0) (proj₂ (♮ᶠ ((○ a) ᵖ∥ (suc n))) Fin.zero)
  ... | yes p = suc (proj₁ h1) , h3 where
    h1 = lemma-40 {suc m} n {○ a} rl
    h2 = P.trans p (P.trans (P.sym (lemma-35 {_} {(○ a) ᵖ∥ (suc n)})) (lemma-35 {_} {○ a ᵖ∥ (suc (proj₁ h1))}))
    h3 : suc m P.≡ proj₁ (♮ᶠ (a ᵖ∥ (suc (suc (proj₁ h1)))))
    h3 with dec (a 0) (proj₂ (♮ᶠ (○ a ᵖ∥ (suc (proj₁ h1)))) Fin.zero)
    h3 | yes p = proj₂ h1
    h3 | no ¬p = ⊥-elim (¬p h2)
  lemma-40 {suc m} (suc n) {a} (s≤s rl) | no ¬p = suc (proj₁ h1) , h3 where
    h1 = lemma-40 {m} n {○ a} rl
    h3 : suc m P.≡ proj₁ (♮ᶠ (a ᵖ∥ (suc (suc (proj₁ h1)))))
    h3 with dec (a 0) (proj₂ (♮ᶠ (○ a ᵖ∥ (suc (proj₁ h1)))) Fin.zero)
    ... | yes p = ⊥-elim (¬p h2) where
      h2 = P.trans p (P.trans (P.sym (lemma-35 {_} {(○ a) ᵖ∥ (suc (proj₁ h1))})) (lemma-35 {_} {○ a ᵖ∥ (suc n)}))
    ... | no ¬p1 = P.cong suc (proj₂ h1)

  lemma-42 : ∀{m} → (a : A ʷ∥ (suc m)) → proj₁ (♮ᶠ a) ≤ m
  lemma-42 {zero} a = z≤n
  lemma-42 {suc m} a with dec (a Fin.zero) (proj₂ (♮ᶠ {m} (○ᶠ a)) Fin.zero)
  ... | yes p = ≤-trans (lemma-42 {m} (○ᶠ a)) (n≤1+n m)
  ... | no ¬p = s≤s (lemma-42 {m} (○ᶠ a))


-- Finite Stuttering Equality

  lemma-28 :  ∀{m n k} → {a : A ʷ∥ (suc m)} → {b : A ʷ∥ (suc n)} → {c : A ʷ∥ (suc k)}
              → a ≃ᶠ b → b ≃ᶠ c → a ≃ᶠ c
  lemma-28 {m} {n} {k} {a} {b} {c} (eq1 , rl1) (eq2 , rl2)
    = (P.trans eq1 eq2) , h1 where
    h1 = Cp.lemma-29 (≤-reflexive eq1) (≤-reflexive eq2) (≤-reflexive (P.trans eq1 eq2)) (proj₂ (♮ᶠ a)) (proj₂ (♮ᶠ b)) (proj₂ (♮ᶠ c)) rl1 rl2

-- Stuttering

  lemma-26 : (a : A ʷ) → [ ⟨ ¬_ ⟩ $ Stutter a ] → ∀ m
             → let na = proj₂ (♮ᶠ (a ᵖ∥ (suc m)))
               in (a ᵖ∥ (suc m)) ≅ᶠ na 
  lemma-26 a SF zero = P.refl , λ fn → P.cong a (P.sym (toℕ-inject≤ fn (s≤s z≤n)))
  lemma-26 a SF (suc m)
    with ♮ᶠ {m} (○ᶠ (a ᵖ∥ (suc (suc m)))) | lemma-26 (○ a) (○ SF) m
  ... | n , b | g with dec ((a ᵖ∥ suc (suc m)) Fin.zero) (b Fin.zero)
  lemma-26 a SF (suc m) | n , b | g | yes p = ⊥-elim (SF 0 (P.trans p (P.sym ((proj₂ g) Fin.zero))))
  lemma-26 a SF (suc m) | n , b | g | no ¬p
    =   P.cong suc (proj₁ g)
      , λ { Fin.zero → P.refl
          ; (Fin.suc fn) → P.trans ((proj₂ g) fn)
                                (P.cong b (inject≤-irrelevant fn ((≤-reflexive (proj₁ g)))
                                                                 (≤-pred (≤-reflexive (P.cong suc (proj₁ g))))))}


  lemma-36 :  ∀{m} → (a : A ʷ) → [ ⟨ ¬_ ⟩∥ $ᶠ (Stutterᶠ (a ᵖ∥ (suc m))) ]∥
              → (⟨ ¬_ ⟩ $ (Stutter a)) [ zero ,, m ⟩
  lemma-36 a fsf t z≤t t<m s = fsf (fromℕ≤ t<m) (P.trans h3 (P.trans s (P.sym h4))) where
    h1 = toℕ-inject≤ (fromℕ≤ t<m) (≤-step (≤-reflexive P.refl))
    h2 = toℕ-fromℕ≤ t<m
    h3 = P.cong a (P.trans h1 h2)
    h4 = P.cong (○ a) h2

  lemma-43 :  ∀{m n} → {a : A ʷ} → ∀ rl
              → let na = proj₂ (♮ᶠ (a ᵖ∥ (suc m)))
                    nb = proj₂ (♮ᶠ (a ᵖ∥ (suc n)))
                in [ (na ≤ᶠ nb) rl ]∥ → ¬ (na ≅ᶠ nb) → ¬ (n ≤ m)
  lemma-43 {m} {n} {a} rl rlf neq n≤m = neq h2 where
    h1 = lemma-33 {n} {m} {a} n≤m
    h2 = Cp.lemma-40 {rl1 = rl} {proj₁ h1} rlf (proj₂ h1)


  lemma-38 :  ∀{m n} → {a : A ʷ} → {b : A ʷ} → ∀{rl}
              → let nb = ♮ᶠ (b ᵖ∥ (suc n))
                in [ ((a ᵖ∥ (suc m)) ≤ᶠ (proj₂ nb)) rl ]∥
              → ∃ (λ e → a ᵖ∥ (suc m) ≅ᶠ proj₂ (♮ᶠ (b ᵖ∥ (suc e))))
  lemma-38 {m} {n} {a} {b} {s≤s rl} rleq = {!h1!} where
    h1 = lemma-40 {m} n {b} rl
    h3 = lemma-33 {proj₁ h1} {n} {b} {!h1!}
    

  lemma-32 :  ∀{m n} → {a : A ʷ} → {b : A ʷ}
              → a ᵖ∥ (suc m) ≃ᶠ b ᵖ∥ (suc n) → ∀ k → k ≤ m → ∃ (λ e → a ᵖ∥ (suc k) ≃ᶠ b ᵖ∥ (suc e))
  lemma-32 {m} {n} {a} {b} eq k rl = {!!}

  lemma-31 : {a : A ʷ} → {b : A ʷ} → {c : A ʷ}
             → a ≃ b → b ≃ c → a ≃ c
  lemma-31 a≃b b≃c m with a≃b m | b≃c m
  lemma-31 a≃b b≃c m | n1 , k1 , mltsn1 , rl1 | n2 , k2 , mltsn2 , rl2
    = {!!}
    
  
  lemma-27 : ∀{PA} → ⊨ (Γ (Γ PA) ≣ Γ PA)
  lemma-27 a = h1 , {!!} where
    h1 : (Γ (Γ _) ⟶ Γ _) a
    h1 (s , a≃s , q , s≃q , q∈PA) = q , ({!lemma-28 a≃s s≃q!} , q∈PA)
  
--  lemma-27 : ∀{m PA′} → (a : A ʷ∥ (suc m)) → (PA : Γ PA′) → a ∈ᶠ

