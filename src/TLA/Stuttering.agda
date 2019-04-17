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
open import Data.Nat using (ℕ ; _+_ ; zero ; suc ; _≤_ ; _≥_ ; _⊔_ ; _≤″_ ; _<_ ; s≤s ; z≤n ; _≤?_ ; ≤-pred)
open import Data.Nat.Properties using (m≤m⊔n ; n≤m⊔n ; ≤⇒≤″ ; +-comm ; +-assoc
                                      ; n≤m+n ; ≤-trans ; +-suc ; n≤1+n ; ≰⇒> ; ≤-reflexive ; ≤-step
                                      ; <⇒≤ ; <⇒≢ ; ≰⇒≥ ; m≤n⇒m⊔n≡n ; m≤n⇒n⊔m≡n ; ≤-refl)
open import Data.Product  
open import Data.Empty
open import Data.Sum
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
                in proj₂ na ≤ᶠ proj₂ nb
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
    h1 = Cp.lemma-29 (proj₂ (♮ᶠ a)) (proj₂ (♮ᶠ b)) (proj₂ (♮ᶠ c)) rl1 rl2

-- Stuttering

  lemma-26 : (a : A ʷ) → [ ⟨ ¬_ ⟩ $ Stutter a ] → ∀ m
             → let na = proj₂ (♮ᶠ (a ᵖ∥ (suc m)))
               in (a ᵖ∥ (suc m)) ≅ᶠ na 
  lemma-26 a SF zero = P.refl , ≤-reflexive P.refl , λ fn → P.cong a (P.sym (toℕ-inject≤ fn (s≤s z≤n)))
  lemma-26 a SF (suc m)
    with ♮ᶠ {m} (○ᶠ (a ᵖ∥ (suc (suc m)))) | lemma-26 (○ a) (○ SF) m
  ... | n , b | g with dec ((a ᵖ∥ suc (suc m)) Fin.zero) (b Fin.zero)
  lemma-26 a SF (suc m) | n , b | (geq , grl , g) | yes p = ⊥-elim (SF 0 (P.trans p (P.sym (g Fin.zero))))
  lemma-26 a SF (suc m) | n , b | (geq , grl , g) | no ¬p
    =   P.cong suc geq
      , s≤s grl
      , λ { Fin.zero → P.refl
          ; (Fin.suc fn) → P.trans (g fn)
                                (P.cong b P.refl)}


  lemma-36 :  ∀{m} → (a : A ʷ) → [ ⟨ ¬_ ⟩∥ $ᶠ (Stutterᶠ (a ᵖ∥ (suc m))) ]∥
              → (⟨ ¬_ ⟩ $ (Stutter a)) [ zero ,, m ⟩
  lemma-36 a fsf t z≤t t<m s = fsf (fromℕ≤ t<m) (P.trans h3 (P.trans s (P.sym h4))) where
    h1 = toℕ-inject≤ (fromℕ≤ t<m) (≤-step (≤-reflexive P.refl))
    h2 = toℕ-fromℕ≤ t<m
    h3 = P.cong a (P.trans h1 h2)
    h4 = P.cong (○ a) h2

  lemma-43 :  ∀{m n} → {a : A ʷ} 
              → let na = proj₂ (♮ᶠ (a ᵖ∥ (suc m)))
                    nb = proj₂ (♮ᶠ (a ᵖ∥ (suc n)))
                in (na ≤ᶠ nb) → ¬ (na ≅ᶠ nb) → ¬ (n ≤ m)
  lemma-43 {m} {n} {a} rlf neq n≤m = neq h2 where
    h1 = lemma-33 {n} {m} {a} n≤m
    h2 = Cp.lemma-40 rlf h1

  -- Better version of lemma-43
  lemma-46 :  ∀{m n k} → {a : A ʷ} → {b : A ʷ∥ (suc k)}
              → let nam = proj₂ (♮ᶠ (a ᵖ∥ (suc m)))
                    nan = proj₂ (♮ᶠ (a ᵖ∥ (suc n)))
                    nmax = proj₂ (♮ᶠ (a ᵖ∥ (suc (m ⊔ n))))
                in (nam ≤ᶠ nan) → b ≅ᶠ nan → b ≅ᶠ nmax
  lemma-46 {m} {n} {_} {a} {b} rlf1 g@(rl2 , rlf2)
    = h3 (m ≤? n) where --  F.case (m ≤? n) of
       nam = proj₂ (♮ᶠ (a ᵖ∥ (suc m)))
       nan = proj₂ (♮ᶠ (a ᵖ∥ (suc n)))
       nmax = proj₂ (♮ᶠ (a ᵖ∥ (suc (m ⊔ n))))
       h3 : Dec (m ≤ n) → _
       h3 (yes p) = P.subst (λ z → b ≅ᶠ proj₂ (♮ᶠ (a ᵖ∥ suc z))) (P.sym (m≤n⇒m⊔n≡n p)) g
       h3 (no ¬p) = P.subst (λ z → b ≅ᶠ proj₂ (♮ᶠ (a ᵖ∥ suc z))) (P.sym (m≤n⇒n⊔m≡n p)) h313 where
         p = ≰⇒≥ ¬p
         h311 = lemma-33 {_} {_} {a} p
         h312 = Cp.lemma-40 {_} {_} {nam} {nan} rlf1 h311
         h313 = Cp.lemma-43 {_} {_} {_} {b} {nan} {nam} g (Cp.lemma-41 h312)

  lemma-38 :  ∀{m n} → {a : A ʷ∥ (suc m)} → {b : A ʷ}
              → let nb = ♮ᶠ (b ᵖ∥ (suc n))
                in a ≤ᶠ (proj₂ nb)
              → ∃ (λ e → a ≅ᶠ proj₂ (♮ᶠ (b ᵖ∥ (suc e))))
  lemma-38 {m} {n} {a} {b} g@(s≤s rl , rleq) with (h1e ≤? n) where
    h1 = lemma-40 {m} n {b} rl
    h1e = proj₁ h1
  ... | (yes p) = F.case h4
    of λ { (inj₁ z) → h1e , ((P.cong suc (proj₂ h1)) , z)
         ; (inj₂ z) → h1e , Cp.lemma-41 ((P.cong suc (P.sym (proj₂ h1))) , z)} where
    nb = proj₂ (♮ᶠ (b ᵖ∥ (suc n)))
    h1 = lemma-40 {m} n {b} rl
    h1e = proj₁ h1
    h1nb = proj₂ (♮ᶠ (b ᵖ∥ suc h1e))
    h3 = lemma-33 {_} {_} {b} p 
    h4 = Cp.lemma-42 a h1nb nb (s≤s rl , rleq) h3
  ... | (no ¬p) = h1e , (P.cong suc (proj₂ h1)) , h4 where
    nb = proj₂ (♮ᶠ (b ᵖ∥ (suc n)))
    h1 = lemma-40 {m} n {b} rl
    h1e = proj₁ h1
    h1nb = proj₂ (♮ᶠ (b ᵖ∥ suc h1e))
    h3 = lemma-33 {_} {_} {b} (≰⇒≥ ¬p) 
    h4 = Cp.lemma-29 _ _ h1nb g h3



  lemma-32 :  ∀{m n} → {a : A ʷ} → {b : A ʷ}
              → a ᵖ∥ (suc m) ≃ᶠ b ᵖ∥ (suc n) → ∀ k → k ≤ m → ∃ (λ e → a ᵖ∥ (suc k) ≃ᶠ b ᵖ∥ (suc e))
  lemma-32 {m} {n} {a} {b} (eq , rlf) k rl = h3 where
    nb = proj₂ (♮ᶠ (b ᵖ∥ (suc n)))
    na = proj₂ (♮ᶠ (a ᵖ∥ (suc k)))
    h1 = lemma-33 {_} {_} {a} rl
    h2 = Cp.lemma-29 _ _ nb h1 rlf
    h3 = lemma-38 {_} {n} {na} {b} h2

-- Can I simplify this by using lemma-32?
  lemma-44 : {a : A ʷ} → {b : A ʷ}
             → a ≃ b → ∀ l → ∃ (λ e → a ᵖ∥ (suc l) ≃ᶠ b ᵖ∥ (suc e))
  lemma-44 {a} {b} eq l with eq l
  ... | n , k , rl1 , rl2 , eqf , rlf = h3 where
    h1 = lemma-33 {_} {_} {a} rl1
    nal = proj₂ (♮ᶠ (a ᵖ∥ (suc l)))
    nan = proj₂ (♮ᶠ (a ᵖ∥ (suc n)))
    nb = proj₂ (♮ᶠ (b ᵖ∥ (suc k)))
    h2 = Cp.lemma-29 nal nan nb h1 rlf
    h3 = lemma-38 {_} {k} {nal} {b} h2


  lemma-45 : {a : A ʷ} → {b : A ʷ}
             → (∀ l → ∃ (λ e → a ᵖ∥ (suc l) ≃ᶠ b ᵖ∥ (suc e)))
             → (∀ l → ∃ (λ e → b ᵖ∥ (suc l) ≃ᶠ a ᵖ∥ (suc e)))
             → a ≃ b
  lemma-45 {a} {b} f g l with f l | g l
  ... | e1 , eqf1@(rl1 , rlf1) | e2 , eqf2@(rl2 , rlf2)
    = h1 (l ≤? e1) (l ≤? e2) where
      h1 : Dec (l ≤ e1) → _ → _
      h1 (yes p) _ = l , e1 , ≤-refl , p , eqf1
      h1 (no ¬p) (yes v) = e2 , l , v , ≤-refl , Cp.lemma-41 eqf2
      h1 (no ¬p) (no ¬v) = l , l , ≤-refl , ≤-refl , h15 where
        nal = proj₂ (♮ᶠ (a ᵖ∥ (suc l)))
        nae = proj₂ (♮ᶠ (a ᵖ∥ (suc e2)))
        nbe = proj₂ (♮ᶠ (b ᵖ∥ (suc e1)))
        nbl = proj₂ (♮ᶠ (b ᵖ∥ (suc l)))
        p = ≰⇒≥ ¬p
        v = ≰⇒≥ ¬v
        h11 = lemma-33 {_} {_} {b} p
        h12 = lemma-33 {_} {_} {a} v
        h13 = Cp.lemma-29 nal nbe nbl rlf1 h11
        h14 = Cp.lemma-29 nbl nae nal rlf2 h12
        h15 = Cp.lemma-40 h13 h14
             

  lemma-47 : {a : A ʷ} → {b : A ʷ}
             → a ≃ b → b ≃ a
  lemma-47 {a} {b} a≃b m with a≃b m
  ... | n , k , rl1 , rl2 , rlf = k , n , rl2 , rl1 , Cp.lemma-41 rlf

  lemma-48 : (a : A ʷ)
             → a ≃ a
  lemma-48 a m = m , m , ≤-refl , ≤-refl , Cp.lemma-44 (proj₂ (♮ᶠ (a ᵖ∥ (suc m))))
  
  lemma-31 : {a : A ʷ} → {b : A ʷ} → {c : A ʷ}
             → a ≃ b → b ≃ c → a ≃ c
  lemma-31 {a} {b} {c} a≃b b≃c = h7 where
    h1 = lemma-44 {a} {b} a≃b
    h2 = lemma-44 {b} {c} b≃c
    h3 = lemma-44 {b} {a} (lemma-47 {a} {b} a≃b)
    h4 = lemma-44 {c} {b} (lemma-47 {b} {c} b≃c)
    h5 : ∀ l → ∃ (λ e → a ᵖ∥ (suc l) ≃ᶠ c ᵖ∥ (suc e))
    h5 l = h53 where
      na = proj₂ (♮ᶠ (a ᵖ∥ (suc l)))
      h51 = h1 l
      nb = proj₂ (♮ᶠ (b ᵖ∥ (suc (proj₁ h51))))
      h52 = h2 (proj₁ h51)
      nc = proj₂ (♮ᶠ (c ᵖ∥ (suc (proj₁ h52))))
      h53 = proj₁ h52 , Cp.lemma-43 {_} {_} {_} {na} {nb} {nc} (proj₂ h51) (proj₂ h52)
    h6 : ∀ l → ∃ (λ e → c ᵖ∥ (suc l) ≃ᶠ a ᵖ∥ (suc e))
    h6 l = h63 where
      nc = proj₂ (♮ᶠ (c ᵖ∥ (suc l)))
      h61 = h4 l
      nb = proj₂ (♮ᶠ (b ᵖ∥ (suc (proj₁ h61))))
      h62 = h3 (proj₁ h61)
      na = proj₂ (♮ᶠ (a ᵖ∥ (suc (proj₁ h62))))
      h63 = proj₁ h62 , Cp.lemma-43 {_} {_} {_} {nc} {nb} {na} (proj₂ h61) (proj₂ h62)
    h7 = lemma-45 {a} {c} h5 h6


  lemma-27 : ∀{PA} → ⊨ (Γ (Γ PA) ≣ Γ PA)
  lemma-27 a = h1 , h2 where
    h1 : (Γ (Γ _) ⟶ Γ _) a
    h1 (s , a≃s , q , s≃q , q∈PA) = q , (lemma-31 {a} {s} {q} a≃s s≃q , q∈PA)
    h2 : (Γ _ ⟶ Γ (Γ _)) a
    h2 x = a , lemma-48 a , x

