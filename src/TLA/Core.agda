module TLA.Core where

open import Level renaming (suc to lsuc ; zero to lzero)
import Relation.Binary.PropositionalEquality as P
open import Data.Fin using (Fin ; toℕ ; fromℕ ; fromℕ≤ ; inject₁ ; inject≤)
open import Data.Nat as N using (ℕ ; suc ; zero ; _+_ ; _<_ ; _≤_ ; s≤s ; _≟_)
open import Data.Nat.Properties using (n≤1+n ; ≤-reflexive)
open import Data.List using (List ; [] ; _∷_ ; tabulate ; lookup ; filter ; length)
open import Data.Product
open import Data.Empty
open import Data.Unit
open import Relation.Nullary
open import Data.Sum
import Function as F
open import LTL.Core
open import LTL.Stateless
open import LTL.Until
open import LTL.Globally
open import LTL.Product
open import LTL.Sum
open import LTL.Future

module _ {ℓ} where

  BSet : (A : Set ℓ) → Set (lsuc ℓ)
  BSet A = (a : A ʷ) → Set ℓ

  P¬∅ : {A : Set ℓ} → BSet A → Set ℓ
  P¬∅ P = ∃ λ s → P s

  ⊨ : ∀{A} → BSet A → Set ℓ
  ⊨ P = ∀ a → P a 

-- syntactic sugar.
  _∈_ : ∀{A} → (a : A ʷ) → BSet A → Set ℓ
  a ∈ P = P a

  _⟶_ : ∀{A} → BSet A → BSet A → BSet A
  (PA ⟶ PB) a = PA a → PB a

  _&_ : ∀{A} → BSet A → BSet A → BSet A
  (PA & PB) a = PA a × PB a

  _≣_ : ∀{A} → BSet A → BSet A → BSet A
  (PA ≣ PB) = (PA ⟶ PB) & (PB ⟶ PA)

module _ {ℓ} where

-- Finite Equality
  _≡ᶠ_ : ∀{m} → {C : Set ℓ} → (a b : C ʷ∥ m) → Set ℓ ʷ∥ m
  (a ≡ᶠ b) n = a n P.≡ b n

  _≤ᶠ_ : ∀{m n} → {C : Set ℓ} → (a : C ʷ∥ m) → (b : C ʷ∥ n) → m N.≤ n → Set ℓ ʷ∥ m
  (a ≤ᶠ b) m≤n fn = a fn P.≡ b (inject≤ fn m≤n)

  _≅ᶠ_ : ∀{m n} → {C : Set ℓ} → (a : C ʷ∥ m) → (b : C ʷ∥ n) → Set ℓ
  _≅ᶠ_ {m} {n} a b = Σ (m P.≡ n) λ eq → [ (a ≤ᶠ b) (≤-reflexive eq) ]∥


  infix 30 _ᵖ∥_
  _ᵖ∥_ : {A : Set ℓ} → (a : A ʷ) → (m : ℕ) → A ʷ∥ m
  (a ᵖ∥ m) fn = a (toℕ fn)

  infix 30 _ᵖᶠ∥_
  _ᵖᶠ∥_ : {A : Set ℓ} → ∀{m} → (a : A ʷ∥ m) → (n : ℕ) → {rl : n N.≤ m} → A ʷ∥ n
  (a ᵖᶠ∥ n) {rl} fn = a (inject≤ fn rl)

  _∈ᶠ_ : ∀{m} → {A : Set ℓ} → (a : A ʷ∥ m) → BSet A → Set ℓ
  a ∈ᶠ P = ∃ λ s → s ∈ P × [ (s ᵖ∥ _) ≡ᶠ a ]∥

-- Equality
  _≡_ : {B : (Set ℓ) ʷ } → (a b : [ B ]) → (Set ℓ) ʷ
  _≡_ a b n = a n P.≡ b n

-- Sequences of Sequences

  Seq : (A : Set ℓ) → Set ℓ
  Seq A = (m : ℕ) → A ʷ

  subSeq : ∀{A : Set ℓ} → Seq A → (f : ℕ → ℕ) → (∀ k → f k < f (suc k)) → Seq A
  subSeq seq f rl m = seq (f m)

  _s∈_ : ∀{A} → Seq A → (P : BSet A) → Set ℓ
  (s s∈ P)= ∀ k → P (s k)

  Seqᶠ : (A : Set ℓ) → ℕ → Set ℓ
  Seqᶠ A m = (n : ℕ) → A ʷ∥ m

  _s∈ᶠ_ : ∀{A m} → Seqᶠ A m → (P : BSet A) → Set ℓ
  (s s∈ᶠ P)= ∀ k → (s k) ∈ᶠ P

  Seqᶠⁱ : (A : Set ℓ) → Set ℓ
  Seqᶠⁱ A = (n : ℕ) → A ʷ∥ n    

  _s∈ᶠⁱ_ : {A : Set ℓ} → (s : Seqᶠⁱ A) → BSet A → Set ℓ
  s s∈ᶠⁱ P = (m : ℕ) → s m ∈ᶠ P

  _toSeqᶠⁱ : {A : Set ℓ} → A ʷ → Seqᶠⁱ A
  (a toSeqᶠⁱ) m = a ᵖ∥ m

  _stoSeqᶠⁱ : {A : Set ℓ} → Seq A  → Seqᶠⁱ A
  (s stoSeqᶠⁱ) m = (s m) ᵖ∥ m

  Limit : {A : Set ℓ} → (lm : A ʷ) → (seq : Seq A) → Set ℓ
  Limit lm seq = ∀ m → ∃ (λ n → ∀ k → [ ((seq (k + n)) ᵖ∥ m) ≡ᶠ (lm ᵖ∥ m) ]∥)

  Limitᶠⁱ : {A : Set ℓ} → (lm : A ʷ) → (seq : Seqᶠⁱ A) → Set ℓ
  Limitᶠⁱ lm seq = ∀ m → [ seq m ≡ᶠ (lm ᵖ∥ m) ]∥

  LimitSq : {A : Set ℓ} → (seqa seqb : Seq A ) → Set ℓ
  LimitSq seqa seqb = ∀ m → ∃ (λ n → ∀ k → [ ((seqa (k + n)) ᵖ∥ m) ≡ᶠ ((seqb (k + n)) ᵖ∥ m) ]∥)

  LimitSqᶠⁱ : {A : Set ℓ} → (seqa seqb : Seqᶠⁱ A ) → Set ℓ
  LimitSqᶠⁱ seqa seqb = ∀ m → [ seqa m ≡ᶠ seqb m ]∥


  Cl : ∀{A} → BSet A → BSet A
  Cl P s = ∃ λ seq → (seq s∈ P) × Limit s seq

-- State Function
  StF : (A : Set ℓ) → (B : Set ℓ) → Set ℓ 
  StF A B = A → B


-- State Predicate
  StP : ∀{ℓ₁} → (A : Set ℓ) → Set (ℓ ⊔ lsuc ℓ₁)
  StP {ℓ₁} A = A → Set ℓ₁

-- Action

  RawAction : (A : Set ℓ) → Set (lsuc ℓ)
  RawAction A = A → A → Set ℓ

  ⟦_⟧_ : ∀{A B} → RawAction A → StF A B → Set ℓ
  ⟦_⟧_ ract stF = ∀ a b → ract a b ⊎ (stF a P.≡ stF b)


  _₊_ : ∀{A B} → BSet A → StF A B → BSet A
  (E ₊ V) a = E a ⊎ (∃ λ m → ((a ᵖ∥ m) ∈ᶠ E) × [ (⟨ V ⟩ $ (○ₙ a m)) ≡ ((⟨ V ⟩ $ (○ (○ₙ a m)))) ])

  _⟶ᶠ_ : ∀{A} → BSet {ℓ} A → BSet A → BSet A
  (PA ⟶ᶠ PB) a = (∀{m} → (a ᵖ∥ m) ∈ᶠ PA → (a ᵖ∥ m) ∈ᶠ PB)
  
  _-▹_ : ∀{A} → BSet {ℓ} A → BSet A → BSet A
  (PA -▹ PB) = (PA ⟶ PB) & (PA ⟶ᶠ PB)  


  _⟶ᶠ⁺_ : ∀{A} → BSet {ℓ} A → BSet A → BSet A
  (PA ⟶ᶠ⁺ PB) a = (∀{m} → (a ᵖ∥ m) ∈ᶠ PA → (a ᵖ∥ (1 + m)) ∈ᶠ PB)

  _-▹⁺_ : ∀{A} → BSet {ℓ} A → BSet A → BSet A
  PA -▹⁺ PB =  (PA ⟶ PB) & (PA ⟶ᶠ⁺ PB)  


-- Stuttering

  Stutter : {A : Set ℓ} → A ʷ → (Set ℓ) ʷ
  Stutter a = a ≡ ○ a

  Terminating : {A : Set ℓ} → A ʷ → Set ℓ
  Terminating a = [ ◇ᶠ (□ᶠ (Stutter a)) ]

  Non-Terminating : {A : Set ℓ} → A ʷ → Set ℓ
  Non-Terminating a = [ □ᶠ (◇ᶠ (⟨ ¬_ ⟩ $ (Stutter a))) ]
  
  Stutter-free : {A : Set ℓ} → A ʷ → Set ℓ
  Stutter-free a = [ ⟨ ¬_ ⟩ $ Stutter a ] ⊎ [ (⟨ ¬_ ⟩ $ Stutter a) U □ᶠ (Stutter a) ]

  Stutterᶠ : {A : Set ℓ} → ∀{m} → A ʷ∥ (suc m) → (Set ℓ) ʷ∥ m
  Stutterᶠ {_} {m} a = (a ᵖᶠ∥ m) {n≤1+n m} ≡ᶠ ○ᶠ a

module St {ℓ} {A : Set ℓ} {dec : ∀ (x y : A) → Dec (x P.≡ y)} where

  ♮ᶠ : ∀{m} → A ʷ∥ (suc m) → ∃ λ n → A ʷ∥ (suc n)
  ♮ᶠ {zero} a = zero , a
  ♮ᶠ {suc m} a with ♮ᶠ {m} (○ᶠ a)
  ♮ᶠ {suc m} a | n , b
    = F.case (dec (a Fin.zero) (b Fin.zero)) of
         λ { (yes p) → n , b
           ; (no ¬p) → suc n , λ { Fin.zero → a Fin.zero ; (Fin.suc x) → b x}}


  _≃ᶠ_ : ∀{m n} → (a : A ʷ∥ (suc m)) → (b : A ʷ∥ (suc n)) → Set ℓ
  _≃ᶠ_ a b = na ≅ᶠ nb where
    na = proj₂ (♮ᶠ a)
    nb = proj₂ (♮ᶠ b)

  _≃_ : (a b : A ʷ) → Set ℓ
  a ≃ b = ∀ (m : ℕ) → ∃ λ n →
                      ∃ λ k → m N.≤ (suc n) × ((a ᵖ∥ (suc n)) ≃ᶠ (a ᵖ∥ (suc k)))
    

-- We cannot construct it , thus we define its type.
  ♮ : A ʷ → Set ℓ
  ♮ a = ∃ λ s → a ≃ s × Stutter-free s

-- Closure under stuttering

  infix 30 Γ
  Γ : BSet A → BSet A
  Γ PA a = ∃ λ s → a ≃ s × PA s

  infix 30 _isProp
  _isProp : BSet A → Set ℓ
  PA isProp = ⊨ (PA ≣ Γ PA)

