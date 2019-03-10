module TLA.Core where

open import Level renaming (suc to lsuc)
import Relation.Binary.PropositionalEquality as P
open import Data.Fin using (Fin ; toℕ)
open import Data.Nat using (ℕ ; suc ; _+_ ; _<_)
open import Data.Product
open import Data.Sum
open import LTL.Core
open import LTL.Stateless

module _ {ℓ} where

  Property : (A : Set ℓ) → Set (lsuc ℓ)
  Property A = (a : A ʷ) → Set ℓ

  Tautology : ∀{A} → Property A → Set ℓ
  Tautology P = ∀ a → P a 


-- syntactic sugar.
  _∈_ : ∀{A} → (a : A ʷ) → Property A → Set ℓ
  a ∈ P = P a

  _⟶_ : ∀{A} → Property A → Property A → Property A
  (PA ⟶ PB) a = PA a → PB a

  _&_ : ∀{A} → Property A → Property A → Property A
  (PA & PB) a = PA a × PB a

  _≣_ : ∀{A} → Property A → Property A → Property A
  (PA ≣ PB) = (PA ⟶ PB) & (PB ⟶ PA)

-- Finite Behavior
  _ʷ∥_ : Set ℓ → ℕ → Set ℓ
  A ʷ∥ m = Fin m → A

[_]∥ : ∀{ℓ m} → (Set _) ʷ∥ m → Set ℓ
[ Aₛ ]∥ = (fn : Fin _) → Aₛ fn

module _ {ℓ} where

-- Finite Equality
  _≡ᶠ_ : ∀{m} → {C : Set ℓ} → (a b : C ʷ∥ m) → Set ℓ ʷ∥ m
  (a ≡ᶠ b) n = a n P.≡ b n

  prefix : {A : Set ℓ} → (a : A ʷ) → (m : ℕ) → A ʷ∥ m
  prefix beh m fn = beh (toℕ fn)


  _∈ᶠ_ : ∀{m} → {A : Set ℓ} → (a : A ʷ∥ m) → Property A → Set ℓ
  a ∈ᶠ P = ∃ λ s → s ∈ P × [ prefix s _ ≡ᶠ a ]∥


-- Equality
  _≡_ : {Behₛ : (Set ℓ) ʷ } → (a b : [ Behₛ ]) → (Set ℓ) ʷ
  _≡_ a b n = a n P.≡ b n



  Seq : (A : Set ℓ) → Set ℓ
  Seq A = (m : ℕ) → A ʷ

  subSeq : ∀{A : Set ℓ} → Seq A → (f : ℕ → ℕ) → (∀ k → f k < f (suc k)) → Seq A
  subSeq seq f rl m = seq (f m)

  _s∈_ : ∀{A} → Seq A → (P : Property A) → Set ℓ
  (s s∈ P)= ∀ k → P (s k)

  Seqᶠ : (A : Set ℓ) → ℕ → Set ℓ
  Seqᶠ A m = (n : ℕ) → A ʷ∥ m    

-- ?
  Seqᶠⁱ : (A : Set ℓ) → Set ℓ
  Seqᶠⁱ A = (n : ℕ) → A ʷ∥ n    

  Limit : {A : Set ℓ} → (lm : A ʷ) → (seq : Seq A) → Set ℓ
  Limit lm seq = ∀ m → ∃ (λ n → ∀ k → [ (prefix (seq (k + n)) m) ≡ᶠ (prefix lm m) ]∥)


  LimitSq : {A : Set ℓ} → (seqa seqb : Seq A ) → Set ℓ
  LimitSq seqa seqb = ∀ m → ∃ (λ n → ∀ k → [ (prefix (seqa (k + n)) m) ≡ᶠ (prefix (seqb (k + n)) m) ]∥)

-- ?
  LimitSqᶠⁱ : {A : Set ℓ} → (seqa seqb : Seqᶠⁱ A ) → Set ℓ
  LimitSqᶠⁱ seqa seqb = ∀ m → [ seqa m ≡ᶠ seqb m ]∥

  Cl : ∀{A} → Property A → Property A
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


  _₊_ : ∀{A B} → Property A → StF A B → Property A
  (E ₊ V) a = E a ⊎ (∃ λ m → ((prefix a m) ∈ᶠ E) × [ (⟨ V ⟩ $ (○ₙ a m)) ≡ ((⟨ V ⟩ $ (○ (○ₙ a m)))) ])

  _⟶ᶠ_ : ∀{A} → Property {ℓ} A → Property A → Property A
  (PA ⟶ᶠ PB) a = (∀{m} → (prefix a m) ∈ᶠ PA → (prefix a m) ∈ᶠ PB)
  
  _-▹_ : ∀{A} → Property {ℓ} A → Property A → Property A
  (PA -▹ PB) = (PA ⟶ PB) & (PA ⟶ᶠ PB)  

