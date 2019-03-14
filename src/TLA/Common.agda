module TLA.Common where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- Add this to the standard library.
lemma-1 : (f : ℕ → ℕ) → (rl : ∀ k → f k < f (suc k)) → ∀ m → ∃ λ n → ∀ k → m ≤ f (k + n) 
lemma-1 f rl zero = zero , (λ k → _≤_.z≤n)
lemma-1 f rl (suc m)
  = let n , eq = lemma-1 f rl m
    in suc n , λ k → let q = +-suc k n
                     in ≤-trans (s≤s (eq k)) (subst (λ z → suc (f (k + n)) ≤ f z) (sym q) (rl (k + n))) 

-- Add this to the standard library.
lemma-2 : (f : ℕ → ℕ) → (rl : ∀ k → f k < f (suc k)) → ∀ k → k ≤ f k
lemma-2 f rl zero = _≤_.z≤n
lemma-2 f rl (suc k) = ≤-trans (s≤s (lemma-2 f rl k)) (rl k)
