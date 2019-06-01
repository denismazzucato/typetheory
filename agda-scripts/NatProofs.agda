module NatProofs where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

-- these functions are necessary for the exercises

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

-- swap proof with the aids of emacs goal completitions shortcut
-- m + (n + p) ≡ n + (m + p)

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero n p = refl
+-swap (suc m) n p rewrite +-swap m n p | +-suc n (m + p) = refl

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

-- inc : Bin → Bin
-- inc nil = x0 nil
-- inc (x0 n) = inc {!!}
-- inc (x1 n) = {!!} 

-- import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
