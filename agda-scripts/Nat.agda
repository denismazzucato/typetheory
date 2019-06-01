-- module name 
module Nat where

-- import propositional equality and reasoning proofs
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_ ; _∎)

-- natural type
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- this tells agda that ℕ corresponds to the natural numbers
-- implies shorthand for the well-known number syntax like 0, 1, 2 ...
-- the pragma also enable an efficient way to internally represent the natural numbers
{-# BUILTIN NATURAL ℕ #-}

-- operations
_+₁_ : ℕ → ℕ → ℕ
zero     +₁ n = n
(succ m) +₁ n = succ(m +₁ n)

_+₂_ : ℕ → ℕ → ℕ
n +₂ zero = n
n +₂ (succ m) = succ(n +₂ m)

-- basic proofs
_ =
  begin
    2 +₁ 3
  ≡⟨⟩
    succ(1 +₁ 3)
  ≡⟨⟩
    succ(succ(0 +₁ 3))
  ≡⟨⟩
    succ(succ(3))
  ≡⟨⟩
    5
  ∎

_ =
  begin
    2 +₂ 3
  ≡⟨⟩
    succ(2 +₂ 2)
  ≡⟨⟩
    succ(succ(2 +₂ 1))
  ≡⟨⟩
    succ(succ(succ(2 +₂ 0)))
  ≡⟨⟩
    succ(succ(succ(2)))
  ≡⟨⟩
    5
  ∎

-- pretty different

-- now lets proof that _ +₁ _ is propositional equality to _ +₂ _ by induction

-- first we define two lemma
-- lemma 1, identity over zero in the wrong place

+₁-identity : ∀ (n : ℕ) → n +₁ zero ≡ n
+₁-identity zero =
  begin
    zero +₁ zero
  ≡⟨⟩
    zero
  ∎
+₁-identity (succ n) =
  begin
    (succ n) +₁ zero
  ≡⟨⟩
    succ (n +₁ zero)
  ≡⟨ cong succ (+₁-identity n) ⟩ -- the space before "cong" is essential
    succ n
  ∎

+₂-identity : ∀ (n : ℕ) → zero +₂ n ≡ n
+₂-identity zero =
  begin
    zero +₂ zero
  ≡⟨⟩
    zero
  ∎
+₂-identity (succ n) =
  begin
    zero +₂ (succ n)
  ≡⟨⟩
    succ (zero +₂ n)
  ≡⟨ cong succ (+₂-identity n) ⟩ -- the space before "cong" is essential
    succ n
  ∎

-- lemma 2, succ in the wrong place

+₁-succ : ∀ (m n : ℕ) → m +₁ (succ n) ≡ succ (m +₁ n)
+₁-succ zero n =
  begin
    zero +₁ (succ n)
  ≡⟨⟩
    succ n
  ≡⟨⟩
    succ (zero +₁ n)
  ∎
+₁-succ (succ m) n =
  begin
    (succ m) +₁ (succ n)
  ≡⟨⟩
    succ (m +₁ (succ n))
  ≡⟨ cong succ (+₁-succ m n) ⟩
    succ (succ (m +₁ n))
  ≡⟨⟩
    succ ((succ m) +₁ n)
  ∎

+₂-succ : ∀ (m n : ℕ) → (succ m) +₂ n ≡ succ (m +₂ n)
+₂-succ m zero =
  begin
    (succ m) +₂ zero
  ≡⟨⟩
    succ m
  ≡⟨⟩
    succ (m +₂ zero)
  ∎
+₂-succ m (succ n) =
  begin
    (succ m) +₂ (succ n)
  ≡⟨⟩
    succ ((succ m) +₂ n)
  ≡⟨ cong succ (+₂-succ m n) ⟩
    succ (succ (m +₂ n))
  ≡⟨⟩
    succ (m +₂ (succ n))
  ∎


+-comm : ∀ (m n : ℕ) → m +₁ n ≡ m +₂ n
+-comm m zero =
  begin
    m +₁ zero
  ≡⟨ +₁-identity m ⟩
    m
  ≡⟨⟩
    m +₂ zero
  ∎
+-comm m (succ n) =
  begin
    m +₁ (succ n)
  ≡⟨ +₁-succ m n ⟩
    succ(m +₁ n)
  ≡⟨ cong succ (+-comm m n) ⟩
    succ(m +₂ n)
  ≡⟨⟩
    m +₂ (succ n)
  ∎
