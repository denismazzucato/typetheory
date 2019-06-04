-- in this file I'll test different ways to sum natural numbers


-- natural type
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}


-- recursion combinator (Simple)
ind : {X : Set} → X → (X → X) → (ℕ → X)
ind x f zero = x
ind x f (succ n) = f (rec x f n)

-- primitive-recursion combinator
-- p-rec : (X : Set) → 
