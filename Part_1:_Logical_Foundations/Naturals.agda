module plfa.Naturals where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- is longhand for
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl  -- Agda knows how to compute the value of 2 + 3

_*_ : ℕ → ℕ → ℕ
zero  * n  =  zero
suc m * n  =  n + (m * n)

_ =
  begin
    2 * 3
  ≡⟨⟩    -- inductive case
    3 + (1 * 3)
  ≡⟨⟩    -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩    -- base case
    3 + (3 + 0)
  ≡⟨⟩    -- simplify
    6
  ∎

_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ suc m = n * (n ^ m)

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

infixl 6  _+_  _∸_
infixl 7  _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- Exercise
----------------------------------------------------

-- Write out 7 in longhand.
seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

-- Compute 3 + 4, writing out your reasoning as a chain of equations.
_ = 3 + 4
  ≡⟨⟩ suc (2 + 4)
  ≡⟨⟩ suc (suc ( 1 + 4))
  ≡⟨⟩ suc (suc (suc 4))
  ≡⟨⟩ 7
  ∎

-- Compute 3 * 4, writing out your reasoning as a chain of equations.
_ = 3 * 4
  ≡⟨⟩ 4 + (2 * 4)
  ≡⟨⟩ 4 + (4 + (1 * 4))
  ≡⟨⟩ 4 + (4 + (4 + 0))
  ≡⟨⟩ 12
  ∎

-- Check that 3 ^ 4 is 81
_ = 3 ^ 4
  ≡⟨⟩ 81
  ∎

-- Compute 5 ∸ 3 and 3 ∸ 5, writing out your reasoning as a chain of equations.
_ = 5 ∸ 3 ≡⟨⟩ 2 ∎
_ = 3 ∸ 5 ≡⟨⟩ 0 ∎

-- STL: import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)

-- Exercise Bin (stretch)
data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

-- 1011 x1 x1 x0 x1 nil
-- inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil


inc : Bin → Bin
inc nil = x1 nil
inc (x0 b) = x1 b
inc (x1 b) = x0 (inc b)

-- x0 nil ? nil
to : ℕ → Bin
to zero = x0 nil
to (suc n) = inc (to n)

--  extend this func to nil
from : Bin → ℕ
from nil = zero
from (x0 b) = 2 * from b
from (x1 b) = 1 + 2 * from b

-- test
_ = to 11 ≡⟨⟩ x1 x1 x0 x1 nil ∎
_ = from (x1 x1 x0 x1 nil) ≡⟨⟩ 11 ∎
