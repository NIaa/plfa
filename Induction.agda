module plfa.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans;  sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)

{-
f ps rewrite eq = v

f ps with lhsₑ | e
...    | .rhsₑ | refl = v
  左 等式
  隐含的右 等式匹配      result
-}

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl

-- desugar
+-assocW : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assocW zero    n p                          =  refl
+-assocW (suc m) n p with (m + n + p) | (+-assocW m n p)
...                | . (m + (n + p))  | refl = refl

-- Feel again
+-assocF : ∀ (m n p : ℕ ) → ( m + n ) + p ≡ m + (n + p)
+-assocF zero n p = refl
+-assocF (suc m) n p rewrite +-assocF m n p = refl

{-
base  (zero + n) + p ≡ zero + (n + p)
ind   suc ((m + n) + p) ≡ suc (m + (n + p))
hyp is obvious

Rewriting avoids not only chains of equations but also the need to invoke cong.
-}
{-
data One : Bin → Set where
  nil : One (c1 nil)
  c0_ : ∀{x : Bin} → One x → One (c0 x)
  c1_ : ∀{x : Bin} → One x → One (c1 x)

data Can : Bin → Set where
  zero : Can (c0 nil)
  leading : ∀{x : Bin} → One x → Can x
-}


+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) = cong suc (+-identityʳ m)

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = +-identityʳ m
+-comm m (suc n) = trans (+-suc m n) (cong suc (+-comm m n))

_~_ = trans
infixr 5 _~_

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q = (+-assoc m n (p + q)) ~ (cong (λ x → m + x) (sym (+-assoc n p q))) ~ sym (+-assoc m (n + p) q)

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) = cong suc (+-identity′ n)

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n = cong suc (+-suc′ m n)

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero = +-identity′ m
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n  = refl

-- Exercise
-----------------------------------------

-- operators
-- Give another example of a pair of operators that have an identity and are associative, commutative, and distribute over one another.
-- * +

-- Give an example of an operator that has an identity and is associative but is not commutative.
-- ++ { [] is id }

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
-- +-swap m n p rewrite sym (+-assoc m n p) | +-comm m n  = +-assoc n m p
+-swap m n p = trans (sym (+-assoc m n p)) (trans (cong (λ x → x + p) (+-comm m n)) (+-assoc n m p))

-- m (n p) == n (m p)
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | +-assoc p (m * p) (n * p)  = refl

*-identityʳ : ∀ (n : ℕ) → n * zero ≡ zero
*-identityʳ zero = refl
*-identityʳ (suc n) = *-identityʳ n

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl

lemma-*suc : ∀ a b → a + a * b ≡ a * suc b
lemma-*suc zero b = refl
lemma-*suc (suc a) b rewrite sym (lemma-*suc a b) | +-swap b a (a * b) = refl


*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero = *-identityʳ m
*-comm m (suc n) rewrite sym (lemma-*suc m n) | cong (_+_ m) (*-comm m n) = refl
-- *-comm m (suc n) rewrite sym (lemma-*suc m n) | *-comm m n = refl
--*-comm m (suc n) ≡ sym (lemma-*suc ? )


0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl
-- 如何工作， 为什么分开？


∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc zero (suc n) p rewrite 0∸n≡0 p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

-- Bin-laws
-- Recall that Exercise Bin defines a datatype of bitstrings representing natural numbers
data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

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

lemma-+suc : ∀ (m n : ℕ) → (m + suc n) ≡ suc (m + n)
lemma-+suc zero n = refl
lemma-+suc (suc m) n = cong suc (lemma-+suc m n)

-- seems true
from∘inc-suc∘from : ∀ (x : Bin) → from (inc x) ≡ suc (from x)
from∘inc-suc∘from nil = refl
from∘inc-suc∘from (x0 x) = refl
from∘inc-suc∘from (x1 x) rewrite from∘inc-suc∘from x | +-identityʳ (from x) | lemma-+suc (from x) (from x) = refl

-- Bin → ℕ → Bin
--  nil → 0 → x0 nil, which is not true
-- l2 : ∀ (x : Bin) → to (from x) ≡ x
-- l2 nil = {!!}
-- l2 (x0 x) = {!!}
-- l2 (x1 x) = {!!}

-- ℕ → Bin → ℕ, true
from∘to-id : ∀ (n : ℕ) → from (to n) ≡ n
from∘to-id zero = refl
from∘to-id (suc n) rewrite from∘inc-suc∘from (to n) | from∘to-id n = refl

-- import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
