module plfa.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm; *-distrib-+)


data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
    --------
    → zero ≤ n
  s≤s : ∀ {m n : ℕ}
    → m ≤ n
    -------------
    → suc m ≤ suc n

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

_ : 2 ≤ 4
_ = s≤s {n = 3} (s≤s {n = 2} z≤n)

infix 4 _≤_

-- Reflexivity
≤-refl : ∀ {n : ℕ}
  -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

-- Transitivity
≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
  -----
  → m ≤ p
≤-trans z≤n       _          =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)

-- Anti-symmetry
≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
  -----
  → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)

-- Total (parameterised by m n)
data Total (m n : ℕ) : Set where
  forward :
    m ≤ n
    ---------
    → Total m n
  flipped :
    n ≤ m
    ---------
    → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)

≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)

-- Monotonicity
+-monoʳ-≤ : ∀ (m p q : ℕ)
  → p ≤ q
  -------------
  → m + p ≤ m + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc m) p q p≤q  =  s≤s (+-monoʳ-≤ m p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
  -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

-- Strict inequality
infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ}
    ------------
    → zero < suc n
  s<s : ∀ {m n : ℕ}
    → m < n
    -------------
    → suc m < suc n

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero :
    ---------
    even zero
  suc  : ∀ {n : ℕ}
    → odd n
    ------------
    → even (suc n)

data odd where
  suc   : ∀ {n : ℕ}
    → even n
    -----------
    → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
  ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
  -----------
  → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)


-- Exercise
-------------------------------

-- Give an example of a preorder that is not a partial order.
-- thin category

-- Give an example of a partial order that is not a total order.
-- ⊂ on Sets


-- The above proof omits cases where one argument is z≤n and one argument is s≤s. Why is it ok to omit them?
-- Because in those cases unification fails

--Show that multiplication is monotonic with regard to inequality.
*-monoʳ-≤ : ∀ (m p q : ℕ) → p ≤ q → m * p ≤ m * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc m) p q p≤q = +-mono-≤ p q (m * p) (m * q) p≤q (*-monoʳ-≤ m p q p≤q)
-- p + m p <= q + m p <= q + m q

*-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-monoˡ-≤ m n zero m≤n rewrite *-comm m zero | *-comm n zero  = z≤n
*-monoˡ-≤ m n (suc p) m≤n rewrite *-comm m (suc p) | *-comm n (suc p) = *-monoʳ-≤ (suc p) m n m≤n
-- m (s p) <= n (s p)
-- (sp m <= sp n

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)


<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s _) = z<s
<-trans (s<s m≤n) (s<s n≤p) = s<s (<-trans m≤n n≤p)

-- trichotomy
data Trichotomy (m n : ℕ) : Set where
  forward : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  backword : n < m → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = eq refl
<-trichotomy zero (suc n) = forward z<s
<-trichotomy (suc m) zero = backword z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n
...                            | forward m<n = forward (s<s m<n)
...                            | eq refl = eq refl
...                            | backword n<m = backword (s<s n<m)

+-monoʳ-< : ∀ (m p q : ℕ) → p < q → m + p < m + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc m) p q p<q = s<s (+-monoʳ-< m p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monoˡ-< m n zero m<n rewrite +-comm m zero | +-comm n zero = m<n
+-monoˡ-< m n (suc p) m<n rewrite +-comm m (suc p) | +-comm n (suc p) = s<s (+-monoʳ-< p m n m<n)

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoʳ-< m p q p<q) (+-monoˡ-< m n q m<n)

≤-iff-< : ∀ {m n : ℕ} → (suc m) ≤ n → m < n
≤-iff-< {zero} {suc n} (s≤s .{zero} .{n} z≤n) = z<s
-- ≤-iff-< .{zero} .{(suc n)} (s≤s {zero} {n} z≤n) = z<s
≤-iff-< {suc m} {suc n} (s≤s .{(suc m)} .{n} sm≤n) = s<s (≤-iff-< sm≤n)
-- ≤-iff-< .{(suc m)} .{(suc n)} (s≤s {suc m} {n} sm≤n) = s<s (≤-iff-< sm≤n)


<-iff-≤ : ∀ {m n : ℕ} → m < n → (suc m) ≤ n
-- <-iff-≤ .{zero} {suc n} (z<s .{n}) = s≤s z≤n
<-iff-≤ .{zero} .{(suc n)} (z<s {n}) = s≤s z≤n
-- <-iff-≤ {suc m} {suc n} (s<s .{m} .{n} m<n) = s≤s (<-iff-≤ m<n)
<-iff-≤ .{(suc m)} .{(suc n)} (s<s {m} {n} m<n) = s≤s (<-iff-≤ m<n)

≤-suc : ∀ {n : ℕ} → n ≤ suc n
≤-suc {zero} = z≤n
≤-suc {suc n} = s≤s ≤-suc

<-trans-revisited : ∀ {m n p : ℕ} → m < n → n < p → m < p
-- m<n sm<=n n<p sn<=p
<-trans-revisited m<n n<p = ≤-iff-< (≤-trans (<-iff-≤ m<n) (≤-trans ≤-suc (<-iff-≤ n<p)))
-- using ≤-trans and ...

-- o+e≡o
-- e+e≡e
o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
e+o≡o : ∀ {m n : ℕ} → even m → odd n → odd (m + n)

e+o≡o zero on = on
e+o≡o (suc om) on = suc (o+o≡e om on)
o+o≡e (suc em) on = suc (e+o≡o em on)

open import plfa.Induction

data One : Bin → Set where
  one : One (x1 nil)
  x0_ : ∀ {b : Bin} → One b → One (x0 b)
  x1_ : ∀ {b : Bin} →  One b → One (x1 b)

data Can : Bin → Set where
  zero : Can (x0 nil)
  can : {b : Bin} → One b → Can b

propertyOne1 : ∀ {b : Bin} → One b → One (inc b)
propertyOne1 one = x0 one
propertyOne1 (x0 ob) = x1 ob
propertyOne1 (x1 ob) = x0 propertyOne1 ob

propertyCan1 : ∀ {b : Bin} → Can b → Can (inc b)
propertyCan1 zero = can one
propertyCan1 (can x) = can (propertyOne1 x)

propertyCan2 : ∀ (n : ℕ) → Can (to n)
propertyCan2 zero = zero
propertyCan2 (suc n) = propertyCan1 (propertyCan2 n)


-- works on canonical
_+b_ : ∀ (b c : Bin) → Bin
nil +b c = c
b +b nil = b
(x0 b) +b (x0 c) = x0 (b +b c)
(x0 b) +b (x1 c) = x1 (b +b c)
(x1 b) +b (x0 c) = x1 (b +b c)
(x1 b) +b (x1 c) = x0 inc (b +b c)

+b-identityˡ-x0nil : (b : Bin) → Can b → (x0 nil) +b b ≡ b
+b-identityˡ-x0nil .(x0 nil) zero = refl
+b-identityˡ-x0nil .(x1 nil) (can one) = refl
+b-identityˡ-x0nil .(x0 _) (can (x0 x)) = refl
+b-identityˡ-x0nil .(x1 _) (can (x1 x)) = refl

-- not necessary canonical
+b-incˡ : ∀(b c : Bin) → inc b +b c ≡ inc (b +b c)
+b-incˡ nil nil = refl
+b-incˡ nil (x0 c) = refl
+b-incˡ nil (x1 c) = refl
+b-incˡ (x0 b) nil = refl
+b-incˡ (x0 b) (x0 c) = refl
+b-incˡ (x0 b) (x1 c) = refl
+b-incˡ (x1 b) nil = refl
+b-incˡ (x1 b) (x0 c) = cong x0_ (+b-incˡ b c)
+b-incˡ (x1 b) (x1 c) = cong x1_ (+b-incˡ b c)

double : ∀ {b : Bin} → One b → (b +b b) ≡ (x0 b)
double one = refl
double (x0 ob) = cong x0_ (double ob)
double {b} (x1 ob) rewrite double ob = refl

to-homomorphism : ∀ (m n : ℕ) → to (m + n) ≡ to m +b to n
to-homomorphism zero zero = refl
to-homomorphism zero (suc n) with propertyCan2 (suc n)
... | property rewrite +b-identityˡ-x0nil (inc (to n)) (propertyCan2 (suc n)) = refl
to-homomorphism (suc m) n rewrite to-homomorphism m n = sym (+b-incˡ (to m) (to n))

propertyOne3 : ∀ {b : Bin} → One b → to (from b) ≡ b
propertyOne3 one = refl
-- cancel .b
propertyOne3 {x0 b} (x0 ob) rewrite plfa.Induction.+-comm (from b) 0 | to-homomorphism (from b) (from b) | propertyOne3 {b} ob = double ob
propertyOne3 {x1 b} (x1 ob) rewrite plfa.Induction.+-comm (from b) 0 | to-homomorphism (from b) (from b) | propertyOne3 {b} ob | double ob = refl

propertyCan3 : ∀ {b : Bin} → Can b → to (from b) ≡ b
propertyCan3 zero = refl
propertyCan3 (can x) = propertyOne3 x
