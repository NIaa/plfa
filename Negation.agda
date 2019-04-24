module plfa.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import plfa.Isomorphism using (_≃_; extensionality)
open import plfa.Relations using (_<_; z<s; s<s)
open import Function using (_∘_)


¬_ : Set → Set
¬ A = A → ⊥
-- S → S, higher lv

¬-elim : ∀ {A : Set} → ¬ A  → A → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro x = λ z → z x

¬¬-intro′ : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

-- We cannot show that ¬ ¬ A implies A,
-- but we can show that ¬ ¬ ¬ A implies ¬ A:
¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
--¬¬¬-elim nnna na = nnna (λ z → z na)
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)
--                       elim : ⊥

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

-- data _≡_ {a} {A : Set a} (x : A) : A → Set a where
--   instance refl : x ≡ x

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)
-- x ≡ y false, ⊥, then every thing, get.
-- ⊥ → ⊥ -- ⊥ → Anything
-- ⊤ → ⊥ -- no constructor

_ : 1 ≢ 2
_ = λ ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ ()

-- indeed, there is exactly one proof of ⊥ → ⊥
id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

-- holds if for every x, NO x
id≡id′ : id ≡ id′
id≡id′ = extensionality λ ()

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

-- Excluded middle is irrefutable
postulate
  em : ∀ {A : Set} → A ⊎ ¬ A
-- the law of the excluded middle does not hold in intuitionistic logic.       cannot construct such a type
-- However, we can show that it is irrefutable
em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
--em-irrefutable k = k (inj₂ λ a → k (inj₁ a))
em-irrefutable k = k (inj₂ λ a → k (inj₁ a))
-- Goal: ¬ (¬ (.A ⊎ ¬ .A))
-- input    k is  {(A ⊎ ¬ A) → ⊥}
-- output        ⊥
-- need a ⊎ ¬ a

-------------------------------------------
-- Exercise
--------------------------------------------

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive {zero} = λ ()
<-irreflexive {suc n} = λ {(s<s n<n) → <-irreflexive n<n}
--- m < n = suc m ≤ n
--<-irreflexive : ∀{n : ℕ} → ¬ n < n
--<-irreflexive (s<s n<n) = <-irreflexive n<n
-- IS THIS BECAUSE infixr ≡ reasoning?

-- Show that strict inequality satisfies trichotomy,
-- that is, for any naturals m and n exactly one of the following holds:

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


pred : ∀ (n : ℕ) → ℕ
pred zero = zero
pred (suc n) = n

<-pred : ∀ {n m : ℕ} → suc n plfa.Relations.< suc m → n plfa.Relations.< m
<-pred (plfa.Relations.s<s a) = a

data Tri (A B C : Set) : Set where
  tri< : ( a :   A) (¬b : ¬ B) (¬c : ¬ C) → Tri A B C
  tri≈ : (¬a : ¬ A) ( b :   B) (¬c : ¬ C) → Tri A B C
  tri> : (¬a : ¬ A) (¬b : ¬ B) ( c :   C) → Tri A B C
-- exactly one of the following holds:
-- when one holds the negation of the other two must also hold.
<-trichotomy-Exact : ∀ (m n : ℕ) → Tri (m < n) (m ≡ n) (n < m)
<-trichotomy-Exact zero zero = tri≈ (λ ()) refl (λ ())
<-trichotomy-Exact zero (suc n) = tri< z<s (λ ()) (λ ())
<-trichotomy-Exact (suc m) zero = tri> (λ ()) (λ ()) z<s
<-trichotomy-Exact (suc m) (suc n) with <-trichotomy-Exact m n
... | tri< m<n m≢n n≮m = tri< (s<s m<n) (λ sm≡sn → m≢n (cong pred sm≡sn)) (n≮m ∘ <-pred)
... | tri≈ m≮n m≡n n≮m = tri≈ (λ {sm<sn → m≮n (<-pred sm<sn)}) (cong suc m≡n) λ z → n≮m (<-pred z)
... | tri> m≮n m≢n n<m = tri> (λ z → m≮n (<-pred z)) (m≢n ∘ cong pred) (s<s n<m)
-- in fact, it's simple, just build ⊥ from a ¬
-- all para to original

-- have m≢n              ¬ (m ≡ n)
-- need (sm ≢ sn)        ¬ (sm ≡ sn)
-- (¬b ∘ cong pred) var
-- ((m ≡ n) → ⊥)

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = record {
    to = λ { nAB → ⟨ (λ z → nAB (inj₁ z)) , (λ z → nAB (inj₂ z))  ⟩ }
  ; from = λ {⟨ nA , nB ⟩ → λ {(inj₁ A) → nA A ; (inj₂ B) → nB B  } }
  ; from∘to = λ {nAB → extensionality λ {(inj₁ A) → refl; (inj₂ B) → refl} }
  ; to∘from = λ {⟨ na , nb ⟩ → refl}
  }
--  extensionality : ∀ {A B : Set} {f g : A → B}
--    → (∀ (x : A) → f x ≡ g x)
--    -----------------------
--    → f ≡ g

--        λ x → somekind of refl



---------------------------------------
-- classical
---------------------------------------
-- Stable
Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-stab : ∀ {A : Set} → Stable (¬ A)
¬-stab = ¬¬¬-elim

∧-stab : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
∧-stab sa sb =  λ k → ⟨ sa (λ q → k λ ab → q (Data.Product.proj₁ ab)) ,                              -- hand
                        sb (λ z → z (sb (λ z₁ → k (λ z₂ → z₁ (Data.Product.proj₂ z₂))))) ⟩           -- auto
-- I DK

{-
In classical logic, we have that A is equivalent to ¬ ¬ A. As we discuss below,
in Agda we use intuitionistic logic, where we have
  #### only half of this equivalence, namely that A implies ¬ ¬ A:


Intuitionists, concerned by assumptions made by some logicians about the nature of infinity,
insist upon a constructionist notion of truth.
In particular, they insist that
  #### a proof of A ⊎ B must show which of A or B holds,

Intuitionists also reject the law of the excluded middle,
which asserts A ⊎ ¬ A for every A, since the law gives no clue as to which of A or ¬ A holds.

Propositions as Types was first formulated for intuitionistic logic.
It is a perfect fit, because in the intuitionist interpretation the formula A ⊎ B is provable exactly when one exhibits either a proof of A or a proof of B,
so the type corresponding to disjunction is a disjoint sum.
-}
