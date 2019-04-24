module plfa.Decidable where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.Relations using (_<_; z<s; s<s)
open import plfa.Isomorphism using (_⇔_)


infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}   → zero ≤ n
  s≤s : ∀ {m n : ℕ}
    → m ≤ n → suc m ≤ suc n

data Bool : Set where
  true  : Bool
  false : Bool

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n       =  true
suc m ≤ᵇ zero   =  false
suc m ≤ᵇ suc n  =  m ≤ᵇ n

2≤4 : (2 ≤ᵇ 4) ≡ true
2≤4 = refl
4≤2 : (4 ≤ᵇ 2) ≡ false
4≤2 = refl

T : Bool → Set
T true   =  ⊤
T false  =  ⊥

-- while there is no possible evidence that T b holds if b is false.
-- while if b is false then T b in uninhabited.
T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt   =  refl
T→≡ false ()

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl  =  tt

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero n = λ _ → z≤n
≤ᵇ→≤ (suc m) zero = λ ()
≤ᵇ→≤ (suc m) (suc n) = λ x → s≤s (≤ᵇ→≤ m n x)


≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n = tt
≤→≤ᵇ (s≤s mn) = ≤→≤ᵇ mn
-- we consider only cases where the relation holds, and can ignore those where it does not.

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n
-- Just like ≤-pred

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤? n = yes z≤n
suc m ≤? zero = no ¬s≤z
suc m ≤? suc n with m ≤? n
... | yes m≤n = yes (s≤s m≤n)
... | no  m≰n = no (¬s≤s m≰n)
-- Again, with is necessary
-- Because inductive condition is packed

-- the definition of _≤?_ proves itself correct,
-- as attested to by its type.
-- The code of _≤?_ is far more compact than the combined code of _≤ᵇ_, ≤ᵇ→≤, and ≤→≤ᵇ


-- While using no, definitly define a helper

_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        | true   | p        | _            = yes (p tt)
...        | false  | _        | ¬p           = no ¬p

-- Putting the expressions into the with clause permits Agda to exploit the fact that
-- T (m ≤ᵇ n) is ⊤ when m ≤ᵇ n is true, and that T (m ≤ᵇ n) is ⊥ when m ≤ᵇ n is false.

⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋  =  true
⌊ no ¬x ⌋  =  false

-- Using erasure, we can easily derive _≤ᵇ_ from _≤?_:
_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n  =  ⌊ m ≤? n ⌋

toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes a} = λ _ → a
toWitness {A} {no ¬a} = λ ()
fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes a} = λ _ → tt
fromWitness {A} {no ¬a} = ¬a

≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤  =  toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′  =  fromWitness

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
false ∧ _     = false
_     ∧ false = false

infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ{ ⟨ x , y ⟩ → ¬x x }
_     ×-dec no ¬y = no λ{ ⟨ x , y ⟩ → ¬y y }

-- gray means check passed but swap changes result

infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _      = true
_     ∨ true   = true
false ∨ false  = false


infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
_     ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }

not : Bool → Bool
not true  = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x)  =  no (¬¬-intro x)
¬? (no ¬x)  =  yes ¬x

_⊃_ : Bool → Bool → Bool
_     ⊃ true   =  true
false ⊃ _      =  true
true  ⊃ false  =  false

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_     →-dec yes y  =  yes (λ _ → y)
no ¬x →-dec _      =  yes (λ x → ⊥-elim (¬x x))
yes x →-dec no ¬y  =  no (λ f → ¬y (f x))



-- Exercise
--------------------------------------------------------------------------
¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s ¬m<n = λ {(s<s sm<sn) → ¬m<n sm<sn}

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero <? zero = no (λ ())
zero <? (suc n) = yes z<s
suc m <? zero = no (λ ())
suc m <? suc n with m <? n
... | yes m<n = yes (s<s m<n)
... | no  n<m = no (¬s<s n<m)

pred : ∀ (n : ℕ) → ℕ
pred zero = zero
pred (suc n) = n

s≢s : ∀ {m n : ℕ} → ¬ (m ≡ n) → ¬ (suc m ≡ suc n)
s≢s m≢n sm≡sn = m≢n (cong pred sm≡sn)

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc n = no (λ ())
suc m ≡ℕ? zero = no (λ ())
suc m ≡ℕ? suc n with m ≡ℕ? n
... | yes m≡n = yes (cong suc m≡n)
... | no  m≢n = no (s≢s m≢n)


∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× (yes x) (yes x₁) = refl
∧-× (yes x) (no x₁) = refl
∧-× (no x) (yes x₁) = refl
∧-× (no x) (no x₁) = refl

∨-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-× (yes x) (yes x₁) = refl
∨-× (yes x) (no x₁) = refl
∨-× (no x) (yes x₁) = refl
∨-× (no x) (no x₁) = refl

not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ (yes x) = refl
not-¬ (no x) = refl

_iff_ : Bool → Bool → Bool
true iff true = true
true iff false = false
false iff true = false
false iff false = true

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes a ⇔-dec yes b = yes (record { to = λ _ → b ; from = λ _ → a })
yes a ⇔-dec no ¬b = no λ z → ¬b (_⇔_.to z a)
no a ⇔-dec yes b = no λ z → a (_⇔_.from z b)
no ¬a ⇔-dec no ¬b = yes (record { to = λ {a → ⊥-elim (¬a a)} ; from = λ b → ⊥-elim (¬b b) })

iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
iff-⇔ (yes x) (yes x₁) = refl
iff-⇔ (yes x) (no x₁) = refl
iff-⇔ (no x) (yes x₁) = refl
iff-⇔ (no x) (no x₁) = refl
