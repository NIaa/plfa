module plfa.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂ ; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.Isomorphism using (_≃_; extensionality)

open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm; +-cancelˡ-≡)

-- Universals 任意 对所有元素成立
-- ∀ A     {A : _}
--  unpack₂ : ∀ {A B} → Id A → Id B → A
--  unpack₃ : ∀ {A} (_ : Id A) {B} → Id B → A

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
  -----------------
  → B M
∀-elim L M = L M
-- Functions arise as a special case of dependent functions,
-- When a function is viewed as evidence of implication,
-- both its argument and result are viewed as evidence,
-- whereas when a dependent function is viewed as evidence of a universal,
-- its argument is viewed as an element of a data type and its result is viewed as
-- evidence of a proposition that depends on the argument.


-- Existentials 存在 对特定元素成立
-- Variable x appears free in B x but bound in Σ[ x ∈ A ] B x
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

-- Products arise as a special case of existentials,
-- does not depend on a variable drawn from the first component
-- When a function is viewed as evidence of implication, both its argument and result are viewed as evidence,
-- While viewed as evidence of an existential,
-- the first component is viewed as an element of a datatype
-- and the second component is viewed as evidence of a proposition that depends on the first component.

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B
--  constructor ⟨_,_⟩ (x : A)  B x

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
  ---------------
  → C
∃-elim f = λ { ⟨ x , y ⟩ → f x y }

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set} → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying = record
  { to = λ f → λ { ⟨ x , y ⟩ → f x y}
  ; from = λ g x y → g ⟨ x , y ⟩
  ; from∘to = λ f → refl
  ;  to∘from = λ {g → extensionality λ { ⟨ x , y ⟩ → refl } }
  }

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc : ∀ {n : ℕ}
    → odd n
    ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
    -----------
    → odd (suc n)

-- even n iff ∃[ m ] ( m * 2 ≡ n)
-- odd n iff ∃[ m ] (1 + m * 2 ≡ n)


-- We induct over the evidence that n is even or odd:
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)
even-∃ even-zero = ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
... | ⟨ h , eql ⟩  = ⟨ suc h , cong suc eql ⟩
odd-∃ (odd-suc e) with even-∃ e
... | ⟨ h , eql ⟩ = ⟨ h , cong suc eql ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n
∃-even ⟨ zero , refl ⟩ = even-zero
∃-even ⟨ suc x , refl ⟩ = even-suc (∃-odd ⟨ x , refl ⟩)
∃-odd ⟨ x , refl ⟩ = odd-suc (∃-even ⟨ x , refl ⟩)

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ = record
  { to = λ lhs x y → lhs ⟨ x , y ⟩
  ; from = λ rhs → λ {⟨ x , y ⟩ → rhs x y}
  ; from∘to = λ {lhs → extensionality λ { ⟨ x , y ⟩ → refl}}
  ; to∘from = λ rhs → refl }

-- again, func var → refl

-----------------------------------------
-- Exercise
-- →-distrib-⊎; →-distrib-×;
-- ×-distrib-⊎; ⊎-distrib-×;
-- ∀-distrib-×;

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× = record
  { to = λ f → ⟨ (λ x → proj₁ (f x)) , (λ x → proj₂ (f x)) ⟩
  ; from = λ {⟨ ab , ac ⟩ → λ a → ⟨ ab a , ac a ⟩}
  ; from∘to = λ f → refl
  ; to∘from = λ {⟨ ab , ac ⟩ → refl} }


⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (_⊎_.inj₁ ab) = λ a → _⊎_.inj₁ (ab a)
⊎∀-implies-∀⊎ (_⊎_.inj₂ ac) = λ a → _⊎_.inj₂ (ac a)

--⊎∀-implies-∀⊎ (_⊎_.inj₁ ab) = λ a → _⊎_.inj₁ (ab a)
--⊎∀-implies-∀⊎ (_⊎_.inj₂ ac) = λ a → _⊎_.inj₂ (ac a)



suc+1 : ∀ (n : ℕ) → suc n ≡ n + 1
suc+1 zero = refl
suc+1 (suc n) = cong suc (suc+1 n)

-- twisted
∃-even' : ∀ {n : ℕ} → ∃[ m ] (2 * m ≡ n) → even n
∃-odd' :  ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) → odd n
∃-even' ⟨ zero , refl ⟩ = even-zero
∃-even' ⟨ suc n , refl ⟩ with ∃-odd' ⟨ n , refl ⟩
... | e rewrite +-identityʳ n | suc+1 n | sym (+-assoc n n 1) = even-suc e where
∃-odd' ⟨ n , refl ⟩ with ∃-even' ⟨ n , refl ⟩
... | e rewrite +-identityʳ n | sym (suc+1 (n + n)) = odd-suc e


≤-+-∃ : ∀ (y z : ℕ) → y ≤ z → ∃[ x ] (x + y ≡ z)
≤-+-∃ zero n _≤_.z≤n = ⟨ n , +-identityʳ n ⟩
≤-+-∃ (suc m) (suc n) (_≤_.s≤s m≤n) with ≤-+-∃ m n m≤n
... | ⟨ k , eql ⟩ rewrite sym eql | +-comm k m = ⟨ k , +-comm k (suc m) ⟩



∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
  --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , y ⟩ ∀x→Bx = y (∀x→Bx x)


open import plfa.Relations using (One; one; x0_; x1_; Can; zero; can;  propertyCan2; propertyCan3)
--open import plfa.Relations
open import plfa.Induction
-- notice the type signature

-- cannot use!!
-- helpme : (b : Bin) (canb : Can b) → propertyCan2 (from b ) ≡ canb

Single : ∀{A : Set} → (A → Set) → Set
Single {A} B = ∀{x : A} (b1 b2 : B x) → b1 ≡ b2

One-Single : Single One
One-Single one one = refl
One-Single one (x1 ())
One-Single (x0 o1) (x0 o2) rewrite One-Single o1 o2 = refl
One-Single (x1 ()) one
One-Single (x1 o1) (x1 o2) rewrite One-Single o1 o2 = refl

Can-Single : Single Can
Can-Single zero zero = refl
Can-Single zero (can (x0 ()))
Can-Single (can (x0 ())) zero
Can-Single (can o1) (can o2) = cong can (One-Single o1 o2)

Σtup : ∀{A : Set} {B : A → Set}
  → (x : A) → B x → Σ A B
Σtup = ⟨_,_⟩

Σ-functional : ∀{A : Set} {B : A → Set} {x y : A}
  → x ≡ y
  → Single B
  → (Bx : B x)
  → (By : B y)
  → Σtup x Bx ≡ Σtup y By
Σ-functional refl sgl Bx By rewrite sgl Bx By = refl

{-
ℕ≃Can : ∀ {b : Bin} → ℕ ≃ ∃[ x ](Can x)
ℕ≃Can = record
  { to = λ n → ⟨ to n , propertyCan2 n ⟩
  ; from = λ {⟨ b , _ ⟩ → from b}
  ; from∘to = from∘to-id
  ; to∘from = λ {⟨ b , canb ⟩ → {!!}}
  }
-}

--------------------------------------
-- I DON'T GET IT!!!!!!!!!!!!!!!!!!!!
--------------------------------------
