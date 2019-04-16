module plfa.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
    -----------------------
    → f ≡ g

_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)
same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n where
  helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
  helper m zero = refl
  helper m (suc n) = cong suc (helper m n)
-- Looks like with, but have to apply comm
-- helper is more convenient

same : _+′_ ≡ _+_
same = extensionality (λ n → extensionality (same-app n))
-- only tool is extensionality

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_
-- field (parameter of the type)

-- A record declaration is equivalent to a corresponding inductive data declaration:
data _≃′_ (A B : Set): Set where
  mk-≃′ : ∀ (to : A → B) →
    ∀ (from : B → A) →
    ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
    ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
    A ≃′ B
-- to construct, need all 4 things above, which is reasonable
to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f
from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g
from∘to′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (x : A) → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f
to∘from′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g
{-
data ⊥ : Set where
record ⊤ : Set where
  tt : ⊤
  tt = record {}
-- Single trival construction

data ⊤ : Set where
  t : ∀ (tt : ⊤) → ⊤
tt = record
-}

-- Syntax still table like
≃-refl : ∀ {A : Set} → A ≃ A
≃-refl = record
           { to = λ z → z
           ; from = λ z → z
           ; from∘to = λ x → refl
           ; to∘from = λ y → refl
           }

≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B = record
  { to = from A≃B
  ; from = to A≃B
  ; from∘to = to∘from A≃B
  ; to∘from = from∘to A≃B
  }

≃-trans : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C = record
  { to = λ z → to B≃C (to A≃B z)
  ; from = from A≃B ∘ from B≃C
  ; from∘to = λ x → from A≃B (from B≃C (to B≃C (to A≃B x)))
            ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩  from A≃B (to A≃B x) -- you need some refl, and from, to stick together
            ≡⟨ from∘to A≃B x ⟩ x
            ∎
  -- A -> A≡A
  ; to∘from = λ x → trans (cong (to B≃C) (to∘from (A≃B) (from B≃C x))) (to∘from B≃C x)
  -- no difficulty, just you didn't realize
  -- C -> C≡C
  }

-- Convenient to construct upon any equational relation

module ≃-Reasoning where
  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set} → A ≃ B → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≃ B → B ≃ C → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set) → A ≃ A
  A ≃-∎ = ≃-refl
open ≃-Reasoning

-- embedding, to sth bigger
infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_


≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =  record
  {to = λ z → z
  ;from = λ z → z
  ;from∘to = λ x → refl
  }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C = record
  {to = λ z → to B≲C (to A≲B z)
  ;from = λ z → from A≲B (from B≲C z)
  ;from∘to = λ x → trans (cong (from A≲B) (from∘to B≲C (to A≲B x))) (from∘to A≲B x)
  }


≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
  → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to = record
  {to = from B≲A
  ;from = to B≲A
  ;to∘from = from∘to B≲A
  ;from∘to = λ x → to B≲A (from B≲A x)
    ≡⟨ cong (to B≲A) (sym (cong-app to≡from x)) ⟩ to B≲A (to A≲B x)
    -- because it's function type ≡ refl, only have
    ≡⟨ sym (cong-app from≡to (to A≲B x)) ⟩ from A≲B (to A≲B x)
    ≡⟨ from∘to A≲B x ⟩ x ∎

    -- seems C-A not working because of f ≡ g
  }

≲-antisym' : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
  → A ≃ B
≲-antisym' A≲B B≲A to≡from from≡to =
  record
    { to      = to A≲B
    ; from    = from A≲B
    ; to∘from = λ{y →
      begin
        to A≲B (from A≲B y)
      ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
        to A≲B (to B≲A y)
      ≡⟨ cong-app to≡from (to B≲A y) ⟩
        from B≲A (to B≲A y)
      ≡⟨ from∘to B≲A y ⟩
        y
      ∎}
     ; from∘to = from∘to A≲B
     }
-- Because 4 terms are related.

module ≲-Reasoning where
  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎
  ≲-begin_ : ∀ {A B : Set} → A ≲ B → A ≲ B
  ≲-begin A≲B = A≲B
  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≲ B → B ≲ C → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C
  _≲-∎ : ∀ (A : Set) → A ≲ A
  A ≲-∎ = ≲-refl
open ≲-Reasoning


--------------------------------------------------------
-- Exercise

-- Show that every isomorphism implies an embedding.
≃-implies-≲ : ∀ {A B : Set} → A ≃ B → A ≲ B
≃-implies-≲ AB  = record
  { to = to AB
  ; from = from AB
  ; from∘to = from∘to AB
  }

-- Define equivalence of propositions (also known as “if and only if”) as follows:
-- Show that equivalence is reflexive, symmetric, and transitive.
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
⇔-refl : ∀ {A : Set} → A ⇔ A
⇔-refl = record { to = λ z → z ; from = λ z → z }
⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym = λ z → record { to = _⇔_.from z ; from = _⇔_.to z }
⇔-trans : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans = λ z z₁ →
              record
              { to = λ z₂ → _⇔_.to z₁ (_⇔_.to z z₂)
              ; from = λ z₂ → _⇔_.from z (_⇔_.from z₁ z₂)
              }

-- Using the above, establish that there is an embedding of ℕ into Bin.


open import plfa.Induction renaming (from to from'; to to to')
open import plfa.Relations

ℕ≲bin : ℕ ≲ Bin
ℕ≲bin = record
  {
  from = from'
  ; to  = to'
  ; from∘to = from∘to-id
  }


-- import Function using (_∘_)
-- import Function.Inverse using (_↔_)
-- import Function.LeftInverse using (_↞_)
