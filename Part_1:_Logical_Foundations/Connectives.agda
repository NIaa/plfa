module plfa.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_; _≲_; _⇔_; extensionality)
open plfa.Isomorphism.≃-Reasoning
-- mod in mod

-- Conjunction is product
data _×_ (A : Set) (B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

record _×′_ (A B : Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B
open _×′_
-- introducing a conjunction | eliminating a conjunction

data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_


×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to       =  λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from     =  λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to  =  λ{ ⟨ x , y ⟩ → refl }
    ; to∘from  =  λ{ ⟨ y , x ⟩ → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

-- no elimination rule
-- Given evidence that ⊤ holds, there is nothing more of interest we can conclude.
data ⊤ : Set where
  tt :
    --
    ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

-- ⊤ is identity of Set × "1"
⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ = record {
    to = λ {⟨ tt , a ⟩ → a}
  ; from = ⟨_,_⟩ tt
  ; to∘from = λ y → refl
  ; from∘to = λ {⟨ tt , a ⟩ → refl }
  }
-- specify tt
⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
--⊤-identityʳ {A} = {!×-comm A ⊤!}
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
  A
  ≃-∎
-- rewrite, trans are for ≡, here is ≃, import them

-- ⊥ is



-- Disjunction is sum
data _⊎_ : Set → Set → Set where
  inj₁ : ∀ {A B : Set}
    → A
    -----
    → A ⊎ B
  inj₂ : ∀ {A B : Set}
    → B
    -----
    → A ⊎ B

-- eliminating a disjunction
case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
  -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ x) = g x

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infix 1 _⊎_
-- Thus, A × C ⊎ B × C parses as (A × C) ⊎ (B × C).

-- False is empty
data ⊥ : Set where
-- no clauses!
⊥-elim : ∀ {A : Set}
  → ⊥
  --
  → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

-- Implication is function
-- Defining a function, with a named definition or a lambda abstraction,
-- is referred to as introducing a function,
-- while applying a function is referred to as eliminating the function.
η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying = record {
   to = λ {f → λ {⟨ x , y ⟩ → f x y}}
  ;from = λ {g → λ {x y → g ⟨ x , y ⟩}}
  ;from∘to = λ f → refl
  ;to∘from = λ {g → extensionality λ {⟨ x , y ⟩ → refl} } 
  }

-- c^(a+b) ≡ c^a * c^b

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ = record {
    to = λ f → ⟨ (λ x → f (inj₁ x)) , (λ x → f (inj₂ x)) ⟩
  ; from = λ {⟨ ac , bc ⟩ → λ { (inj₁ x) → ac x ; (inj₂ x) → bc x } }
  ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
  ; to∘from = λ {⟨ g , h ⟩ → refl}
  }

-- (bc) ^ a = b^a c^a
→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× = record
  { to = λ {f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩}
  ; from = λ { ⟨ ab , ac ⟩ → λ { a → ⟨ ab a , ac a ⟩ }}
  ; from∘to = λ {a→bc → extensionality λ {a → η-× (a→bc a)}}
  ; to∘from = λ {⟨ ab , bc ⟩ → refl}
  }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ = record {
    to = λ {⟨ inj₁ a , c ⟩ → inj₁ ⟨ a , c ⟩ ; ⟨ inj₂ b , c ⟩ → inj₂ ⟨ b , c ⟩ }
  ; from = λ { (inj₁ ⟨ a , c ⟩) → ⟨ inj₁ a , c ⟩ ; (inj₂ ⟨ b , c ⟩) → ⟨ inj₂ b , c ⟩ }
  ; from∘to = λ {⟨ inj₁ a , c ⟩ → refl; ⟨ inj₂ b , c ⟩ → refl }
  ; to∘from = λ {(inj₁ ⟨ a , c ⟩) → refl ; (inj₂ ⟨ b , c ⟩) → refl }
  }

-- a * b + c ≤ (a + c) * (b + c)
⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× = record {
    to = λ { (inj₁ ⟨ a , b ⟩) → ⟨ inj₁ a , inj₁ b ⟩ ; (inj₂ c) → ⟨ inj₂ c , inj₂ c ⟩ }
  ; from = λ {⟨ inj₁ a , inj₁ b ⟩ →  inj₁ ⟨ a , b ⟩
           ;  ⟨ inj₂ c , inj₁ b ⟩ →  inj₂ c
           ;  ⟨ inj₁ a , inj₂ c ⟩ → inj₂ c
           ;  ⟨ inj₂ c , inj₂ c' ⟩ → inj₂ c -- c or c'
           }
  ; from∘to = λ { (inj₁ ⟨ a , b ⟩) → refl ; (inj₂ c) → refl }
  }

--------------------------------------------------------------------
-- Exercise

--- Show that A ⇔ B as defined earlier is isomorphic to (A → B) × (B → A).
⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× = record {
  to = λ A⇔B → ⟨ _⇔_.to A⇔B , _⇔_.from A⇔B ⟩
  ; from = λ {⟨ A→B , B→A ⟩ → record { to = A→B ; from = B→A }}
  ; from∘to = λ A⇔B → refl
  ; to∘from = λ {⟨ A→B , B→A ⟩  → refl}
  }

-------------------------------------------------------
---------------------------------------------------------
--------------------------------------------------
----------------------------------------------
---------------------------- S. H. I. T. --------------------
⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm {A} {B} = record {
    from = helperF
  ; to = helperT
  ; to∘from = helperTF
  ; from∘to = helperFT
  } where
    helperF : B ⊎ A → A ⊎ B
    helperF (inj₁ x) = inj₂ x
    helperF (inj₂ x) = inj₁ x
    helperT : A ⊎ B → B ⊎ A
    helperT (inj₁ x) = inj₂ x
    helperT (inj₂ x) = inj₁ x
    helperTF : (ba : B ⊎ A) → helperT (helperF ba) ≡ ba
    helperTF (inj₁ x) = refl
    helperTF (inj₂ x) = refl
    helperFT : (ab : A ⊎ B) → helperF (helperT ab) ≡ ab
    helperFT (inj₁ x) = refl
    helperFT (inj₂ x) = refl


⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc {A} {B} {C} = record {
    from = helperF
  ; to = helperT
  ; to∘from = helperTF
  ; from∘to = helperFT
  } where
  helperT : (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
  helperT (inj₁ (inj₁ x)) = inj₁ x
  helperT (inj₁ (inj₂ x)) = inj₂ (inj₁ x)
  helperT (inj₂ x) = inj₂ (inj₂ x)
  helperF : A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
  helperF (inj₁ x) = inj₁ (inj₁ x)
  helperF (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
  helperF (inj₂ (inj₂ x)) = inj₂ x
  helperTF : (abc : A ⊎ (B ⊎ C)) → helperT (helperF abc) ≡ abc
  helperTF (inj₁ x) = refl
  helperTF (inj₂ (inj₁ x)) = refl
  helperTF (inj₂ (inj₂ x)) = refl
  helperFT : (abc : (A ⊎ B) ⊎ C) → helperF (helperT abc) ≡ abc
  helperFT (inj₁ (inj₁ x)) = refl
  helperFT (inj₁ (inj₂ x)) = refl
  helperFT (inj₂ x) = refl

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ {A} = record {
   to = helperT
  ;from = inj₂
  ;from∘to = helperFT
  ;to∘from = λ y → refl
  } where
  helperT : ⊥ ⊎ A → A
  helperT (inj₁ ())
  helperT (inj₂ a) = a
  helperFT : (ta : ⊥ ⊎ A) → inj₂ (helperT ta) ≡ ta
  helperFT (inj₁ ())
  helperFT (inj₂ x) = refl

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ {A} = record {
    to = helperT
  ; from = inj₁
  ; from∘to = helperFT
  ; to∘from = λ y → refl
  } where
  helperT : A ⊎ ⊥ → A
  helperT (inj₁ x) = x
  helperT (inj₂ ())
  helperFT : (at : A ⊎ ⊥) → inj₁ (helperT at) ≡ at
  helperFT (inj₁ x) = refl
  helperFT (inj₂ ())

-- weak distributive law

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , c ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ x , c ⟩ = inj₂ ⟨ x , c ⟩

-- a b + c d ≤ (a + c) (b + d) = ab + cd + ac + bd, true
⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩

{-
⊎×-implies-×⊎R : ∀ {A B C D : Set} → (A ⊎ C) × (B ⊎ D) → (A × B) ⊎ (C × D)
⊎×-implies-×⊎R ⟨ inj₁ a , inj₁ b ⟩ = inj₁ ⟨ a , b ⟩
⊎×-implies-×⊎R ⟨ inj₁ a , inj₂ d ⟩ = {!!}
⊎×-implies-×⊎R ⟨ inj₂ c , inj₁ b ⟩ = {!!}
⊎×-implies-×⊎R ⟨ inj₂ c , inj₂ d ⟩ = inj₂ ⟨ c , d ⟩
-- where should I place ⊥?
-}

-- import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
-- import Data.Unit using (⊤; tt)
-- import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
-- import Data.Empty using (⊥; ⊥-elim)
-- import Function.Equivalence using (_⇔_)


-- When you use func ≡, obviously need extensionality or η rules
-- a ≤ b
