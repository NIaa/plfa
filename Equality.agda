module plfa.Equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B} → u ≡ x → v ≡ y → f u v ≡ f x y
cong₂ f refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin_ refl = refl

  _≡⟨⟩_ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎ = refl

open ≡-Reasoning
{-
trans′ {A} {x} {y} {z} x≡y y≡z =
begin
x
≡⟨ x≡y ⟩
y
≡⟨ y≡z ⟩
z
∎
should be some refl
begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))
                               z≡z
                       y ≡ z | trans
             x ≡ z | trans
       nonsense
-}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎


data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ} → even n → odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm m n ev  rewrite +-comm n m = ev

even-comm′ : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm′ m n ev with   m + n  | +-comm m n
...                  | .(n + m) | refl       = ev
-- with can be replaced by local helper


-- data _≡_ {A : Set} (x : A) : A → Set where
--   refl : x ≡ x

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y -- Set → Set is Set₁
-- ≐ 有两个参数, x y, 生成一个Set1，  P (P x)

--  _≡_ : {A : Set} -> A -> A -> Set1
-- x ≡ y = (P : _ -> Set) -> P x -> P y


-- provide access to the implicit parameter, while infix form cannot
-- We cannot assign Set the type Set, since this would lead to contradictions such as Russell’s Paradox and Girard’s Paradox
-- Set : Set₁, Set₁ : Set₂


refl-≐ : ∀ {A : Set} {x : A} → x ≐ x
refl-≐ P = λ z → z
--refl-≐ P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
trans-≐ xy yz P Px = yz P (xy P Px)
--trans-≐ x≐y y≐z P Px  = y≐z P (x≐y P Px)
                               -- P y
                                   -- P z

sym-≐ : ∀ {A : Set} (x y : A) → x ≐ y → y ≐ x
sym-≐ x y x≐y P Py = (x≐y (λ z → P z → P x) λ z → z) Py
-- make Px, i.e. pick [P : ] [P x : ] for x ≐ y
--sym-≐ x y xy P py =  xy (\z -> P z -> P x) (λ z → z)  py
-- P is _ → P x
{-
sym-≐ {A} {x} {y} x≐y P = Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx
-}

≡-implies-≐ : ∀ {A : Set} {x y : A} → x ≡ y → x ≐ y
≡-implies-≐ x≡y P = subst P x≡y
-- subst P x≡y

≐-implies-≡ : ∀ {A : Set} {x y : A} → x ≐ y → x ≡ y
≐-implies-≡ {A} {x} {y} xy = xy (_≡_ x) refl
--                             (x ≡ _)    [Px : x ≡ x]   => P y : x ≡ y
{-
≐-implies-≡ {A} {x} {y} x≐y  =  Qy
  where
    Q : A → Set
    Q z = x ≡ z
    Qx : Q x
    Qx = refl
    Qy : Q y
    Qy = x≐y Q Qx
-}


open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x

_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y


-- Martin refl as default
-- Lebniz cong as default
-- just like +-identityˡ
{-


SUCC = λn.λf.λx.f(n f x)
PRED = λn.λf.λx.n(λg.λh.h(g f))(λu.x)(λu.u)

  Pred suc a
-}
