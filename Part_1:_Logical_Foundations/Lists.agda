module plfa.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribˡ-+; *-comm; *-distribʳ-+; +-comm;  *-distrib-∸;*-identity;+-∸-assoc;+-∸-comm;n∸n≡0;m≤m+n)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Data.Empty using (⊥-elim)
open import Level using (Level)
open import plfa.Isomorphism using (_≃_; _⇔_; extensionality)
open import Data.Product using (_×_; ∃; ∃-syntax;proj₁;proj₂) renaming (_,_ to ⟨_,_⟩)


data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

{-# BUILTIN LIST List #-}

--  pattern declarations
pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) = cong (_∷_ x) (++-identityʳ xs)

length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = (reverse xs) ++ [ x ]

shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A) → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse {A} [] ys = refl
shunt-reverse {A} (x ∷ xs) ys rewrite ++-assoc (reverse xs) [ x ] ys | shunt-reverse xs (x ∷ ys) = refl
--  shunt-reverse xs (x ∷ ys)
--  sym (++-assoc (reverse xs) [ x ] ys)

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

-- like fold, parameterized iteration in FP

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ acc [] = acc
foldr _⊗_ acc (x ∷ xs) = x ⊗ foldr _⊗_ acc xs

sum : List ℕ → ℕ
sum = foldr _+_ 0

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid = record
  { assoc = +-assoc
  ; identityˡ = +-identityˡ
  ; identityʳ = +-identityʳ }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =  sym (identityˡ ⊗-monoid y)
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y rewrite foldr-monoid _⊗_ e ⊗-monoid xs y | assoc ⊗-monoid x (foldr _⊗_ e xs) y  = refl

{-
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y = begin
                                           (x ⊗ foldr _⊗_ y xs) ≡⟨ cong (_⊗_ x)
                                           (foldr-monoid _⊗_ e
                                            (record
                                             { assoc = assoc ⊗-monoid
                                             ; identityˡ = identityˡ ⊗-monoid
                                             ; identityʳ = identityʳ ⊗-monoid
                                             })
                                            xs y)
                                           ⟩
                                           (x ⊗ (foldr _⊗_ e xs ⊗ y)) ≡⟨
                                           sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
                                           ((x ⊗ foldr _⊗_ e xs) ⊗ y) ∎
-- C-c C-a ↑
-}

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (here ())
not-in (there (here ()))
not-in (there (there (here ())))
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))

not-in2 : 3 ∉ []
not-in2 ()

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ {A} {P} xs ys = record { to = helper-to xs ys ; from = helper-from xs ys } where
  helper-to : (xs ys : List A) → All P (xs ++ ys) → (All P xs × All P ys) -- Notice helper's scope
  helper-to [] ys AP++ = ⟨ [] ,  AP++ ⟩
  helper-to (x ∷ xs) ys (Px ∷ APxs) with helper-to xs ys APxs
  ... | ⟨ al , ar ⟩ = ⟨ Px ∷ al , ar ⟩
  helper-from : (xs ys : List A) → (All P xs  × All P ys) → All P (xs ++ ys)
  helper-from .[] ys ⟨ [] , ar ⟩ = ar
  helper-from (x ∷ xs) ys ⟨ Px ∷ al , ar ⟩ = Px ∷ helper-from xs ys ⟨ al , ar ⟩

all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p  =  foldr _∧_ true ∘ map p

Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)

All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? []                                 =  yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes Pxs     =  yes (Px ∷ Pxs)
...                 | no ¬Px | _           =  no λ{ (Px ∷ Pxs) → ¬Px Px   }
...                 | _      | no ¬Pxs     =  no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }
-------------------------------------------------------
-- Exercise
-- ++ is infixr
-- rewrite from rhs, like ≡ reasoning
reverse-++-commute : ∀ {A : Set} {xs ys : List A} → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-commute {A} {[]} {ys} = sym (++-identityʳ (reverse ys))
reverse-++-commute {A} {x ∷ xs} {ys} rewrite sym (++-assoc (reverse ys) (reverse xs) [ x ]) | reverse-++-commute {A} {xs} {ys} = refl
-- Goal: reverse (xs ++ ys) ++ [ x ] ≡ reverse ys ++ reverse xs ++ [ x ]
-- ->   sym ++-assoc                       (                       )


-- 方程作用于任意值相等
map-compose' : ∀ {A B C} (f : B → C)(g : A → B)(xs : List A) →
  map (f ∘ g) xs ≡ (map f ∘ map g) xs
map-compose' f g []       = refl
map-compose' f g (x ∷ xs) rewrite map-compose' f g xs = refl

map-compose : ∀ {A B C : Set} {f : A → B} {g : B → C} → map (g ∘ f) ≡ map g ∘ map f
map-compose {A} {B} {C} {f} {g} = extensionality λ xs → (map-compose' g f xs)
--{ [] → refl ; (a ∷ as) → {!!}} -- how to prop of as?
-- Goal: ((λ {.x} → g) ∘ f) x ∷ map ((λ {.x} → g) ∘ f) as ≡ ((λ {.x} → map g) ∘ map f) (x ∷ as)
-- have                  map (g . f) xs ≡ map g . map f xs

-- extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g
-- 搞清楚这是怎么回事
-- 对比STL 的cong形式

map-++-commute : ∀ {A B : Set} {f : A → B} {xs ys : List A}
  →  map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute {A} {B} {f} {[]} {ys} = refl
map-++-commute {A} {B} {f} {x ∷ xs} {ys} = cong (_∷_ (f x)) (map-++-commute {A} {B} {f} {xs} {ys})

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B


map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node t x t₁) = node (map-Tree f g t) (g x) (map-Tree f g t₁)


product : (xs : List ℕ) → ℕ
product = foldr _*_ (suc zero)

--product
product_test : product [ 1 , 2 , 3 , 4 ] ≡ 24
product_test = refl


foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
  foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ ⊗ e [] ys = refl
foldr-++ ⊗ e (x ∷ xs) ys = cong (⊗ x) (foldr-++ ⊗ e xs ys)


map-is-foldr' : ∀ {A B : Set} {f : A → B} → (xs : List A) →
  map f xs ≡ (foldr (λ x xs → f x ∷ xs) []) xs
map-is-foldr' {A} {B} {f} [] = refl
map-is-foldr' {A} {B} {f} (x ∷ xs) = cong (_∷_ (f x)) (map-is-foldr' xs)

map-is-foldr : ∀ {A B : Set} {f : A → B} →
  map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr {A} {B} {f} = extensionality λ xs → map-is-foldr' xs

fold-Tree : ∀ {A B C : Set}  → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree fleaf gnode (leaf x) = fleaf x
fold-Tree fleaf gnode (node t x t₁) = gnode (fold-Tree fleaf gnode t) x (fold-Tree fleaf gnode t₁)

map-is-fold-Tree' : ∀ {A B C D : Set} → {ac : A → C} → {bd : B → D}
   → (t : Tree A B) → map-Tree ac bd t ≡ (fold-Tree (leaf ∘ ac) (λ l b r → node l (bd b) r) t)
map-is-fold-Tree' (leaf x) = refl
map-is-fold-Tree' {A} {B} {C} {D} {ac} {bd} (node l b r) = map-Tree ac bd (node l b r)
  ≡⟨ refl ⟩ node (map-Tree ac bd l) (bd b) (map-Tree ac bd r)
  ≡⟨ cong (λ x → node (map-Tree ac bd l) (bd b) x) (map-is-fold-Tree' {A} {B} {C} {D} {ac} {bd} r) ⟩
    node (map-Tree ac bd l) (bd b) (fold-Tree (λ z → leaf (ac z)) (λ z z₁ → node z (bd z₁)) r)
  ≡⟨ cong (λ x → node x (bd b) (fold-Tree (λ z → leaf (ac z)) (λ z z₁ → node z (bd z₁)) r)) (map-is-fold-Tree' {A} {B} {C} {D} {ac} {bd} l) ⟩
    node (fold-Tree (λ z → leaf (ac z)) (λ z z₁ → node z (bd z₁)) l) (bd b) (fold-Tree (λ z → leaf (ac z)) (λ z z₁ → node z (bd z₁)) r)
  ∎

map-is-fold-Tree : ∀ {A B C D : Set} → {ac : A → C} → {bd : B → D}
  →  map-Tree ac bd  ≡ fold-Tree (leaf ∘ ac) (λ l b r → node l (bd b) r)
map-is-fold-Tree = extensionality map-is-fold-Tree'

-- sum-downFrom
downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n

open import Data.Nat.Properties using (*-distrib-∸;*-identity;+-∸-assoc;+-∸-comm;n∸n≡0;m≤m+n)



sum-downFrom : ∀ (n : ℕ)
  → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc zero) = refl
sum-downFrom (suc (suc n)) with sum-downFrom n
... | e = ((suc n) + foldr _+_ 0 (downFrom (suc n))) * 2
      ≡⟨ *-distribʳ-+ 2 (suc n) (foldr (_+_) 0 (downFrom (suc n)))  ⟩
        suc (suc (n * 2 + (n + foldr _+_ zero (downFrom n)) * 2))
--        n * 2 + foldr _+_ zero (downFrom n) * 2
      ≡⟨ cong (λ x → suc (suc (n * 2) + x)) (sum-downFrom (suc n)) ⟩
        suc (suc (n * 2 + (n + n * n)))
      ≡⟨ cong (λ x → suc (suc (n * 2 + x))) (*-comm (suc n) n) ⟩ suc (suc (n * 2 + n * suc n))
--      ≡⟨ cong (λ x → suc (suc x)) (sym (*-distribˡ-+ n 2 (suc n))) ⟩ suc (suc (n * suc (suc (suc n))))
      ≡⟨ cong (λ x  → suc (suc (x + n * (suc n)))) (*-comm n 2)⟩ suc (suc (n + (n + zero) + n * suc n))
      ≡⟨ cong (λ x → suc (suc (n + x + n * (suc n)))) (+-identityʳ n)⟩ suc (suc (n + n + n * suc n))
      ≡⟨⟩ suc (suc n + n + n * suc n)
      ≡⟨ cong (λ x → suc (x + n * (suc n))) (+-comm (suc n) n) ⟩ suc (n + suc n + n * suc n)
      ≡⟨ cong suc (+-assoc n (suc n) (n * (suc n))) ⟩ suc (n + suc (n + n * suc n))
      ≡⟨⟩ suc (n + suc (n + n * suc n))
      ∎

{-
foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
-}

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e [] = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldl _⊗_ y xs ≡ y ⊗ foldl _⊗_ e xs
foldl-monoid _⊗_ e ⊗-monoid [] y = sym (identityʳ ⊗-monoid y)
foldl-monoid _⊗_ e ⊗-monoid (x ∷ xs) y
  rewrite foldl-monoid _⊗_ e ⊗-monoid xs (y ⊗ x) | assoc ⊗-monoid y x (foldl _⊗_ e xs)
        | foldl-monoid _⊗_ e ⊗-monoid xs x | identityˡ ⊗-monoid x | foldl-monoid _⊗_  e ⊗-monoid xs x = refl


-- Show that if _⊗_ and e form a monoid, then foldr _⊗_ e and foldl _⊗_ e always compute the same result.
foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
foldr-monoid-foldl _⊗_ e  ⊗-monoid [] = refl
foldr-monoid-foldl _⊗_ e ⊗-monoid (x ∷ xs) rewrite identityˡ ⊗-monoid x | foldr-monoid-foldl _⊗_ e  ⊗-monoid xs | foldl-monoid _⊗_ e ⊗-monoid xs x = refl

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ {A} {P} xs ys = record { to = helper-to xs ys ; from = from xs ys } where
  helper-to : (xs ys : List A) → Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
  helper-to [] ys Pxs++ys = inj₂ Pxs++ys
  helper-to (x ∷ xs) ys (here Px) = inj₁ (here Px)
  helper-to (x ∷ xs) ys (there Pxs++ys) with helper-to xs ys Pxs++ys
  ... | inj₁ ax = inj₁ (there ax)
  ... | inj₂ ay = inj₂ ay
  from : (xs ys : List A) → (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
  from [] ys (inj₁ ())
  from [] ys (inj₂ Py) = Py
  from (x ∷ xs) ys (inj₁ (here Px)) = here Px
  from (x ∷ xs) ys (inj₁ (there Pxs)) = there (from xs ys (inj₁ Pxs))
  from (x ∷ xs) ys (inj₂ Py) = there (from xs ys (inj₂ Py))
--  helper-from :

All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ {A} {P} xs ys = record
  { to = to xs ys
  ; from = from xs ys
  ; from∘to = λ Pxs++ys → from∘to xs ys Pxs++ys
  ; to∘from = λ { ⟨ Pxs , Pys ⟩ → to∘from xs ys ⟨ Pxs , Pys ⟩ }
  }  where
    to : (xs ys : List A) → All P (xs ++ ys) → All P xs × All P ys
    to [] ys Pxs++ys = ⟨ [] , Pxs++ys ⟩
    to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
    ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩
    from : (xs ys : List A) → All P xs × All P ys → All P (xs ++ ys)
    from [] ys ⟨ Pxs , Pys ⟩ = Pys
    from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ = Px ∷ from xs ys ⟨ Pxs , Pys ⟩
    from∘to : (xs ys : List A) (Pxs++ys : All P (xs ++ ys)) → from xs ys (to xs ys Pxs++ys) ≡ Pxs++ys
    from∘to [] ys Pxs++ys = refl
    from∘to (x ∷ xs) ys (Px ∷ xs++ys) with from∘to xs ys xs++ys
    ... | eql rewrite eql = refl
    to∘from : (xs ys : List A) ( Pxs×Pys : All P xs × All P ys) → to xs ys (from xs ys Pxs×Pys) ≡ Pxs×Pys
    to∘from [] ys ⟨ [] , Pys ⟩ = refl
    to∘from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ rewrite to∘from xs ys ⟨ Pxs , Pys ⟩ = refl

--¬Any≃All¬
_∘′_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘′ f) x  =  g (f x)


¬Any≃All¬ : ∀ {A : Set} (P : A → Set) (xs : List A)
  → (¬_ ∘′ Any P) xs ≃ All (¬_ ∘′ P) xs
¬Any≃All¬ {A} P xs = record { to = to xs ; from = from xs ; from∘to = from∘to xs ; to∘from = to∘from xs }
  where
  to : (xs : List A) → (¬_ ∘′ Any P) xs → All (¬_ ∘′ P) xs
  to [] lhs = []
  to (x ∷ xs) lhs = (λ Px → lhs (here Px)) ∷ to xs λ Pxs → lhs (there Pxs)
  from : (xs : List A) → All (¬_ ∘′ P) xs  → (¬_ ∘′ Any P) xs
  from [] lhs = λ ()
  from (x ∷ _)  (¬Px ∷ _)    (here Px) = ¬Px Px
  from (x ∷ xs) (¬Px ∷ ¬Pxs) (there AnyPxs) = from xs ¬Pxs AnyPxs
  from∘to : (xs : List A) → (¬AnyPxs : (¬_ ∘′ Any P) xs) → from xs (to xs ¬AnyPxs) ≡ ¬AnyPxs
  from∘to [] ¬AnyPxs = extensionality λ ()
  from∘to (x ∷ xs) ¬AnyPxs = extensionality λ { (here Px) → refl; (there AnyPxs) → ⊥-elim (¬AnyPxs (there AnyPxs))}
  to∘from : (xs : List A) → (All¬Pxs : (All (¬_ ∘′ P) xs)) → to xs (from xs All¬Pxs) ≡ All¬Pxs
  to∘from [] [] = refl
  to∘from (x ∷ xs) (¬Px ∷ All¬Pxs) rewrite to∘from xs All¬Pxs = refl

¬All≃Any¬ : ∀ {A : Set} (P : A → Set) (xs : List A)
  → (¬_ ∘′ All P) xs ≃ Any (¬_ ∘′ P) xs
¬All≃Any¬ {A} P xs = record { to = {!!} ; from = {!!} ; from∘to = {!!} ; to∘from = {!!} } where
  to : (xs : List A) → (¬_ ∘′ All P) xs → Any (¬_ ∘′ P) xs
  to [] ¬AllPxs = ⊥-elim (¬AllPxs [])
  to (x ∷ xs) ¬AllPx∷xs = {!!}
  from : (xs : List A) →  Any (¬_ ∘′ P) xs → (¬_ ∘′ All P) xs
  from [] () AllPxs
  from (x ∷ xs) (here ¬Px) (Px ∷ AllPxs) = ¬Px Px
  from (x ∷ xs) (there Any¬Pxs) (Px ∷ AllPxs) = from xs Any¬Pxs AllPxs
--  from∘to :
--  to∘from :
-- ???  HOW TO PATTERN MATCH ¬AllPx∷xs


--Exercise any? (stretch)
-- all : ∀ {A : Set} → (A → Bool) → List A → Bool
-- All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
any : ∀ {A : Set} → (A → Bool) → List A → Bool
any p = foldr _∨_ false ∘ map p

Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
Any? P? [] = no (λ ())
Any? P? (x ∷ xs) with P? x | Any? P? xs
...    | yes p | yes ps = yes (here p)
...    | yes p | no ¬ps = yes (here p)
...    | no ¬p | yes ps = yes (there ps)
...    | no ¬p | no ¬ps = no λ{ (here px) → ¬p px; (there pxs) → ¬ps pxs}

filter? : ∀ {A : Set} {P : A → Set}
  → (P? : Decidable P) → List A → ∃[ ys ]( All P ys )
filter? P? [] = ⟨ [] , [] ⟩
filter? P? (x ∷ xs) with P? x | filter? P? xs
...                   | yes p | ⟨ ys , AllPys ⟩ = ⟨ x ∷ ys , p ∷ AllPys ⟩
...                   | no ¬p | ⟨ ys , AllPys ⟩ = ⟨ ys , AllPys ⟩
