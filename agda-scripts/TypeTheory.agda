-- workbook for TypeTheory course (Maietti, Sambin)
module TypeTheory where

open import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (¬?)
open import Data.List using (List; _∷_; [])
open import Function using (_∘_)
open import Data.AVL.Sets using (empty; singleton)

-- Martin Lof propositional equality
data Id_,_ {A : Set} : A → A → Set where -- the sign is the formation rules
  id : (x : A) → Id x , x -- the constructors are the introduction elements of a type

-- elimination and conversion rule for ML equality
El-Id : ∀ -- the type specify the elimination rule
  {A : Set}
  {C : (x : A) → (y : A) → (z : Id x , y)  → Set}
  {a b : A}
  → (p : Id a , b)
  → ((x : A) → C x x (id x))
  → C a b p
El-Id (id a) c = c a -- the body specify the elersion rule

-- elimination and conversion rule for ℕ induction
El-ℕ : ∀ {D : ℕ → Set} → (m : ℕ) → (d : D 0) → (e : (x : ℕ) → D x → D (suc x)) → D m
El-ℕ zero d e = d
El-ℕ (suc m) d e = e m (El-ℕ m d e)

-- equality preservation among programs
eq-pres : ∀ {A B : Set} {a b : A} → (f : (x : A) → B) → Id a , b → Id (f a) , (f b)
eq-pres f w = El-Id w (id ∘ f)

-- symmetricmetric
symmetric : ∀ {A : Set} {x y : A}
  → Id x , y → Id y , x
symmetric w = El-Id w id

-- transitivity
transitivity : ∀ {A : Set} {a b c : A}
  → Id a , b → Id b , c → Id a , c  
transitivity w₁ w₂ =
  El-Id
    -- {A} -- type of Identity
    {C = λ x → λ y → λ _ → (Id _ , x → Id _ , y)} -- type of C, has to be explicit
    -- {b} -- a
    -- {c} -- b
    w₂ -- "base proof" p
    (λ _ → λ w → w) -- proof c, where the first x ∈ A is avoided
  w₁ -- El-Id applied to w₁

-- propositional equality among sum operator
_+_ : ℕ → ℕ → ℕ
x + y = El-ℕ x y (λ _ z → suc z) 

-- lemma₁, x + 0 equal x
lemma₁ : (x : ℕ) → Id x , (x + 0) 
lemma₁ x′ = El-ℕ x′ (id 0) k
  where
    k : (x : ℕ) → Id x , (x + 0) → Id (suc x) , ((suc x) + 0)
    k x z = El-Id {C = λ x → λ y → λ _ → Id (suc x) , (suc y)} z (id ∘ suc)

lemma₂ : (x y : ℕ) → Id (x + (suc y)) , (suc (x + y))
lemma₂ x′ y′ = El-ℕ {D = λ x → Id (x + (suc y′)) , (suc (x + y′))}
  x′
  (id (suc y′))
  λ _ → eq-pres suc -- note that z implict param 

-- note that
-- El-ℕ x y λ x₂ → suc x₂ ≡ x + y, this holds for definition
-- El-ℕ y x λ x₂ → suc x₂ ≡ y + x, this holds for definition
-- then to proof x +₁ y ≡ x +₂ y you can proof x + y ≡ y + x (eg commutative)
eq-sum : (x y : ℕ) → Id (x + y) , (y + x)
eq-sum x′ y′ = El-ℕ {D = λ y → Id (x′ + y) , (y + x′)}
  y′
  (symmetric (lemma₁ x′))
  λ y z → transitivity {b = suc (x′ + y)} (lemma₂ x′ y) (eq-pres suc z)

-- 0 ≠ 1
data N₀ : Set where

data N₁ : Set where
  ⋆ : N₁

El-N₁ : ∀ {M : N₁ → Set} → (t : N₁) → M ⋆ → M t  
El-N₁ ⋆ c = c

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B


El-× : ∀ {A B : Set} {M : A × B → Set} → (d : A × B) → ((x : A) → (y : B) → M ⟨ x , y ⟩) → M d
El-× ⟨ x , y ⟩ m = m x y

π₁ : ∀ {A B : Set} → A × B → A
π₁ x = El-× x λ x _ → x

π₂ : ∀ {A B : Set} → A × B → B
π₂ x = El-× x λ _ y → y

_⇔_ : (A B : Set) → Set
A ⇔ B = (A → B) × (B → A)

data U₀ : Set where
  N₀̂ : U₀ -- empty
  N₁̂ : U₀ -- singleton

T : U₀ → Set
T N₀̂ = N₀
T N₁̂ = N₁ 

-- conversion ℕ → Universe
f : ℕ → U₀
f m = El-ℕ m N₁̂ λ _ _ → N₀̂ -- no recursion

k : (x y : U₀) → Id x , y → (T x ⇔ T y)
k x y w = El-Id {C = λ x y _ → (T x ⇔ T y) }
  w
  λ _ → ⟨ (λ y → y) , (λ y → y) ⟩

-- main point 
neq : Id 0 , 1 → N₀
neq w = (π₁ (k N₁̂ N₀̂ (eq-pres f w))) ⋆

-- ac
-- definition of Product Type dependant
data Σ {A : Set} (B : A → Set) : Set where
  ⟪_,_⟫ : (x : A) → B x → Σ λ(x' : A) → B x'

-- the function type is already defined but we can define the Π to obtain a notation
-- closer to ML
-- definition of Function type(Abstraction)
Π : {X : Set} → (Y : X → Set) → Set
Π {X} Y = (x : X) → Y x

-- left projection
proj₁ : {A : Set} {B : A → Set} → (Σ λ(x : A) → B x) → A
proj₁ ⟪ a , b ⟫ = a

-- right proj₁rojection
proj₂ : {A : Set} {B : A → Set} → (c : Σ λ(x : A) → B x) → B (proj₁ c)
proj₂ ⟪ a , b ⟫ = b

axiom-of-choice : {A : Set} {B : A → Set} {C : (x : A) → B x → Set}
  → Π λ(z : Π λ(x : A) → (Σ λ(y : B x) → C x y))
  → Σ λ(f : Π λ(x : A) → B x) → Π λ(x : A) → C x (f x)
axiom-of-choice = λ z → ⟪ (λ x → proj₁ (z x)) , (λ x → proj₂ (z x)) ⟫

-- η-conversion
η-conv : ∀ {A B : Set } → (z : A × B) → Id ⟨ π₁ z , π₂ z ⟩ , z
η-conv z = El-× {M = λ z → Id ⟨ π₁ z , π₂ z ⟩ , z}
  z
  λ x y →  El-Id {C = λ a b _ → Id ⟨ a , π₂ ⟨ b , y ⟩ ⟩ , ⟨ b , y ⟩ } 
    (id x)
    λ a → El-Id {C = λ a′ b′ _  → Id ⟨ a , a′ ⟩ , ⟨ a , b′ ⟩} 
      (id y)
      λ b → id ⟨ a , b ⟩

-- peano axioms
-- _*_ : ∀ (x y : ℕ) → ℕ
-- x * y = El-ℕ x 0 λ x z → (y + z)

-- infixl 6 _+_
-- infixl 7 _*_ 

pre : ℕ → ℕ -- used in ax₂
pre x = El-ℕ x zero λ x _ → x

-- ax1
ax₁ : ∀ {x : ℕ} → Id (suc x) , 0 → N₀
ax₁ {x} w = (π₁ (k N₁̂ N₀̂ (eq-pres f (symmetric w)))) ⋆

--ax2
ax₂ : ∀ {x y : ℕ} → Id (suc x) , (suc y) → Id x , y
ax₂ {x} {y} = eq-pres pre


--ax3
ax₃ : ∀ {x : ℕ} → Id (x + 0) , x
ax₃ {x} = symmetric (lemma₁ x )

--ax4
ax₄ : ∀ {x y : ℕ} → Id (x + suc y) , (suc (x + y))
ax₄ {x} {y} = lemma₂ x y

--ax5 and ax6 are almost the same as ax3 and ax4, the formers use * op while the latters use + instead
-- ax₅ : ∀ {x : ℕ} → Id (x * 0) , 0
-- ax₆ : ∀ {x y : ℕ} → Id (x * suc y) , (x * y + x)

--ax7                      x     x₁                             x₂
ax₇ : ∀ {A : ℕ → Set} → A 0 → ((x : ℕ) → A x → A (suc x)) → ((x : ℕ) → A x)
ax₇ {A} = λ x x₁ x₂ → El-ℕ x₂ x x₁
