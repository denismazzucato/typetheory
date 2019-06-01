-- definition of Product Type
data Σ {A : Set} (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ \(x' : A) → B x'

-- left projection
π₁ : {A : Set} {B : A → Set} → (Σ \(x : A) → B x) → A
π₁ ⟨ a , b ⟩ = a

-- right π₁rojection
π₂ : {A : Set} {B : A → Set} → (c : Σ \(x : A) → B x) → B (π₁ c)
π₂ ⟨ a , b ⟩ = b

-- the function type is already defined but we can define the Π to obtain a notation
-- closer to ML
-- definition of Function type(Abstraction)
Π : {X : Set} → (Y : X → Set) → Set
Π {X} Y = (x : X) → Y x

axiom-of-choice : {A : Set } {B : A → Set} {C : (x : A) → B x → Set}
  → Π \(z : Π \(x : A) → (Σ \(y : B x) → C x y))
  → Σ \(f : Π \(x : A) → B x) → Π \(x : A) → C x (f x)
axiom-of-choice = λ z → ⟨ (λ x → π₁ (z x)), (λ x → π₂ (z x)) ⟩
