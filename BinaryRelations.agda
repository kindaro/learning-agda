open import Prelude

are-path-connected : {A B C : Set} {ℓ₁ ℓ₂ : Level} → A — B [ ℓ₁ ] → B — C [ ℓ₂ ] → A — C [ ℓ₁ ⊔ ℓ₂ ]
are-path-connected R₁ R₂ = λ a c → ∃ λ b → R₁ a b × R₂ b c

_—_ : {A B C : Set} {ℓ₁ ℓ₂ : Level} → B — C [ ℓ₂ ] → A — B [ ℓ₁ ] → A — C [ ℓ₁ ⊔ ℓ₂ ]
R₂ — R₁ = are-path-connected R₁ R₂
infixl 9 _—_

_† : ∀ {A B : Set} {ℓ : Level} → A — B [ ℓ ] → B — A [ ℓ ]
R † = λ b a → R a b
infix 30 _†

transpose-is-involution : ∀ {A B : Set} {ℓ : Level} → ∀ (R : A — B [ ℓ ]) → (R †) † ≡ R
transpose-is-involution R = reflexivity

equality-of-relations : ∀ {A B : Set} {ℓ : Level} → A — B [ ℓ ] → A — B [ ℓ ] → Set _
equality-of-relations {A} {B} R₁ R₂ = ∀ (a : A) (b : B) → R₁ a b ↔ R₂ a b

_≋_ = equality-of-relations
infix 5 _≋_

composition-before-transpose-is-idempotent : ∀ {A B : Set} {ℓ : Level} → ∀ (R : A — B [ ℓ ]) → R † — R ≋ R † — R — R † — R
composition-before-transpose-is-idempotent R = λ a b → {!!}
