module Accessible where

data Accessible {A : Set} (relation : A → A → Set) (a₀ : A) : Set where
  access : (∀ (a : A) → relation a a₀ → Accessible relation a) → Accessible relation a₀

well-founded : {A : Set} → (relation : A → A → Set) → Set
well-founded relation = ∀ a → Accessible relation a

well-founded-recursion
  : {A : Set} → {relation : A → A → Set} → {property : A → Set}
  → (∀ a₀ → (∀ a → relation a a₀ → property a) → property a₀) → (a₀ : A) → Accessible relation a₀
  → property a₀
well-founded-recursion algebra a₀ (access evidence)
  = algebra a₀ λ a related → well-founded-recursion algebra a (evidence a related)

module Total where

  recursion
    : ∀ {A : Set} {relation : A → A → Set} {property : A → Set} → well-founded relation
    → (∀ a₀ → (∀ a → relation a a₀ → property a) → property a₀) → (a₀ : A) → property a₀
  recursion evidence algebra a₀ = well-founded-recursion algebra a₀ (evidence a₀)

  fold
    : ∀ {A : Set} {relation : A → A → Set} {property : A → Set}
    → well-founded relation
    → (value-to-fold : A)
    → (∀ value-to-fold → (∀ folded-value → relation folded-value value-to-fold → property folded-value) → property value-to-fold)
    → property value-to-fold
  fold relation-is-well-founded value-to-fold algebra
    = well-founded-recursion algebra value-to-fold (relation-is-well-founded value-to-fold)
