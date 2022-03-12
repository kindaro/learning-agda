module Prelude where

open import Agda.Primitive using (Level)
open import Relation.Nullary using (¬_) public
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Core using (_≢_) public
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Equality using (_≡_) public
open import Function.Base using (_∘_) public
open import Agda.Builtin.Nat using (Nat; zero; suc) public
open ≡-Reasoning public
open import Agda.Primitive as Prim public
  using    (Level; _⊔_; Setω)
  renaming (lzero to ℓ₀; lsuc to next-level)

symmetry : {A : Set} → Symmetric {A = A} _≡_
symmetry = sym

congruence : {A B : Set} → ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
congruence = cong

pattern reflexivity = refl

ℕ : Set
ℕ = Nat

pattern successor x = suc x

substitute : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
substitute property refl evidence = evidence
