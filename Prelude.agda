module Prelude where

open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Core
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Equality using (_≡_) public
open ≡-Reasoning public

symmetry : {A : Set} → Symmetric {A = A} _≡_
symmetry = sym

congruence : {A B : Set} → ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
congruence = cong

reflexivity : {A : Set} → {x : A} → x ≡ x
reflexivity = refl
