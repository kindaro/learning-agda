module Prelude where

open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Core
open import Agda.Builtin.Equality public
open ≡-Reasoning public

symmetry : {A : Set} → Symmetric {A = A} _≡_
symmetry = sym

congruence : {A B : Set} → ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
congruence = cong
