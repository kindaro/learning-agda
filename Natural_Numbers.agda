module Natural_Numbers where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

data ℕ : Set where
  zero : ℕ
  successor : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + x = x
successor y + x = successor (y + x)

_ : 2 + 3 ≡ 5
_ = refl

_×_ : ℕ → ℕ → ℕ
zero × x = zero
successor y × x = x + (y × x)

_ : 2 × 3 ≡ 6
_ = refl

_^_ : ℕ → ℕ → ℕ
x ^ zero = 1
x ^ successor y = x × (x ^ y)

_ : 2 ^ 10 ≡ 1024
_ = refl

data ℕ₂ : Set where
  ₂ : ℕ₂
  _I : ℕ₂ → ℕ₂
  _· : ℕ₂ → ℕ₂

x : ℕ₂
x = ₂ · · I

successor₂ : ℕ₂ → ℕ₂
successor₂ ₂ = ₂ I
successor₂ (x I) = successor₂ x ·
successor₂ (x ·) = x I

_ : successor₂ (₂ I I I) ≡ ₂ I · · ·
_ = refl

_ : successor₂ (₂ I · ·) ≡ ₂ I · I
_ = refl

ℕ→ℕ₂ : ℕ → ℕ₂
ℕ→ℕ₂ zero = ₂
ℕ→ℕ₂ (successor x) = successor₂ (ℕ→ℕ₂ x)

_ : ℕ→ℕ₂ 5 ≡ ₂ I · I
_ = refl

-- ℕ₂→ℕ : ℕ₂ → ℕ
-- ℕ₂→ℕ ₂ = zero
-- ℕ₂→ℕ (x ·) = (ℕ₂→ℕ x) × 2
-- ℕ₂→ℕ (x I) = successor (ℕ₂→ℕ (x ·))
-- Termination checker is not going to allow this… Maybe a little tweak could let it?

ℕ₂→ℕ : ℕ₂ → ℕ
ℕ₂→ℕ ₂ = zero
ℕ₂→ℕ (x ·) = (ℕ₂→ℕ x) × 2
ℕ₂→ℕ (x I) = successor ((ℕ₂→ℕ x) × 2)

_ : ℕ₂→ℕ (₂ I · I) ≡ 5
_ = refl

+associative : ∀ (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
+associative zero y z = refl
+associative (successor x) y z = begin (successor x + y) + z
  ≡⟨ cong successor (+associative x y z) ⟩ successor (x + (y + z)) ∎

+identity : ∀ (x : ℕ) → x + zero ≡ x
+identity zero = refl
+identity (successor x) = begin successor (x + zero)
  ≡⟨ cong successor (+identity x) ⟩ successor x ∎

+successor-move : ∀ (x y : ℕ) → x + successor y ≡ successor (x + y)
+successor-move zero y = refl
+successor-move (successor x) y = begin successor x + successor y
  ≡⟨ cong successor (+successor-move x y) ⟩ successor (successor x + y) ∎

+commutative : ∀ (x y : ℕ) → x + y ≡ y + x
+commutative x zero = begin x + zero ≡⟨ +identity x ⟩ zero + x ∎
+commutative x (successor y) = begin x + successor y
  ≡⟨ +successor-move x y ⟩ successor (x + y)
  ≡⟨ cong successor (+commutative x y) ⟩ successor (y + x) ∎

infixl 6 _+_
infixl 7 _×_

×+distributive : ∀ (x y z : ℕ) → x × (y + z) ≡ x × y + x × z
×+distributive zero y z = refl
×+distributive (successor x) y z = begin
  successor x × (y + z) ≡⟨⟩
  y + z + x × (y + z) ≡⟨ +associative y z (x × (y + z)) ⟩
  y + (z + (x × (y + z))) ≡⟨ cong (λ e → y + (z + e)) (×+distributive x y z) ⟩
  y + (z + (x × y + x × z)) ≡⟨ cong (λ e → y + e) (sym (+associative z (x × y) (x × z))) ⟩
  y + (z + x × y + x × z) ≡⟨ cong (λ e → y + (e + (x × z))) (+commutative z (x × y)) ⟩
  y + (x × y + z + x × z) ≡⟨ cong (λ e → y + e) (+associative (x × y) z (x × z)) ⟩
  y + (x × y + (z + x × z)) ≡⟨⟩
  y + (x × y + successor x × z) ≡⟨ sym (+associative y (x × y) (z + x × z)) ⟩
  y + x × y + successor x × z ≡⟨⟩
  successor x × y + successor x × z ∎
