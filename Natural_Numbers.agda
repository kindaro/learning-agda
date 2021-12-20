module Natural_Numbers where

open import Prelude

data ℕ : Set where
  zero : ℕ
  successor : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + x = x
successor y + x = successor (y + x)

_ : 2 + 3 ≡ 5
_ = reflexivity

_∸_ : ℕ → ℕ → ℕ
x ∸ zero = x
zero ∸ successor y = zero
successor x ∸ successor y = x ∸ y

_×_ : ℕ → ℕ → ℕ
zero × x = zero
successor y × x = x + (y × x)

_ : 2 × 3 ≡ 6
_ = reflexivity

_^_ : ℕ → ℕ → ℕ
x ^ zero = 1
x ^ successor y = x × (x ^ y)

_ : 2 ^ 10 ≡ 1024
_ = reflexivity

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
_ = reflexivity

_ : successor₂ (₂ I · ·) ≡ ₂ I · I
_ = reflexivity

ℕ→ℕ₂ : ℕ → ℕ₂
ℕ→ℕ₂ zero = ₂
ℕ→ℕ₂ (successor x) = successor₂ (ℕ→ℕ₂ x)

_ : ℕ→ℕ₂ 5 ≡ ₂ I · I
_ = reflexivity

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
_ = reflexivity

+associative : ∀ (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
+associative zero y z = reflexivity
+associative (successor x) y z = begin (successor x + y) + z
  ≡⟨ congruence successor (+associative x y z) ⟩ successor (x + (y + z)) ∎

+identity : ∀ (x : ℕ) → x + zero ≡ x
+identity zero = reflexivity
+identity (successor x) = begin successor (x + zero)
  ≡⟨ congruence successor (+identity x) ⟩ successor x ∎

+successor-move : ∀ (x y : ℕ) → x + successor y ≡ successor (x + y)
+successor-move zero y = reflexivity
+successor-move (successor x) y = begin successor x + successor y
  ≡⟨ congruence successor (+successor-move x y) ⟩ successor (successor x + y) ∎

+commutative : ∀ (x y : ℕ) → x + y ≡ y + x
+commutative x zero = begin x + zero ≡⟨ +identity x ⟩ zero + x ∎
+commutative x (successor y) = begin x + successor y
  ≡⟨ +successor-move x y ⟩ successor (x + y)
  ≡⟨ congruence successor (+commutative x y) ⟩ successor (y + x) ∎

infixl 6 _∸_
infixl 6 _+_
infixl 7 _×_

+-swap : ∀ (x y z : ℕ) → x + (y + z) ≡ y + (x + z)
+-swap x y z rewrite symmetry (+associative x y z)
  | +commutative x y
  | +associative y x z
  = reflexivity

×-distributes-over-+-on-the-left : ∀ (x y z : ℕ) → x × (y + z) ≡ x × y + x × z
×-distributes-over-+-on-the-left zero y z = reflexivity
×-distributes-over-+-on-the-left (successor x) y z = begin
  successor x × (y + z) ≡⟨⟩
  y + z + x × (y + z) ≡⟨ +associative y z (x × (y + z)) ⟩
  y + (z + (x × (y + z))) ≡⟨ congruence (λ e → y + (z + e)) (×-distributes-over-+-on-the-left x y z) ⟩
  y + (z + (x × y + x × z)) ≡⟨ congruence (λ e → y + e) (symmetry (+associative z (x × y) (x × z))) ⟩
  y + (z + x × y + x × z) ≡⟨ congruence (λ e → y + (e + (x × z))) (+commutative z (x × y)) ⟩
  y + (x × y + z + x × z) ≡⟨ congruence (λ e → y + e) (+associative (x × y) z (x × z)) ⟩
  y + (x × y + (z + x × z)) ≡⟨⟩
  y + (x × y + successor x × z) ≡⟨ symmetry (+associative y (x × y) (z + x × z)) ⟩
  y + x × y + successor x × z ≡⟨⟩
  successor x × y + successor x × z ∎

×-distributes-over-+-on-the-right : ∀ (x y z : ℕ) → (x + y) × z ≡ x × z + y × z
×-distributes-over-+-on-the-right zero y z = reflexivity
×-distributes-over-+-on-the-right (successor x) y z = begin
  (successor x + y) × z ≡⟨⟩
  z + (x + y) × z ≡⟨ congruence (λ e → z + e) (×-distributes-over-+-on-the-right x y z) ⟩
  z + (x × z + y × z) ≡⟨ symmetry (+associative z (x × z) (y × z)) ⟩
  z + x × z + y × z ≡⟨⟩
  successor x × z + y × z ∎

×-is-associative : ∀ (x y z : ℕ) → x × (y × z) ≡ (x × y) × z
×-is-associative zero y z = reflexivity
×-is-associative (successor x) y z = begin
  successor x × (y × z) ≡⟨⟩
  y × z + x × (y × z) ≡⟨ congruence (λ e → ((y × z) + e)) (×-is-associative x y z) ⟩
  y × z + x × y × z ≡⟨ symmetry (×-distributes-over-+-on-the-right y (x × y) z) ⟩
  (y + x × y) × z ≡⟨⟩
  successor x × y × z ∎

left-identity-of-× : ∀ (x : ℕ) → 1 × x ≡ x
left-identity-of-× x = begin
  1 × x ≡⟨⟩
  x + zero ≡⟨ +identity (x) ⟩
  x ∎

right-identity-of-× : ∀ (x : ℕ) → x × 1 ≡ x
right-identity-of-× zero = reflexivity
right-identity-of-× (successor x) = begin
  successor x × 1 ≡⟨⟩
  1 + (x × 1) ≡⟨ congruence (λ e → 1 + e) (right-identity-of-× x) ⟩
  successor x ∎

right-absorption-of-× : ∀ (x : ℕ) → x × zero ≡ zero
right-absorption-of-× zero = reflexivity
right-absorption-of-× (successor x) = begin
  successor x × zero ≡⟨⟩
  x × zero ≡⟨ right-absorption-of-× x ⟩
  zero ∎

×-move : ∀ (x y : ℕ) → x × successor y ≡ x + x × y
×-move x y = begin
  x × (1 + y) ≡⟨ ×-distributes-over-+-on-the-left x 1 y ⟩
  x × 1 + x × y ≡⟨ congruence (λ e → e + x × y) (right-identity-of-× x) ⟩
  x + x × y ∎

×-is-commutative : ∀ (x y : ℕ) → x × y ≡ y × x
×-is-commutative x zero = begin
  x × zero ≡⟨ right-absorption-of-× x ⟩
  zero ≡⟨⟩
  zero × x ∎
×-is-commutative x (successor y) = begin
  x × successor y ≡⟨ ×-move x y ⟩
  x + x × y ≡⟨ congruence (λ e → x + e) (×-is-commutative x y) ⟩
  x + y × x ≡⟨⟩
  successor y × x ∎

∸-of-zero : ∀ (x : ℕ) → zero ∸ x ≡ zero
∸-of-zero zero = reflexivity
∸-of-zero (successor _) = reflexivity

∸-+-associative : ∀ (x y z : ℕ) → x ∸ y ∸ z ≡ x ∸ (y + z)
∸-+-associative x zero z = reflexivity
∸-+-associative zero (successor y) zero = reflexivity
∸-+-associative zero (successor y) (successor z) = reflexivity
∸-+-associative (successor x) (successor y) z = begin
  successor x ∸ successor y ∸ z ≡⟨⟩
  x ∸ y ∸ z ≡⟨ ∸-+-associative x y z ⟩
  x ∸ (y + z) ∎

^-distributes-over-×-on-the-right : ∀ (x y z : ℕ) → (x × y) ^ z ≡ x ^ z × y ^ z
^-distributes-over-×-on-the-right x y zero = reflexivity
^-distributes-over-×-on-the-right x y (successor z) = begin
  (x × y) ^ successor z ≡⟨⟩
  x × y × (x × y) ^ z ≡⟨ congruence (λ e → x × y × e) (^-distributes-over-×-on-the-right x y z) ⟩
  x × y × (x ^ z × y ^ z) ≡⟨ ×-is-associative (x × y) (x ^ z) (y ^ z) ⟩
  x × y × x ^ z × y ^ z ≡⟨ congruence (λ e → e × y ^ z) (symmetry (×-is-associative x y (x ^ z))) ⟩
  x × (y × x ^ z) × y ^ z ≡⟨ congruence (λ e → x × e × y ^ z) (×-is-commutative y (x ^ z)) ⟩
  x × (x ^ z × y) × y ^ z ≡⟨ congruence (λ e → e × y ^ z) (×-is-associative x (x ^ z) y) ⟩
  x ^ successor z × y × y ^ z ≡⟨ symmetry (×-is-associative (x ^ successor z) y (y ^ z)) ⟩
  x ^ successor z × y ^ successor z ∎

^-distributes-over-+-into-×-on-the-left : ∀ (x y z : ℕ) → x ^ (y + z) ≡ x ^ y × x ^ z
^-distributes-over-+-into-×-on-the-left x zero z = begin
  x ^ (zero + z) ≡⟨⟩
  x ^ z ≡⟨ symmetry (left-identity-of-× (x ^ z)) ⟩
  1 × x ^ z ≡⟨⟩
  x ^ zero × x ^ z ∎
^-distributes-over-+-into-×-on-the-left x (successor y) z = begin
  x ^ (successor y + z) ≡⟨⟩
  x × x ^ (y + z) ≡⟨ congruence (λ e → x × e) (^-distributes-over-+-into-×-on-the-left x y z) ⟩
  x × (x ^ y × x ^ z) ≡⟨ ×-is-associative x (x ^ y) (x ^ z) ⟩
  x × x ^ y × x ^ z ≡⟨⟩
  x ^ successor y × x ^ z ∎

^-×-associative : ∀ (x y z : ℕ) → (x ^ y) ^ z ≡ x ^ (y × z)
^-×-associative x y zero = begin
  (x ^ y) ^ zero ≡⟨⟩
  1 ≡⟨⟩
  x ^ zero ≡⟨ congruence (λ e → x ^ e) (symmetry (right-absorption-of-× y)) ⟩
  x ^ (y × zero) ∎
^-×-associative x y (successor z) = begin
  (x ^ y) ^ successor z ≡⟨⟩
  x ^ y × (x ^ y) ^ z ≡⟨ congruence (λ e → x ^ y × e) (^-×-associative x y z) ⟩
  x ^ y × x ^ (y × z) ≡⟨ symmetry (^-distributes-over-+-into-×-on-the-left x y (y × z)) ⟩
  x ^ (y + y × z) ≡⟨ congruence (λ e → x ^ e) (symmetry (×-move y z)) ⟩
  x ^ (y × successor z) ∎

morph-successor : ∀ (x : ℕ₂) → ℕ₂→ℕ (successor₂ x) ≡ successor (ℕ₂→ℕ x)
morph-successor ₂ = reflexivity
morph-successor (x ·) = begin
  ℕ₂→ℕ (successor₂ (x ·)) ≡⟨⟩
  ℕ₂→ℕ (x I) ≡⟨⟩
  successor ((ℕ₂→ℕ x) × 2) ≡⟨⟩
  successor (ℕ₂→ℕ (x ·)) ∎
morph-successor (x I) = begin
  ℕ₂→ℕ (successor₂ (x I)) ≡⟨⟩
  ℕ₂→ℕ (successor₂ x ·) ≡⟨⟩
  ℕ₂→ℕ (successor₂ x) × 2 ≡⟨ congruence (λ e → e × 2) (morph-successor x) ⟩
  (1 + ℕ₂→ℕ x) × 2 ≡⟨ ×-distributes-over-+-on-the-right 1 (ℕ₂→ℕ x) 2 ⟩
  2 + ℕ₂→ℕ x × 2 ≡⟨⟩
  2 + ℕ₂→ℕ (x ·) ≡⟨⟩
  1 + successor (ℕ₂→ℕ (x ·)) ≡⟨⟩
  1 + successor (ℕ₂→ℕ x × 2) ≡⟨⟩
  successor (ℕ₂→ℕ (x I)) ∎

ℕ₂→ℕ-retracts-ℕ→ℕ₂ : ∀ (x : ℕ) → ℕ₂→ℕ (ℕ→ℕ₂ x) ≡ x
ℕ₂→ℕ-retracts-ℕ→ℕ₂ zero = reflexivity
ℕ₂→ℕ-retracts-ℕ→ℕ₂ (successor x) = begin
  ℕ₂→ℕ (ℕ→ℕ₂ (successor x)) ≡⟨⟩
  ℕ₂→ℕ (successor₂ (ℕ→ℕ₂ x)) ≡⟨ morph-successor (ℕ→ℕ₂ x) ⟩
  successor (ℕ₂→ℕ (ℕ→ℕ₂ x)) ≡⟨ congruence (λ e → successor e) (ℕ₂→ℕ-retracts-ℕ→ℕ₂ x) ⟩
  successor x ∎

open import Data.Empty

_ : ℕ→ℕ₂ (ℕ₂→ℕ (₂ ·)) ≢ ₂ ·
_ = λ ( )
