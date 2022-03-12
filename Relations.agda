module Relations where

open import Prelude
open import Natural_Numbers
open import Tactic.RingSolver
open import Tactic.RingSolver.Core.AlmostCommutativeRing
open import Data.Maybe.Base using (just; nothing)

data _≤_ : ℕ → ℕ → Set where
  zero-≤-x : ∀ {x : ℕ} → zero ≤ x
  successor-x-≤-successor-y : ∀ {x y : ℕ} → x ≤ y → successor x ≤ successor y

infix 4 _≤_

≤-inversion-successor : ∀ {x y : ℕ} → successor x ≤ successor y → x ≤ y
≤-inversion-successor (successor-x-≤-successor-y recurse) = recurse

≤-inversion-zero : ∀ {x : ℕ} → x ≤ zero → x ≡ zero
≤-inversion-zero zero-≤-x = reflexivity

≤-is-reflexive : ∀ {x : ℕ} → x ≤ x
≤-is-reflexive {zero} = zero-≤-x
≤-is-reflexive {successor x} = successor-x-≤-successor-y ≤-is-reflexive

≤-is-transitive : ∀ {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
≤-is-transitive zero-≤-x evidence₂ = zero-≤-x
≤-is-transitive (successor-x-≤-successor-y evidence₁) (successor-x-≤-successor-y evidence₂)
  = successor-x-≤-successor-y (≤-is-transitive evidence₁ evidence₂)

≤-is-antisymmetric : ∀ {x y : ℕ} → x ≤ y → y ≤ x → x ≡ y
≤-is-antisymmetric zero-≤-x zero-≤-x = reflexivity
≤-is-antisymmetric (successor-x-≤-successor-y evidence₁) (successor-x-≤-successor-y evidence₂)
  = congruence successor (≤-is-antisymmetric evidence₁ evidence₂)

data Related (_~_ : ℕ → ℕ → Set) (x y : ℕ) : Set where
  one-way : x ~ y → Related _~_ x y
  other-way : y ~ x → Related _~_ x y

≤-is-total : ∀ (x y : ℕ) → Related _≤_ x y
≤-is-total zero y = one-way zero-≤-x
≤-is-total (successor x) zero = other-way zero-≤-x
≤-is-total (successor x) (successor y) with ≤-is-total x y
… | one-way evidence = one-way (successor-x-≤-successor-y evidence)
… | other-way evidence = other-way (successor-x-≤-successor-y evidence)

weaken-≤-rightwards : ∀ (x y : ℕ) → x ≤ y → x ≤ successor y
weaken-≤-rightwards zero y zero-≤-x = zero-≤-x
weaken-≤-rightwards (successor x) (successor y) (successor-x-≤-successor-y evidence)
  = successor-x-≤-successor-y (weaken-≤-rightwards x y evidence)

weaken-≤-leftwards : ∀ (x y : ℕ) → successor x ≤ y → x ≤ y
weaken-≤-leftwards zero (successor y) (successor-x-≤-successor-y evidence) = zero-≤-x
weaken-≤-leftwards (successor x₁) (successor y) (successor-x-≤-successor-y evidence)
  = successor-x-≤-successor-y (weaken-≤-leftwards x₁ y evidence)

+-is-≤-monotone-on-the-left : ∀ (x y topping : ℕ) → x ≤ y → x + topping ≤ y + topping
+-is-≤-monotone-on-the-left x y zero evidence = substitute (λ e → e ≤ y + zero) (symmetry (+identity x)) (substitute (λ e → x ≤ e) (symmetry (+identity y)) evidence)
+-is-≤-monotone-on-the-left x y (successor topping) evidence
  = substitution (successor-x-≤-successor-y (+-is-≤-monotone-on-the-left x y topping evidence))
    where
      substitution
        = substitute (λ e → e ≤ y + successor topping) (symmetry (+successor-move x topping))
        ∘ substitute (λ e → successor (x + topping) ≤ e) (symmetry (+successor-move y topping))

+-is-≤-monotone-on-the-right : ∀ (x y topping : ℕ) → x ≤ y → topping + x ≤ topping + y
+-is-≤-monotone-on-the-right x y zero evidence = evidence
+-is-≤-monotone-on-the-right x y (successor topping) evidence
  = successor-x-≤-successor-y (+-is-≤-monotone-on-the-right x y topping evidence)

+-is-≤-monotone : ∀ (x₁ x₂ y₁ y₂ : ℕ) → x₁ ≤ y₁ → x₂ ≤ y₂ → x₁ + x₂ ≤ y₁ + y₂
+-is-≤-monotone x₁ x₂ y₁ y₂ evidence₁ evidence₂ = ≤-is-transitive step₁ step₂
  where
    step₁ = +-is-≤-monotone-on-the-left x₁ y₁ x₂ evidence₁
    step₂ = +-is-≤-monotone-on-the-right x₂ y₂ y₁ evidence₂

×-is-≤-monotone-on-the-right : ∀ (x y topping : ℕ) → x ≤ y → topping × x ≤ topping × y
×-is-≤-monotone-on-the-right x y zero evidence = zero-≤-x
×-is-≤-monotone-on-the-right x y (successor topping) evidence
  = +-is-≤-monotone x (topping × x) y (topping × y) evidence (×-is-≤-monotone-on-the-right x y topping evidence)

×-is-≤-monotone-on-the-left : ∀ (x y topping : ℕ) → x ≤ y → x × topping ≤ y × topping
×-is-≤-monotone-on-the-left x y zero evidence = substitute (λ e → e ≤ y × zero) (symmetry (right-absorption-of-× x)) zero-≤-x
×-is-≤-monotone-on-the-left x y (successor topping) evidence
  rewrite ×-is-commutative x (successor topping) | ×-is-commutative y (successor topping)
  = +-is-≤-monotone x (topping × x) y (topping × y) evidence (×-is-≤-monotone-on-the-right x y topping evidence)

×-is-≤-monotone : ∀ (x₁ x₂ y₁ y₂ : ℕ) → x₁ ≤ y₁ → x₂ ≤ y₂ → x₁ × x₂ ≤ y₁ × y₂
×-is-≤-monotone x₁ x₂ y₁ y₂ evidence₁ evidence₂ = ≤-is-transitive step₁ step₂
  where
    step₁ = ×-is-≤-monotone-on-the-left x₁ y₁ x₂ evidence₁
    step₂ = ×-is-≤-monotone-on-the-right x₂ y₂ y₁ evidence₂

data _<_ : ℕ → ℕ → Set where
  defer-to-≤ : ∀ {x y : ℕ} → successor x ≤ y → x < y

infix 4 _<_

<-is-anti-reflexive : ∀ {x : ℕ} → ¬ (x < x)
<-is-anti-reflexive {successor x} (defer-to-≤ (successor-x-≤-successor-y x')) = <-is-anti-reflexive (defer-to-≤ x')

<-is-transitive : ∀ {x y z : ℕ} → x < y → y < z → x < z
<-is-transitive (defer-to-≤ (successor-x-≤-successor-y evidence₁)) (defer-to-≤ (successor-x-≤-successor-y evidence₂))
  = defer-to-≤ (successor-x-≤-successor-y (≤-is-transitive evidence₁ (weaken-≤-leftwards _ _ evidence₂)))

data Three-Way (x y : ℕ) : Set where
  smaller : x < y → Three-Way x y
  of-even-size : x ≡ y → Three-Way x y
  bigger : y < x → Three-Way x y

three-way : ∀ (x y : ℕ) → Three-Way x y
three-way zero zero = of-even-size reflexivity
three-way zero (successor y) = smaller (defer-to-≤ (successor-x-≤-successor-y zero-≤-x))
three-way (successor x) zero = bigger (defer-to-≤ (successor-x-≤-successor-y zero-≤-x))
three-way (successor x) (successor y) with three-way x y
... | smaller (defer-to-≤ evidence) = smaller (defer-to-≤ (successor-x-≤-successor-y evidence))
… | of-even-size evidence = of-even-size (congruence successor evidence)
... | bigger (defer-to-≤ evidence) = bigger (defer-to-≤ (successor-x-≤-successor-y evidence))

weaken-<-rightwards : ∀ (x y : ℕ) → x < y → x < successor y
weaken-<-rightwards x y (defer-to-≤ evidence) = defer-to-≤ (weaken-≤-rightwards (successor x) y evidence)

weaken-<-leftwards : ∀ (x y : ℕ) → successor x < y → x < y
weaken-<-leftwards x y (defer-to-≤ evidence) = defer-to-≤ (weaken-≤-leftwards (successor x) y evidence)

+-is-<-monotone-on-the-left : ∀ (x y topping : ℕ) → x < y → x + topping < y + topping
+-is-<-monotone-on-the-left x y topping (defer-to-≤ evidence)
  = defer-to-≤ (+-is-≤-monotone-on-the-left (successor x) y topping evidence)

+-is-<-monotone-on-the-right : ∀ (x y topping : ℕ) → x < y → topping + x < topping + y
+-is-<-monotone-on-the-right x y topping (defer-to-≤ evidence) = defer-to-≤ (substitute (λ e → e ≤ topping + y) (+successor-move topping x) (+-is-≤-monotone-on-the-right (successor x) y topping evidence))

+-is-<-monotone : ∀ (x₁ x₂ y₁ y₂ : ℕ) → x₁ < y₁ → x₂ < y₂ → x₁ + x₂ < y₁ + y₂
+-is-<-monotone x₁ x₂ y₁ y₂ evidence₁ evidence₂ = <-is-transitive step₁ step₂
  where
    step₁ = +-is-<-monotone-on-the-left x₁ y₁ x₂ evidence₁
    step₂ = +-is-<-monotone-on-the-right x₂ y₂ y₁ evidence₂

data _≡_by_ (x y modulus : ℕ) : Set
  where
    congruent
      : ∀ (times-x times-y remainder : ℕ)
      → x ≡ remainder + times-x × modulus
      → y ≡ remainder + times-y × modulus
      → x ≡ y by modulus

even : ℕ → Set
even x = x ≡ zero by 2

pattern truly-even times-2 = congruent times-2 zero zero reflexivity reflexivity

_ : even 4
_ = truly-even 2

_ : even 100
_ = truly-even 50

data even' : ℕ → Set
data odd' : ℕ → Set

data even' where
  zero-is-even : even' zero
  successor-is-even : ∀ {x} → odd' x → even' (successor x)

data odd' where
  one-is-odd : odd' (successor zero)
  successor-is-odd : ∀ {x} → even' x → odd' (successor x)

pattern next-even x = successor-is-even (successor-is-odd x)

even'→even : ∀ {x} → even' x → even x
even'→even zero-is-even = truly-even zero
even'→even (successor-is-even one-is-odd) = truly-even 1
even'→even (next-even evidence) with even'→even evidence
even'→even (next-even evidence) | truly-even times-2 = truly-even (successor times-2)

even→even' : ∀ {x} → even x → even' x
even→even' {zero} _ = zero-is-even
even→even' (truly-even (successor times-x)) = (next-even ∘ even→even' ∘ truly-even) times-x

odd : ℕ → Set
odd x = x ≡ 1 by 2

pattern truly-odd times-2 = congruent times-2 zero 1 reflexivity reflexivity

open import Algebra.Bundles using (RawRing; CommutativeRing; CommutativeSemiring)

ring : AlmostCommutativeRing _ _
ring = fromCommutativeSemiring
  (record {isCommutativeSemiring = +-×-isCommutativeSemiring})
  λ {0 → just reflexivity; _ → nothing}

open import Data.List using (_∷_; [])

even-the-odds : ∀ {x y} → x ≡ y by 2 → even (x + y)
even-the-odds (congruent times-x times-y remainder reflexivity reflexivity)
  = congruent (times-x + times-y + remainder) zero zero (solve (remainder ∷ times-x ∷ times-y ∷ []) ring) reflexivity
