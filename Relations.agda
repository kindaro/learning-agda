module Relations where

open import Prelude hiding (_×_)
open ℕ using (zero; successor)
open import Natural_Numbers
open import Tactic.RingSolver
open import Tactic.RingSolver.Core.AlmostCommutativeRing
open import Data.Maybe.Base using (just; nothing)
open import Data.Product using (∃; _,_) renaming  (_×_ to _×'_)
open import Data.Sum
open import Accessible

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

weaken-≤-rightwards : ∀ {x y : ℕ} → x ≤ y → x ≤ successor y
weaken-≤-rightwards {zero} {y} zero-≤-x = zero-≤-x
weaken-≤-rightwards {successor x} {successor y} (successor-x-≤-successor-y evidence)
  = successor-x-≤-successor-y (weaken-≤-rightwards evidence)

weaken-≤-leftwards : ∀ {x y : ℕ} → successor x ≤ y → x ≤ y
weaken-≤-leftwards {zero} {successor y} (successor-x-≤-successor-y evidence) = zero-≤-x
weaken-≤-leftwards {successor x₁} {successor y} (successor-x-≤-successor-y evidence)
  = successor-x-≤-successor-y (weaken-≤-leftwards {x₁} {y} evidence)

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

+-is-≤-monotone : ∀ {x₁ x₂ y₁ y₂ : ℕ} → x₁ ≤ y₁ → x₂ ≤ y₂ → x₁ + x₂ ≤ y₁ + y₂
+-is-≤-monotone {x₁} {x₂} {y₁} {y₂} evidence₁ evidence₂ = ≤-is-transitive step₁ step₂
  where
    step₁ = +-is-≤-monotone-on-the-left x₁ y₁ x₂ evidence₁
    step₂ = +-is-≤-monotone-on-the-right x₂ y₂ y₁ evidence₂

×-is-≤-monotone-on-the-right : ∀ (x y topping : ℕ) → x ≤ y → topping × x ≤ topping × y
×-is-≤-monotone-on-the-right x y zero evidence = zero-≤-x
×-is-≤-monotone-on-the-right x y (successor topping) evidence
  = +-is-≤-monotone {x} {topping × x} {y} {topping × y} evidence (×-is-≤-monotone-on-the-right x y topping evidence)

×-is-≤-monotone-on-the-left : ∀ (x y topping : ℕ) → x ≤ y → x × topping ≤ y × topping
×-is-≤-monotone-on-the-left x y zero evidence = substitute (λ e → e ≤ y × zero) (symmetry (right-absorption-of-× x)) zero-≤-x
×-is-≤-monotone-on-the-left x y (successor topping) evidence
  rewrite ×-is-commutative x (successor topping) | ×-is-commutative y (successor topping)
  = +-is-≤-monotone {x} {topping × x} {y} {topping × y} evidence (×-is-≤-monotone-on-the-right x y topping evidence)

×-is-≤-monotone : ∀ (x₁ x₂ y₁ y₂ : ℕ) → x₁ ≤ y₁ → x₂ ≤ y₂ → x₁ × x₂ ≤ y₁ × y₂
×-is-≤-monotone x₁ x₂ y₁ y₂ evidence₁ evidence₂ = ≤-is-transitive step₁ step₂
  where
    step₁ = ×-is-≤-monotone-on-the-left x₁ y₁ x₂ evidence₁
    step₂ = ×-is-≤-monotone-on-the-right x₂ y₂ y₁ evidence₂

≤-is-proof-irrelevant : ∀ {n m : ℕ} (proof₁ proof₂ : n ≤ m) → proof₁ ≡ proof₂
≤-is-proof-irrelevant zero-≤-x zero-≤-x = reflexivity
≤-is-proof-irrelevant (successor-x-≤-successor-y proof₁) (successor-x-≤-successor-y proof₂) = congruence successor-x-≤-successor-y (≤-is-proof-irrelevant proof₁ proof₂)

data _<_ : ℕ → ℕ → Set where
  defer-to-≤ : ∀ {x y : ℕ} → successor x ≤ y → x < y

infix 4 _<_

rephrase-<-as-≤ : ∀ {x y} → x < y → successor x ≤ y
rephrase-<-as-≤ (defer-to-≤ evidence) = evidence

<-is-anti-reflexive : ∀ {x : ℕ} → ¬ (x < x)
<-is-anti-reflexive {successor x} (defer-to-≤ (successor-x-≤-successor-y x')) = <-is-anti-reflexive (defer-to-≤ x')

<-is-transitive : ∀ {x y z : ℕ} → x < y → y < z → x < z
<-is-transitive (defer-to-≤ (successor-x-≤-successor-y evidence₁)) (defer-to-≤ (successor-x-≤-successor-y evidence₂))
  = defer-to-≤ (successor-x-≤-successor-y (≤-is-transitive evidence₁ (weaken-≤-leftwards evidence₂)))

data Three-Way (x y : ℕ) : Set where
  smaller : x < y → Three-Way x y
  of-even-size : x ≡ y → Three-Way x y
  bigger : y < x → Three-Way x y

three-way : ∀ (x y : ℕ) → Three-Way x y
three-way zero zero = of-even-size reflexivity
three-way zero (successor y) = smaller (defer-to-≤ (successor-x-≤-successor-y zero-≤-x))
three-way (successor x) zero = bigger (defer-to-≤ (successor-x-≤-successor-y zero-≤-x))
three-way (successor x) (successor y) with three-way x y
… | smaller (defer-to-≤ evidence) = smaller (defer-to-≤ (successor-x-≤-successor-y evidence))
… | of-even-size evidence = of-even-size (congruence successor evidence)
… | bigger (defer-to-≤ evidence) = bigger (defer-to-≤ (successor-x-≤-successor-y evidence))

weaken-<-rightwards : ∀ {x y : ℕ} → x < y → x < successor y
weaken-<-rightwards {x} {y} (defer-to-≤ evidence) = defer-to-≤ (weaken-≤-rightwards {successor x} {y} evidence)

weaken-<-rightwards-more : ∀ {x y z : ℕ} → x < y → x < z + y
weaken-<-rightwards-more {zero} {successor y} {z} (defer-to-≤ (successor-x-≤-successor-y zero-≤-x))
  rewrite +successor-move z y
  = defer-to-≤ (successor-x-≤-successor-y zero-≤-x)
weaken-<-rightwards-more
  {successor x} {successor (successor y)} {z}
  (defer-to-≤ (successor-x-≤-successor-y (successor-x-≤-successor-y evidence)))
  rewrite +successor-move z (successor y)
  rewrite +successor-move z y
  with weaken-<-rightwards-more {x} {successor y} {z} (defer-to-≤ (successor-x-≤-successor-y evidence))
… | defer-to-≤ recursive-evidence rewrite +successor-move z y = defer-to-≤ (successor-x-≤-successor-y recursive-evidence)

weaken-<-leftwards : ∀ {x y : ℕ} → successor x < y → x < y
weaken-<-leftwards {x} {y} (defer-to-≤ evidence) = defer-to-≤ (weaken-≤-leftwards {successor x} {y} evidence)

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

witness-≤ : {small big : ℕ} → small ≤ big → ∃ λ leftover → (leftover + small) ≡ big
witness-≤ {.ℕ-zero} {big} zero-≤-x = big , cancel-zero-on-the-right
witness-≤ {ℕ-successor small} {ℕ-successor big} (successor-x-≤-successor-y evidence) with witness-≤ evidence
... | number , proof rewrite symmetry proof = number , commute-successor number small

witness-< : {small big : ℕ} → small < big → ∃ λ leftover → successor (leftover + small) ≡ big
witness-< {small} {zero} (defer-to-≤ ())
witness-< {zero} {successor big} (defer-to-≤ (successor-x-≤-successor-y evidence)) = big , congruence successor (+identity big)
witness-< {successor small} {successor big} (defer-to-≤ (successor-x-≤-successor-y evidence)) with witness-< (defer-to-≤ evidence)
... | new-value , new-evidence = new-value , supplement
  where
    supplement : successor (new-value + successor small) ≡ successor big
    supplement = begin
      successor (new-value + successor small) ≡⟨ congruence successor (+successor-move new-value small) ⟩
      successor (successor (new-value + small)) ≡⟨ congruence successor new-evidence ⟩
      successor big ∎

<-is-well-founded : well-founded _<_
<-is-well-founded zero = access lemma
  where
    lemma : (n : ℕ) → (n < zero) → Accessible _<_ n
    lemma n (defer-to-≤ ())
<-is-well-founded (successor n) with <-is-well-founded n
... | access evidence = access (lemma n evidence)
  where
    lemma : (n : ℕ) → ((a : ℕ) → a < n → Accessible _<_ a) → (m : ℕ) → m < successor n → Accessible _<_ m
    lemma n recursive-evidence m evidence with witness-< evidence
    ... | zero , reflexivity = access recursive-evidence
    ... | successor fst , reflexivity = access λ a a<m → recursive-evidence a (weaken-<-rightwards {a} {fst + m} (weaken-<-rightwards-more {a} {m} {fst} a<m))

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
… | truly-even times-2 = truly-even (successor times-2)

even→even' : ∀ {x} → even x → even' x
even→even' {zero} _ = zero-is-even
even→even' (truly-even (successor times-x)) = (next-even ∘ even→even' ∘ truly-even) times-x

odd : ℕ → Set
odd x = x ≡ 1 by 2

pattern truly-odd times-2 = congruent times-2 zero 1 reflexivity reflexivity

dichotomy : Set → Set → Set
dichotomy x y = (x ×' (¬ y)) ⊎ ((¬ x) ×' y)

_≤[_]≤_ : ∀ (lower-bound inside upper-bound : ℕ) → Set
x ≤[ y ]≤ z = x ≤ y ×' y ≤ z

within : ℕ → Relation ℕ ℓ₀
within upper-bound = λ haft lower-bound → ℕ-successor lower-bound ≤[ haft ]≤ upper-bound

_≥[_]>_ = within

successor-≤-is-false : ∀ {number} → successor number ≤ number → ⊥
successor-≤-is-false {ℕ-zero} ()
successor-≤-is-false {ℕ-successor number} (successor-x-≤-successor-y evidence) = successor-≤-is-false evidence

within-is-well-founded : ∀ upper-bound → well-founded (within upper-bound)
within-is-well-founded upper-bound lower-bound = access λ haft binding → case binding of
  λ (lower-binding , upper-binding) → case witness-≤ upper-binding of
    λ (leftover , equation) → lemma₂ upper-bound lower-bound haft leftover lower-binding upper-binding equation
  where
    lemma₂ : ∀ upper-bound lower-bound haft leftover
      (lower-binding : ℕ-successor lower-bound ≤ haft)
      (upper-binding : haft ≤ upper-bound)
      (equation : leftover + haft ≡ upper-bound) → Accessible (within upper-bound) haft
    lemma₂ upper-bound lower-bound .upper-bound ℕ-zero lower-binding upper-binding reflexivity = access
      λ higher-haft (higher-lower-binding , higher-upper-binding) →
          let contradiction = ≤-is-transitive higher-lower-binding higher-upper-binding
          in (ex-falso ∘ successor-≤-is-false) contradiction
    lemma₂ upper-bound lower-bound haft (ℕ-successor leftover) lower-binding upper-binding reflexivity = access
      λ higher-haft (higher-lower-binding , higher-upper-binding) →
        let proof = successor-x-≤-successor-y (+-is-≤-monotone zero-≤-x ≤-is-reflexive)
        in case lemma₂ upper-bound haft (ℕ-successor haft) leftover ≤-is-reflexive proof (commute-successor leftover haft) of
          λ where induction-hypothesis@(access inner-induction-hypothesis) → case three-way (ℕ-successor (ℕ-successor haft)) higher-haft of λ where
            (smaller (defer-to-≤ evidence)) → inner-induction-hypothesis higher-haft (weaken-≤-leftwards evidence , higher-upper-binding)
            (of-even-size reflexivity) → inner-induction-hypothesis higher-haft (≤-is-reflexive , higher-upper-binding)
            (bigger (defer-to-≤ (successor-x-≤-successor-y evidence))) → case ≤-is-antisymmetric evidence higher-lower-binding of
              λ where reflexivity → induction-hypothesis

_−_[_,_] : ∀ (minuend subtrahend : ℕ) → 0 < subtrahend → subtrahend ≤ minuend → ℕ
successor minuend − successor zero [ defer-to-≤ _ , _ ] = minuend
successor (successor minuend) − successor (successor subtrahend)
  [ defer-to-≤ _ , successor-x-≤-successor-y (successor-x-≤-successor-y evidence) ]
    = successor minuend − successor subtrahend
      [ defer-to-≤ (successor-x-≤-successor-y zero-≤-x) , successor-x-≤-successor-y evidence ]

module X where

  successor-−-reduce
    : ∀ (minuend subtrahend : ℕ)
    → Σ ((0 < ℕ-successor subtrahend) ×' (ℕ-successor subtrahend ≤ ℕ-successor minuend ×' (0 < subtrahend ×' subtrahend ≤ minuend))) λ (proof₁ , (proof₂ , (proof₁' , proof₂'))) → ℕ-successor minuend − ℕ-successor (ℕ-successor subtrahend) [ proof₁ , proof₂ ] ≡ minuend − ℕ-successor subtrahend [ proof₁' , proof₂' ]
  successor-−-reduce minuend subtrahend proof₁ proof₂ proof₁' proof₂'
    = let x = Total.fold {ℕ} {within minuend} {λ subtrahend → Σ ((0 < ℕ-successor subtrahend) ×' (ℕ-successor subtrahend ≤ ℕ-successor minuend ×' (0 < subtrahend ×' subtrahend ≤ minuend))) λ (proof₁ , (proof₂ , (proof₁' , proof₂'))) → ℕ-successor minuend − ℕ-successor subtrahend [ proof₁ , proof₂ ] ≡ minuend − subtrahend [ proof₁' , proof₂' ]} (within-is-well-founded minuend) subtrahend {!!}
      in π₂ x
     -- I can introduce a Σ type with proofs and then apply proof irrelevance.

  lemma
    : ∀ (minuend subtrahend : ℕ) → ∀ (proof₁ : 0 < subtrahend) (proof₂ : ℕ-successor subtrahend ≤ minuend)
    → (minuend − subtrahend [ proof₁ , weaken-≤-leftwards proof₂ ]) < minuend
    → (minuend − ℕ-successor subtrahend [ weaken-<-rightwards proof₁ , proof₂ ]) < minuend
  lemma (ℕ-successor .(ℕ-successor _)) (ℕ-successor ℕ-zero)
    (defer-to-≤ (successor-x-≤-successor-y zero-≤-x))
    (successor-x-≤-successor-y (successor-x-≤-successor-y zero-≤-x))
    _
      = defer-to-≤ (successor-x-≤-successor-y (weaken-≤-rightwards ≤-is-reflexive))
  lemma (ℕ-successor (ℕ-successor (ℕ-successor minuend))) (ℕ-successor (ℕ-successor subtrahend)) (defer-to-≤ (successor-x-≤-successor-y zero-≤-x)) (successor-x-≤-successor-y (successor-x-≤-successor-y (successor-x-≤-successor-y evidence))) (defer-to-≤ (successor-x-≤-successor-y x₁)) = {!!}

  −-belittles
    : ∀ (minuend subtrahend : ℕ)
    → ∀ (proof₁ : 0 < subtrahend) → ∀ (proof₂ : subtrahend ≤ minuend)
    → (minuend − subtrahend [ proof₁ , proof₂ ]) < minuend
  −-belittles _ ℕ-zero (defer-to-≤ ()) _
  −-belittles minuend (ℕ-successor subtrahend) proof₁ proof₂ = case three-way 0 subtrahend of λ where
          (smaller evidence) →
            let induction-hypothesis = −-belittles minuend subtrahend evidence (weaken-≤-leftwards proof₂)
            in {!lemma induction-hypothesis!}
          (of-even-size x') → {!!}
          (bigger x') → {!!}

remainder : ∀ (dividend divisor : ℕ) → 0 < divisor → ℕ
remainder dividend divisor divisor-is-non-zero = Total.fold <-is-well-founded dividend
  λ recursive-dividend recursion → lemma recursive-dividend recursion (three-way recursive-dividend divisor)
  where
    lemma : ∀ dividend → (∀ a → a < dividend → ℕ) → Three-Way dividend divisor → ℕ
    lemma dividend _ (smaller _) = dividend
    lemma dividend _ (of-even-size _) = 0
    lemma dividend recursion (bigger (defer-to-≤ evidence))
      with dividend − divisor [ divisor-is-non-zero , weaken-≤-leftwards evidence ] in X
    lemma (ℕ-successor dividend) recursion (bigger (defer-to-≤ evidence)) | ℕ-zero = recursion ℕ-zero (defer-to-≤ (successor-x-≤-successor-y zero-≤-x))
    lemma (ℕ-successor dividend) recursion (bigger (defer-to-≤ evidence)) | ℕ-successor stuff = recursion (ℕ-successor stuff) (defer-to-≤ (successor-x-≤-successor-y {!!}))

-- _ : remainder 10 3 ≡ 1
-- _ = reflexivity

even-odd-dichotomy : ∀ n → dichotomy (even n) (odd n)
even-odd-dichotomy n = {!!}


open import Algebra.Bundles using (RawRing; CommutativeRing; CommutativeSemiring)

ring : AlmostCommutativeRing _ _
ring = fromCommutativeSemiring
  (record {isCommutativeSemiring = +-×-isCommutativeSemiring})
  λ {0 → just reflexivity; _ → nothing}

open import Data.List using (_∷_; [])

even-the-odds : ∀ {x y} → x ≡ y by 2 → even (x + y)
even-the-odds (congruent times-x times-y remainder reflexivity reflexivity)
  = congruent (times-x + times-y + remainder) zero zero (solve (remainder ∷ times-x ∷ times-y ∷ []) ring) reflexivity

data ends-in-I : ℕ₂ → Set
  where
    I-ends-in-I : ends-in-I (₂ I)
    recursive-· : ∀ {n} → ends-in-I n → ends-in-I (n ·)
    recursive-I : ∀ {n} → ends-in-I n → ends-in-I (n I)

data is-canonical : ℕ₂ → Set
  where
    canonical-zero : is-canonical (₂)
    canonical : ∀ {n} → ends-in-I n → is-canonical n

_ : is-canonical (₂ I · I)
_ = canonical (recursive-I (recursive-· I-ends-in-I))

successor₂-ends-in-I : ∀ {n} → ends-in-I n → ends-in-I (successor₂ n)
successor₂-ends-in-I I-ends-in-I = recursive-· I-ends-in-I
successor₂-ends-in-I (recursive-· evidence) = recursive-I evidence
successor₂-ends-in-I (recursive-I evidence) = recursive-· (successor₂-ends-in-I evidence)

successor₂-respects-canonicity : ∀ {n} → is-canonical n → is-canonical (successor₂ n)
successor₂-respects-canonicity canonical-zero = canonical I-ends-in-I
successor₂-respects-canonicity (canonical evidence) = canonical (successor₂-ends-in-I evidence)

conversion-is-canonical : ∀ n → is-canonical (ℕ→ℕ₂ n)
conversion-is-canonical zero = canonical-zero
conversion-is-canonical (successor n) = successor₂-respects-canonicity (conversion-is-canonical n)

if-n₂-ends-in-I-it-is-never-zero : ∀ n₂ → ends-in-I n₂ → zero < ℕ₂→ℕ n₂
if-n₂-ends-in-I-it-is-never-zero ₂ ( )
if-n₂-ends-in-I-it-is-never-zero (.₂ I) I-ends-in-I = defer-to-≤ (successor-x-≤-successor-y zero-≤-x)
if-n₂-ends-in-I-it-is-never-zero (n₂ I) (recursive-I evidence) = defer-to-≤ (successor-x-≤-successor-y zero-≤-x)
if-n₂-ends-in-I-it-is-never-zero (n₂ ·) (recursive-· evidence) with (if-n₂-ends-in-I-it-is-never-zero n₂ evidence)
… | defer-to-≤ recursive-evidence = recurse recursive-evidence
  where
    recurse
      = defer-to-≤
      ∘ weaken-≤-leftwards {1} {ℕ₂→ℕ n₂ × 2}
      ∘ ×-is-≤-monotone-on-the-left 1 (ℕ₂→ℕ n₂) 2

reverse-absorption : ∀ n → n × 2 ≡ 0 → n ≡ 0
reverse-absorption zero reflexivity = reflexivity
reverse-absorption (successor n) ( )

ℕ₂→ℕ≡0 : ∀ n₂ → is-canonical n₂ → ℕ₂→ℕ n₂ ≡ 0 → n₂ ≡ ₂
ℕ₂→ℕ≡0 .₂ canonical-zero evidence-of-equality = reflexivity
ℕ₂→ℕ≡0 (n₂ ·) (canonical (recursive-· evidence)) evidence-of-equality with if-n₂-ends-in-I-it-is-never-zero n₂ evidence
… | defer-to-≤ evidence-of-inequality with reverse-absorption (ℕ₂→ℕ n₂) evidence-of-equality
… | simpler-evidence-of-equality with ℕ₂→ℕ n₂
ℕ₂→ℕ≡0 (n₂ ·) (canonical (recursive-· evidence)) evidence-of-equality | defer-to-≤ ( ) | simpler-evidence-of-equality | zero
ℕ₂→ℕ≡0 (n₂ ·) (canonical (recursive-· evidence)) evidence-of-equality | defer-to-≤ evidence-of-inequality | ( ) | successor n

split-monic : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {g : B → A} → (∀ {a : A} → g (f a) ≡ a) → ∀ {a₁ a₂ : A} → f a₁ ≡ f a₂ → a₁ ≡ a₂
split-monic {_} {_} {_} (f) {g} g-retracts-f {a₁} {a₂} f-equality
  = begin a₁ ≡⟨ symmetry g-retracts-f ⟩ g (f a₁) ≡⟨ congruence g f-equality ⟩ g (f a₂) ≡⟨ g-retracts-f ⟩ a₂ ∎

equality-case : ∀ {number} → ends-in-I number → (number ·) ≡ ℕ→ℕ₂ (ℕ₂→ℕ number × 2)
equality-case {₂} ()
equality-case {.₂ I} I-ends-in-I = reflexivity
equality-case {number I} (recursive-I evidence) = {!!}
equality-case {number ·} (recursive-· evidence) rewrite equality-case {number} evidence = begin
  -- (ℕ→ℕ₂ (ℕ₂→ℕ number × 2) ·) ≡ ℕ→ℕ₂ (ℕ₂→ℕ number × 2 × 2)
  (ℕ→ℕ₂ (ℕ₂→ℕ number × 2) ·) ≡⟨⟩
  -- (ℕ→ℕ₂ (2 × (ℕ₂→ℕ number × 2))) ≡⟨⟩
  {!!}

even-begins-with-· : ∀ n₂ → ends-in-I n₂ → even' (ℕ₂→ℕ n₂) → ∃ (λ x → n₂ ≡ x ·)
even-begins-with-· ((n₂ I) I) canonicity (next-even x₁) = {!!}
even-begins-with-· ((n₂ ·) I) (recursive-I (recursive-· canonicity)) (successor-is-even x₁) = {!!}
even-begins-with-· (n₂ ·) canonicity evenness = n₂ , reflexivity

lemma : ∀ n₂ → ends-in-I n₂ → ℕ→ℕ₂ (ℕ₂→ℕ n₂ × 2) ≡ ℕ→ℕ₂ (ℕ₂→ℕ n₂) ·
lemma ₂ ()
lemma (.₂ I) I-ends-in-I = reflexivity
lemma (n₂ I) (recursive-I evidence) with ℕ₂→ℕ (n₂ I)
... | zero = {!!}
... | successor x₁ = {!!}
lemma (n₂ ·) (recursive-· evidence) = {!!}
-- = begin ℕ→ℕ₂ (n × 2) ≡⟨ ? ⟩ ℕ→ℕ₂ n · ∎

-- lemma : ∀ number → ends-in-I number → (ℕ→ℕ₂ (ℕ₂→ℕ number) ·) ≡ ℕ→ℕ₂ (ℕ₂→ℕ number + ℕ₂→ℕ number)
-- lemma ₂ ()
-- lemma (.₂ I) I-ends-in-I = reflexivity
-- lemma (number I) (recursive-I evidence) = begin
--   successor₂ (ℕ→ℕ₂ (ℕ₂→ℕ number × 2)) · ≡⟨ reflexivity ⟩
--   ℕ→ℕ₂ (successor (ℕ₂→ℕ number × 2)) · ≡⟨ {!!} ⟩
--   successor₂ (ℕ→ℕ₂ (ℕ₂→ℕ number × 2 + successor (ℕ₂→ℕ number × 2))) ∎
-- lemma (number ·) (recursive-· evidence) = {!!}

ℕ→ℕ₂-retracts-ℕ₂→ℕ-if-canonical : ∀ {n₂} → is-canonical n₂ → n₂ ≡ ℕ→ℕ₂ (ℕ₂→ℕ n₂)
ℕ→ℕ₂-retracts-ℕ₂→ℕ-if-canonical {.₂} canonical-zero = reflexivity
ℕ→ℕ₂-retracts-ℕ₂→ℕ-if-canonical {.(₂ I)} (canonical I-ends-in-I) = reflexivity
ℕ→ℕ₂-retracts-ℕ₂→ℕ-if-canonical {number ·} (canonical (recursive-· evidence)) = begin
  number · ≡⟨ congruence (λ e → e ·) (ℕ→ℕ₂-retracts-ℕ₂→ℕ-if-canonical {number} (canonical evidence)) ⟩
  ℕ→ℕ₂ (ℕ₂→ℕ number) · ≡⟨ {!!} ⟩
  ℕ→ℕ₂ (ℕ₂→ℕ number + ℕ₂→ℕ number) ≡⟨ congruence ℕ→ℕ₂ (symmetry (+identity (ℕ₂→ℕ number + ℕ₂→ℕ number))) ⟩
  ℕ→ℕ₂ (ℕ₂→ℕ number + ℕ₂→ℕ number + 0) ≡⟨ congruence ℕ→ℕ₂ (+associative (ℕ₂→ℕ number) (ℕ₂→ℕ number) 0) ⟩
  ℕ→ℕ₂ (ℕ₂→ℕ number + (ℕ₂→ℕ number + 0)) ≡⟨⟩
  ℕ→ℕ₂ (2 × ℕ₂→ℕ number) ≡⟨ congruence ℕ→ℕ₂ (×-is-commutative 2 (ℕ₂→ℕ number)) ⟩
  ℕ→ℕ₂ (ℕ₂→ℕ number × 2) ≡⟨⟩
  ℕ→ℕ₂ (ℕ₂→ℕ (number ·)) ∎
ℕ→ℕ₂-retracts-ℕ₂→ℕ-if-canonical {number I} (canonical (recursive-I evidence)) = {!!}
