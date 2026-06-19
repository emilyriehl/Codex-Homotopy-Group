# Computing the loop space of the circle

```agda
module synthetic-homotopy-theory.computing-loop-space-circle where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.coproduct-types

open import synthetic-homotopy-theory.circle
open import synthetic-homotopy-theory.computing-integer-powers-of-loops
open import synthetic-homotopy-theory.homotopy-groups-circle
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.powers-of-loops
open import synthetic-homotopy-theory.universal-cover-circle
```

</details>

## Idea

The equivalence from the loop space of the circle to the integers is the
universal-cover encoder followed by the inverse of the fiber equivalence. The
transport computation for the universal cover therefore computes what happens
when a loop is concatenated with the generating loop.

## Definitions

### The universal-cover encoder of loops on the circle

```agda
universal-cover-𝕊¹ : 𝕊¹ → UU lzero
universal-cover-𝕊¹ =
  universal-cover-circle free-loop-𝕊¹ dependent-universal-property-𝕊¹

compute-fiber-universal-cover-𝕊¹ :
  ℤ ≃ universal-cover-𝕊¹ base-𝕊¹
compute-fiber-universal-cover-𝕊¹ =
  compute-fiber-universal-cover-circle
    ( free-loop-𝕊¹)
    ( dependent-universal-property-𝕊¹)

point-universal-cover-𝕊¹ : universal-cover-𝕊¹ base-𝕊¹
point-universal-cover-𝕊¹ =
  point-universal-cover-circle
    ( free-loop-𝕊¹)
    ( dependent-universal-property-𝕊¹)

encode-loop-𝕊¹ : type-Ω 𝕊¹-Pointed-Type → universal-cover-𝕊¹ base-𝕊¹
encode-loop-𝕊¹ =
  universal-cover-circle-eq
    ( free-loop-𝕊¹)
    ( dependent-universal-property-𝕊¹)
    ( base-𝕊¹)
```

## Properties

### The encoder is transport in the universal cover

```agda
compute-encode-loop-𝕊¹ :
  (p : type-Ω 𝕊¹-Pointed-Type) →
  encode-loop-𝕊¹ p ＝ tr universal-cover-𝕊¹ p point-universal-cover-𝕊¹
compute-encode-loop-𝕊¹ p =
  compute-map-out-of-identity-type
    ( universal-cover-circle-eq
      ( free-loop-𝕊¹)
      ( dependent-universal-property-𝕊¹))
    ( base-𝕊¹)
    ( p)
```

### The encoder preserves concatenation as iterated transport

```agda
compute-encode-loop-concat-𝕊¹ :
  (p q : type-Ω 𝕊¹-Pointed-Type) →
  encode-loop-𝕊¹ (p ∙ q) ＝ tr universal-cover-𝕊¹ q (encode-loop-𝕊¹ p)
compute-encode-loop-concat-𝕊¹ p q =
  ( compute-encode-loop-𝕊¹ (p ∙ q)) ∙
  ( tr-concat p q point-universal-cover-𝕊¹) ∙
  ( ap (tr universal-cover-𝕊¹ q) (inv (compute-encode-loop-𝕊¹ p)))
```

### Concatenating with the generating loop increments the integer code

```agda
compute-loop-space-𝕊¹-concat-loop-𝕊¹ :
  (p : type-Ω 𝕊¹-Pointed-Type) →
  map-equiv compute-loop-space-𝕊¹ (p ∙ loop-𝕊¹) ＝
  succ-ℤ (map-equiv compute-loop-space-𝕊¹ p)
compute-loop-space-𝕊¹-concat-loop-𝕊¹ p =
  is-injective-equiv
    ( compute-fiber-universal-cover-𝕊¹)
    ( ( is-section-map-inv-equiv
        ( compute-fiber-universal-cover-𝕊¹)
        ( encode-loop-𝕊¹ (p ∙ loop-𝕊¹))) ∙
      ( compute-encode-loop-concat-𝕊¹ p loop-𝕊¹) ∙
      ( ap
        ( tr universal-cover-𝕊¹ loop-𝕊¹)
        ( inv
          ( is-section-map-inv-equiv
            ( compute-fiber-universal-cover-𝕊¹)
            ( encode-loop-𝕊¹ p)))) ∙
      ( inv
        ( compute-tr-universal-cover-circle
          ( free-loop-𝕊¹)
          ( dependent-universal-property-𝕊¹)
          ( map-equiv compute-loop-space-𝕊¹ p))))
```

### Transporting along the inverse generating loop decrements integer codes

```agda
compute-tr-inv-loop-universal-cover-𝕊¹ :
  (k : ℤ) →
  tr universal-cover-𝕊¹
    ( inv loop-𝕊¹)
    ( map-equiv compute-fiber-universal-cover-𝕊¹ k) ＝
  map-equiv compute-fiber-universal-cover-𝕊¹ (pred-ℤ k)
compute-tr-inv-loop-universal-cover-𝕊¹ k =
  eq-transpose-tr
    ( loop-𝕊¹)
    ( ( ap
        ( map-equiv compute-fiber-universal-cover-𝕊¹)
        ( inv (is-section-pred-ℤ k))) ∙
      ( compute-tr-universal-cover-circle
        ( free-loop-𝕊¹)
        ( dependent-universal-property-𝕊¹)
        ( pred-ℤ k)))
```

### Concatenating with the inverse generating loop decrements the integer code

```agda
compute-loop-space-𝕊¹-concat-inv-loop-𝕊¹ :
  (p : type-Ω 𝕊¹-Pointed-Type) →
  map-equiv compute-loop-space-𝕊¹ (p ∙ inv loop-𝕊¹) ＝
  pred-ℤ (map-equiv compute-loop-space-𝕊¹ p)
compute-loop-space-𝕊¹-concat-inv-loop-𝕊¹ p =
  is-injective-equiv
    ( compute-fiber-universal-cover-𝕊¹)
    ( ( is-section-map-inv-equiv
        ( compute-fiber-universal-cover-𝕊¹)
        ( encode-loop-𝕊¹ (p ∙ inv loop-𝕊¹))) ∙
      ( compute-encode-loop-concat-𝕊¹ p (inv loop-𝕊¹)) ∙
      ( ap
        ( tr universal-cover-𝕊¹ (inv loop-𝕊¹))
        ( inv
          ( is-section-map-inv-equiv
            ( compute-fiber-universal-cover-𝕊¹)
            ( encode-loop-𝕊¹ p)))) ∙
      ( compute-tr-inv-loop-universal-cover-𝕊¹
        ( map-equiv compute-loop-space-𝕊¹ p)))
```

### Integer powers of the generating loop compute to their exponents

```agda
compute-power-int-loop-zero-𝕊¹ :
  map-equiv compute-loop-space-𝕊¹
    ( power-int-Ω zero-ℤ 𝕊¹-Pointed-Type loop-𝕊¹) ＝
  zero-ℤ
compute-power-int-loop-zero-𝕊¹ =
  is-retraction-map-inv-equiv compute-fiber-universal-cover-𝕊¹ zero-ℤ

compute-power-int-loop-succ-𝕊¹ :
  (k : ℤ) →
  map-equiv compute-loop-space-𝕊¹
    ( power-int-Ω k 𝕊¹-Pointed-Type loop-𝕊¹) ＝ k →
  map-equiv compute-loop-space-𝕊¹
    ( power-int-Ω (succ-ℤ k) 𝕊¹-Pointed-Type loop-𝕊¹) ＝
  succ-ℤ k
compute-power-int-loop-succ-𝕊¹ k H =
  ( ap
    ( map-equiv compute-loop-space-𝕊¹)
    ( power-int-succ-right-Ω k 𝕊¹-Pointed-Type loop-𝕊¹)) ∙
  ( compute-loop-space-𝕊¹-concat-loop-𝕊¹
    ( power-int-Ω k 𝕊¹-Pointed-Type loop-𝕊¹)) ∙
  ( ap succ-ℤ H)

compute-power-int-loop-pred-𝕊¹ :
  (k : ℤ) →
  map-equiv compute-loop-space-𝕊¹
    ( power-int-Ω k 𝕊¹-Pointed-Type loop-𝕊¹) ＝ k →
  map-equiv compute-loop-space-𝕊¹
    ( power-int-Ω (pred-ℤ k) 𝕊¹-Pointed-Type loop-𝕊¹) ＝
  pred-ℤ k
compute-power-int-loop-pred-𝕊¹ k H =
  ( ap
    ( map-equiv compute-loop-space-𝕊¹)
    ( power-int-pred-right-Ω k 𝕊¹-Pointed-Type loop-𝕊¹)) ∙
  ( compute-loop-space-𝕊¹-concat-inv-loop-𝕊¹
    ( power-int-Ω k 𝕊¹-Pointed-Type loop-𝕊¹)) ∙
  ( ap pred-ℤ H)

compute-power-int-loop-𝕊¹ :
  (k : ℤ) →
  map-equiv compute-loop-space-𝕊¹
    ( power-int-Ω k 𝕊¹-Pointed-Type loop-𝕊¹) ＝ k
compute-power-int-loop-𝕊¹ =
  ind-ℤ
    ( λ k →
      map-equiv compute-loop-space-𝕊¹
        ( power-int-Ω k 𝕊¹-Pointed-Type loop-𝕊¹) ＝ k)
    ( compute-power-int-loop-pred-𝕊¹
      ( zero-ℤ)
      ( compute-power-int-loop-zero-𝕊¹))
    ( λ n → compute-power-int-loop-pred-𝕊¹ (inl n))
    ( compute-power-int-loop-zero-𝕊¹)
    ( compute-power-int-loop-succ-𝕊¹
      ( zero-ℤ)
      ( compute-power-int-loop-zero-𝕊¹))
    ( λ n → compute-power-int-loop-succ-𝕊¹ (inr (inr n)))
```

### Concatenating with integer powers adds the exponent

```agda
compute-loop-space-𝕊¹-concat-power-int-loop-zero-𝕊¹ :
  (p : type-Ω 𝕊¹-Pointed-Type) →
  map-equiv compute-loop-space-𝕊¹
    ( p ∙ power-int-Ω zero-ℤ 𝕊¹-Pointed-Type loop-𝕊¹) ＝
  map-equiv compute-loop-space-𝕊¹ p +ℤ zero-ℤ
compute-loop-space-𝕊¹-concat-power-int-loop-zero-𝕊¹ p =
  ( ap (map-equiv compute-loop-space-𝕊¹) (right-unit {p = p})) ∙
  ( inv (right-unit-law-add-ℤ (map-equiv compute-loop-space-𝕊¹ p)))

compute-loop-space-𝕊¹-concat-power-int-loop-succ-𝕊¹ :
  (p : type-Ω 𝕊¹-Pointed-Type) (k : ℤ) →
  map-equiv compute-loop-space-𝕊¹
    ( p ∙ power-int-Ω k 𝕊¹-Pointed-Type loop-𝕊¹) ＝
  map-equiv compute-loop-space-𝕊¹ p +ℤ k →
  map-equiv compute-loop-space-𝕊¹
    ( p ∙ power-int-Ω (succ-ℤ k) 𝕊¹-Pointed-Type loop-𝕊¹) ＝
  map-equiv compute-loop-space-𝕊¹ p +ℤ succ-ℤ k
compute-loop-space-𝕊¹-concat-power-int-loop-succ-𝕊¹ p k H =
  ( ap
    ( map-equiv compute-loop-space-𝕊¹)
    ( ap
      ( p ∙_)
      ( power-int-succ-right-Ω k 𝕊¹-Pointed-Type loop-𝕊¹))) ∙
  ( ap
    ( map-equiv compute-loop-space-𝕊¹)
    ( inv
      ( assoc
        ( p)
        ( power-int-Ω k 𝕊¹-Pointed-Type loop-𝕊¹)
        ( loop-𝕊¹)))) ∙
  ( compute-loop-space-𝕊¹-concat-loop-𝕊¹
    ( p ∙ power-int-Ω k 𝕊¹-Pointed-Type loop-𝕊¹)) ∙
  ( ap succ-ℤ H) ∙
  ( inv (right-successor-law-add-ℤ (map-equiv compute-loop-space-𝕊¹ p) k))

compute-loop-space-𝕊¹-concat-power-int-loop-pred-𝕊¹ :
  (p : type-Ω 𝕊¹-Pointed-Type) (k : ℤ) →
  map-equiv compute-loop-space-𝕊¹
    ( p ∙ power-int-Ω k 𝕊¹-Pointed-Type loop-𝕊¹) ＝
  map-equiv compute-loop-space-𝕊¹ p +ℤ k →
  map-equiv compute-loop-space-𝕊¹
    ( p ∙ power-int-Ω (pred-ℤ k) 𝕊¹-Pointed-Type loop-𝕊¹) ＝
  map-equiv compute-loop-space-𝕊¹ p +ℤ pred-ℤ k
compute-loop-space-𝕊¹-concat-power-int-loop-pred-𝕊¹ p k H =
  ( ap
    ( map-equiv compute-loop-space-𝕊¹)
    ( ap
      ( p ∙_)
      ( power-int-pred-right-Ω k 𝕊¹-Pointed-Type loop-𝕊¹))) ∙
  ( ap
    ( map-equiv compute-loop-space-𝕊¹)
    ( inv
      ( assoc
        ( p)
        ( power-int-Ω k 𝕊¹-Pointed-Type loop-𝕊¹)
        ( inv loop-𝕊¹)))) ∙
  ( compute-loop-space-𝕊¹-concat-inv-loop-𝕊¹
    ( p ∙ power-int-Ω k 𝕊¹-Pointed-Type loop-𝕊¹)) ∙
  ( ap pred-ℤ H) ∙
  ( inv (right-predecessor-law-add-ℤ (map-equiv compute-loop-space-𝕊¹ p) k))

compute-loop-space-𝕊¹-concat-power-int-loop-𝕊¹ :
  (p : type-Ω 𝕊¹-Pointed-Type) (k : ℤ) →
  map-equiv compute-loop-space-𝕊¹
    ( p ∙ power-int-Ω k 𝕊¹-Pointed-Type loop-𝕊¹) ＝
  map-equiv compute-loop-space-𝕊¹ p +ℤ k
compute-loop-space-𝕊¹-concat-power-int-loop-𝕊¹ p =
  ind-ℤ
    ( λ k →
      map-equiv compute-loop-space-𝕊¹
        ( p ∙ power-int-Ω k 𝕊¹-Pointed-Type loop-𝕊¹) ＝
      map-equiv compute-loop-space-𝕊¹ p +ℤ k)
    ( compute-loop-space-𝕊¹-concat-power-int-loop-pred-𝕊¹
      ( p)
      ( zero-ℤ)
      ( compute-loop-space-𝕊¹-concat-power-int-loop-zero-𝕊¹ p))
    ( λ n → compute-loop-space-𝕊¹-concat-power-int-loop-pred-𝕊¹ p (inl n))
    ( compute-loop-space-𝕊¹-concat-power-int-loop-zero-𝕊¹ p)
    ( compute-loop-space-𝕊¹-concat-power-int-loop-succ-𝕊¹
      ( p)
      ( zero-ℤ)
      ( compute-loop-space-𝕊¹-concat-power-int-loop-zero-𝕊¹ p))
    ( λ n →
      compute-loop-space-𝕊¹-concat-power-int-loop-succ-𝕊¹ p (inr (inr n)))
```

### The loop-space computation preserves loop concatenation

```agda
eq-power-int-loop-compute-loop-space-𝕊¹ :
  (p : type-Ω 𝕊¹-Pointed-Type) →
  power-int-Ω
    ( map-equiv compute-loop-space-𝕊¹ p)
    ( 𝕊¹-Pointed-Type)
    ( loop-𝕊¹) ＝ p
eq-power-int-loop-compute-loop-space-𝕊¹ p =
  is-injective-equiv
    ( compute-loop-space-𝕊¹)
    ( compute-power-int-loop-𝕊¹ (map-equiv compute-loop-space-𝕊¹ p))

preserves-mul-compute-loop-space-𝕊¹ :
  (p q : type-Ω 𝕊¹-Pointed-Type) →
  map-equiv compute-loop-space-𝕊¹ (p ∙ q) ＝
  map-equiv compute-loop-space-𝕊¹ p +ℤ map-equiv compute-loop-space-𝕊¹ q
preserves-mul-compute-loop-space-𝕊¹ p q =
  ( ap
    ( map-equiv compute-loop-space-𝕊¹)
    ( ap (p ∙_) (inv (eq-power-int-loop-compute-loop-space-𝕊¹ q)))) ∙
  ( compute-loop-space-𝕊¹-concat-power-int-loop-𝕊¹
    ( p)
    ( map-equiv compute-loop-space-𝕊¹ q))
```
