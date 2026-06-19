# Computing integer powers of loops

```agda
module synthetic-homotopy-theory.computing-integer-powers-of-loops where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.iterating-automorphisms
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.powers-of-loops
```

</details>

## Idea

Integer powers of a loop are defined by iterating the automorphism that appends
the loop. The general iteration lemmas for automorphisms therefore give the
basic successor and addition computations for integer loop powers.

## Properties

### The inverse map of right concatenation appends the inverse

```agda
compute-map-inv-equiv-concat' :
  {l : Level} {A : UU l} (x : A) {y z : A} (q : y ＝ z)
  (r : x ＝ z) →
  map-inv-equiv (equiv-concat' x q) r ＝ r ∙ inv q
compute-map-inv-equiv-concat' x q =
  htpy-map-inv-equiv-section
    ( equiv-concat' x q)
    ( pair (inv-concat' x q) (is-section-inv-concat' q))
```

### Successor powers append one loop on the right

```agda
power-int-succ-right-Ω :
  {l : Level} (k : ℤ) (A : Pointed-Type l) (ω : type-Ω A) →
  power-int-Ω (succ-ℤ k) A ω ＝ power-int-Ω k A ω ∙ ω
power-int-succ-right-Ω k A ω =
  iterate-automorphism-succ-ℤ'
    ( k)
    ( equiv-concat' (point-Pointed-Type A) ω)
    ( refl)
```

### Predecessor powers append one inverse loop on the right

```agda
power-int-pred-right-Ω :
  {l : Level} (k : ℤ) (A : Pointed-Type l) (ω : type-Ω A) →
  power-int-Ω (pred-ℤ k) A ω ＝ power-int-Ω k A ω ∙ inv ω
power-int-pred-right-Ω k A ω =
  ( iterate-automorphism-pred-ℤ'
    ( k)
    ( equiv-concat' (point-Pointed-Type A) ω)
    ( refl)) ∙
  ( compute-map-inv-equiv-concat'
    ( point-Pointed-Type A)
    ( ω)
    ( power-int-Ω k A ω))
```

### Addition of exponents computes by iterated concatenation

```agda
compute-power-int-add-Ω :
  {l : Level} (k l' : ℤ) (A : Pointed-Type l) (ω : type-Ω A) →
  power-int-Ω (k +ℤ l') A ω ＝
  map-equiv (equiv-power-int-Ω k A ω) (power-int-Ω l' A ω)
compute-power-int-add-Ω k l' A ω =
  iterate-automorphism-add-ℤ
    ( k)
    ( l')
    ( equiv-concat' (point-Pointed-Type A) ω)
    ( refl)
```
