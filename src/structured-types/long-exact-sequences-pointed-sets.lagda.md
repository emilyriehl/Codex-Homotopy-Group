# Long exact sequences of pointed sets

```agda
module structured-types.long-exact-sequences-pointed-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import structured-types.exact-sequences-pointed-sets
open import structured-types.pointed-sets
```

</details>

## Idea

A **long exact sequence of pointed sets** is a three-periodic family of pointed
sets and pointed maps

```text
  ... -> B(n+1) -> F(n) -> E(n) -> B(n) -> ...
```

equipped with exactness at the fiber, total-space, and base terms. This is the
pointed-set display layer used by the long exact sequence of homotopy groups of
a fiber sequence.

## Definition

```agda
record Long-Exact-Sequence-Pointed-Set
  (l1 l2 l3 : Level) :
  UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  where
  constructor make-Long-Exact-Sequence-Pointed-Set
  field
    fiber-Pointed-Set-Long-Exact-Sequence :
      ℕ → Pointed-Set l1
    total-space-Pointed-Set-Long-Exact-Sequence :
      ℕ → Pointed-Set l2
    base-Pointed-Set-Long-Exact-Sequence :
      ℕ → Pointed-Set l3
    hom-fiber-inclusion-Long-Exact-Sequence-Pointed-Set :
      (n : ℕ) →
      hom-Pointed-Set
        ( fiber-Pointed-Set-Long-Exact-Sequence n)
        ( total-space-Pointed-Set-Long-Exact-Sequence n)
    hom-fibration-Long-Exact-Sequence-Pointed-Set :
      (n : ℕ) →
      hom-Pointed-Set
        ( total-space-Pointed-Set-Long-Exact-Sequence n)
        ( base-Pointed-Set-Long-Exact-Sequence n)
    hom-boundary-Long-Exact-Sequence-Pointed-Set :
      (n : ℕ) →
      hom-Pointed-Set
        ( base-Pointed-Set-Long-Exact-Sequence (succ-ℕ n))
        ( fiber-Pointed-Set-Long-Exact-Sequence n)
    is-exact-at-total-space-Long-Exact-Sequence-Pointed-Set :
      (n : ℕ) →
      is-exact-hom-Pointed-Set
        ( fiber-Pointed-Set-Long-Exact-Sequence n)
        ( total-space-Pointed-Set-Long-Exact-Sequence n)
        ( base-Pointed-Set-Long-Exact-Sequence n)
        ( hom-fiber-inclusion-Long-Exact-Sequence-Pointed-Set n)
        ( hom-fibration-Long-Exact-Sequence-Pointed-Set n)
    is-exact-at-base-Long-Exact-Sequence-Pointed-Set :
      (n : ℕ) →
      is-exact-hom-Pointed-Set
        ( total-space-Pointed-Set-Long-Exact-Sequence (succ-ℕ n))
        ( base-Pointed-Set-Long-Exact-Sequence (succ-ℕ n))
        ( fiber-Pointed-Set-Long-Exact-Sequence n)
        ( hom-fibration-Long-Exact-Sequence-Pointed-Set (succ-ℕ n))
        ( hom-boundary-Long-Exact-Sequence-Pointed-Set n)
    is-exact-at-fiber-Long-Exact-Sequence-Pointed-Set :
      (n : ℕ) →
      is-exact-hom-Pointed-Set
        ( base-Pointed-Set-Long-Exact-Sequence (succ-ℕ n))
        ( fiber-Pointed-Set-Long-Exact-Sequence n)
        ( total-space-Pointed-Set-Long-Exact-Sequence n)
        ( hom-boundary-Long-Exact-Sequence-Pointed-Set n)
        ( hom-fiber-inclusion-Long-Exact-Sequence-Pointed-Set n)

open Long-Exact-Sequence-Pointed-Set public
```
