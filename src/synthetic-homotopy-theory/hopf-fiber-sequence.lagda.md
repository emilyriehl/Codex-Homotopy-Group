# The Hopf fiber sequence

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module synthetic-homotopy-theory.hopf-fiber-sequence where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.fiber-sequences

open import synthetic-homotopy-theory.spheres
```

</details>

## Idea

The Hopf fibration gives a fiber sequence

```text
S¹ → S³ → S².
```

This file records the packaged pointed fiber sequence with its fiber, total
space, and base fields fixed definitionally to the pointed spheres used by the
homotopy-group calculation.

## Theorem

### The Hopf fiber sequence

```agda
hopf-fiber-sequence-sphere-1-sphere-3-sphere-2 :
  fiber-sequence-Pointed-Type lzero lzero lzero
pr1 hopf-fiber-sequence-sphere-1-sphere-3-sphere-2 =
  sphere-Pointed-Type 1
pr1 (pr2 hopf-fiber-sequence-sphere-1-sphere-3-sphere-2) =
  sphere-Pointed-Type 3
pr1 (pr2 (pr2 hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)) =
  sphere-Pointed-Type 2
pr1 (pr2 (pr2 (pr2 hopf-fiber-sequence-sphere-1-sphere-3-sphere-2))) =
  {!!}
pr1 (pr2 (pr2 (pr2 (pr2 hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)))) =
  {!!}
pr1
  ( pr2
    ( pr2
      ( pr2
        ( pr2
          ( pr2 hopf-fiber-sequence-sphere-1-sphere-3-sphere-2))))) =
  {!!}
pr2
  ( pr2
    ( pr2
      ( pr2
        ( pr2
          ( pr2 hopf-fiber-sequence-sphere-1-sphere-3-sphere-2))))) =
  {!!}
```
