# Iterated loop fiber sequences of fiber sequences

```agda
module synthetic-homotopy-theory.iterated-loop-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.fiber-sequences
open import structured-types.fibers-of-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.whiskering-pointed-homotopies-composition

open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces-fibers-of-pointed-maps
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

A [fiber sequence](structured-types.fiber-sequences.md)

```text
  F →∗ E →∗ B
```

can be looped any finite number of times. The **iterated loop fiber sequence**
keeps track of the canonical comparison between `Ω^n F` and the fiber of the
iterated loop map `Ω^n E →∗ Ω^n B`, together with the compatibility of the
iterated fiber inclusion.

## Definitions

### Iterated loop fiber sequences

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  pointed-equiv-iterated-loop-fiber-fiber-sequence :
    (n : ℕ) →
    iterated-loop-space n (fiber-fiber-sequence-Pointed-Type S) ≃∗
    fiber-Pointed-Type
      ( pointed-map-iterated-loop-space n
        ( fibration-fiber-sequence-Pointed-Type S))
  pointed-equiv-iterated-loop-fiber-fiber-sequence zero-ℕ =
    pointed-equiv-fiber-fiber-sequence-Pointed-Type S
  pointed-equiv-iterated-loop-fiber-fiber-sequence (succ-ℕ n) =
    comp-pointed-equiv
      ( pointed-equiv-loop-fiber-Pointed-Type
        ( pointed-map-iterated-loop-space n
          ( fibration-fiber-sequence-Pointed-Type S)))
      ( pointed-equiv-Ω-pointed-equiv
        ( pointed-equiv-iterated-loop-fiber-fiber-sequence n))

  pointed-htpy-iterated-loop-fiber-inclusion-fiber-sequence :
    (n : ℕ) →
    pointed-map-iterated-loop-space n
      ( fiber-inclusion-fiber-sequence-Pointed-Type S) ~∗
    ( inclusion-fiber-Pointed-Type
      ( pointed-map-iterated-loop-space n
        ( fibration-fiber-sequence-Pointed-Type S)) ∘∗
      pointed-map-pointed-equiv
        ( pointed-equiv-iterated-loop-fiber-fiber-sequence n))
  pointed-htpy-iterated-loop-fiber-inclusion-fiber-sequence zero-ℕ =
    pointed-htpy-fiber-inclusion-fiber-sequence-Pointed-Type S
  pointed-htpy-iterated-loop-fiber-inclusion-fiber-sequence (succ-ℕ n) =
    concat-pointed-htpy
      ( pointed-htpy-Ω
        ( pointed-map-iterated-loop-space n
          ( fiber-inclusion-fiber-sequence-Pointed-Type S))
        ( inclusion-fiber-Pointed-Type
          ( pointed-map-iterated-loop-space n
            ( fibration-fiber-sequence-Pointed-Type S)) ∘∗
          pointed-map-pointed-equiv
            ( pointed-equiv-iterated-loop-fiber-fiber-sequence n))
        ( pointed-htpy-iterated-loop-fiber-inclusion-fiber-sequence n))
      ( concat-pointed-htpy
        ( preserves-comp-pointed-map-Ω
          ( inclusion-fiber-Pointed-Type
            ( pointed-map-iterated-loop-space n
              ( fibration-fiber-sequence-Pointed-Type S)))
          ( pointed-map-pointed-equiv
            ( pointed-equiv-iterated-loop-fiber-fiber-sequence n)))
        ( concat-pointed-htpy
          ( right-whisker-comp-pointed-htpy
            ( pointed-map-Ω
              ( inclusion-fiber-Pointed-Type
                ( pointed-map-iterated-loop-space n
                  ( fibration-fiber-sequence-Pointed-Type S))))
            ( inclusion-fiber-Pointed-Type
              ( pointed-map-Ω
                ( pointed-map-iterated-loop-space n
                  ( fibration-fiber-sequence-Pointed-Type S))) ∘∗
              pointed-map-pointed-equiv
                ( pointed-equiv-loop-fiber-Pointed-Type
                  ( pointed-map-iterated-loop-space n
                    ( fibration-fiber-sequence-Pointed-Type S))))
            ( pointed-htpy-loop-fiber-inclusion-Pointed-Type
              ( pointed-map-iterated-loop-space n
                ( fibration-fiber-sequence-Pointed-Type S)))
            ( pointed-map-Ω
              ( pointed-map-pointed-equiv
                ( pointed-equiv-iterated-loop-fiber-fiber-sequence n))))
          ( associative-comp-pointed-map
            ( inclusion-fiber-Pointed-Type
              ( pointed-map-Ω
                ( pointed-map-iterated-loop-space n
                  ( fibration-fiber-sequence-Pointed-Type S))))
            ( pointed-map-pointed-equiv
              ( pointed-equiv-loop-fiber-Pointed-Type
                ( pointed-map-iterated-loop-space n
                  ( fibration-fiber-sequence-Pointed-Type S))))
            ( pointed-map-Ω
              ( pointed-map-pointed-equiv
                ( pointed-equiv-iterated-loop-fiber-fiber-sequence n))))))

  iterated-loop-fiber-sequence :
    (n : ℕ) → fiber-sequence-Pointed-Type l1 l2 l3
  pr1 (iterated-loop-fiber-sequence n) =
    iterated-loop-space n (fiber-fiber-sequence-Pointed-Type S)
  pr1 (pr2 (iterated-loop-fiber-sequence n)) =
    iterated-loop-space n (total-space-fiber-sequence-Pointed-Type S)
  pr1 (pr2 (pr2 (iterated-loop-fiber-sequence n))) =
    iterated-loop-space n (base-fiber-sequence-Pointed-Type S)
  pr1 (pr2 (pr2 (pr2 (iterated-loop-fiber-sequence n)))) =
    pointed-map-iterated-loop-space n
      ( fiber-inclusion-fiber-sequence-Pointed-Type S)
  pr1 (pr2 (pr2 (pr2 (pr2 (iterated-loop-fiber-sequence n))))) =
    pointed-map-iterated-loop-space n
      ( fibration-fiber-sequence-Pointed-Type S)
  pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (iterated-loop-fiber-sequence n)))))) =
    pointed-equiv-iterated-loop-fiber-fiber-sequence n
  pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (iterated-loop-fiber-sequence n)))))) =
    pointed-htpy-iterated-loop-fiber-inclusion-fiber-sequence n
```
