# Pointed-set tail of the long exact sequence of homotopy groups

```agda
module synthetic-homotopy-theory.pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import foundation.set-truncations
open import foundation.universe-levels

open import structured-types.exact-sequences-pointed-sets
open import structured-types.fiber-sequences

open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.set-truncated-exactness-homotopy-groups-fiber-sequences
```

</details>

## Idea

The low-degree tail of the long exact sequence is naturally a sequence of
pointed sets. For a fiber sequence `F -> E -> B`, this package records

```text
  ||ΩE||₀ -> ||ΩB||₀ -> ||F||₀ -> ||E||₀ -> ||B||₀
```

with exactness at `||ΩB||₀`, `||F||₀`, and `||E||₀`. There is no terminal
exactness assertion at `||B||₀`; such a statement would assert surjectivity of
`||E||₀ -> ||B||₀`, which does not hold for arbitrary fiber sequences.

## Definitions

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  record Pointed-Set-Tail-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence :
    UU (l1 ⊔ l2 ⊔ l3)
    where
    constructor
      make-Pointed-Set-Tail-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence
    field
      hom-loop-fibration-pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequence :
        hom-Pointed-Set
          ( trunc-Pointed-Set (Ω (total-space-fiber-sequence-Pointed-Type S)))
          ( trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S)))
      hom-boundary-pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequence :
        hom-Pointed-Set
          ( trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S)))
          ( trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))
      hom-fiber-inclusion-pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequence :
        hom-Pointed-Set
          ( trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))
          ( trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S))
      hom-fibration-pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequence :
        hom-Pointed-Set
          ( trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S))
          ( trunc-Pointed-Set (base-fiber-sequence-Pointed-Type S))
      is-exact-loop-fibration-boundary-pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequence :
        is-exact-hom-Pointed-Set
          ( trunc-Pointed-Set (Ω (total-space-fiber-sequence-Pointed-Type S)))
          ( trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S)))
          ( trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))
          ( hom-loop-fibration-pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequence)
          ( hom-boundary-pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequence)
      is-exact-boundary-fiber-inclusion-pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequence :
        is-exact-hom-Pointed-Set
          ( trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S)))
          ( trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))
          ( trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S))
          ( hom-boundary-pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequence)
          ( hom-fiber-inclusion-pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequence)
      is-exact-fiber-inclusion-fibration-pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequence :
        is-exact-hom-Pointed-Set
          ( trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))
          ( trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S))
          ( trunc-Pointed-Set (base-fiber-sequence-Pointed-Type S))
          ( hom-fiber-inclusion-pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequence)
          ( hom-fibration-pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequence)

  open Pointed-Set-Tail-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence
    public

  pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequence :
    Pointed-Set-Tail-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence
  pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequence =
    make-Pointed-Set-Tail-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence
      ( hom-trunc-loop-fibration-fiber-sequence-Pointed-Type S)
      ( hom-trunc-boundary-fiber-sequence-Pointed-Type S)
      ( hom-trunc-fiber-inclusion-fiber-sequence-Pointed-Type S)
      ( hom-trunc-fibration-fiber-sequence-Pointed-Type S)
      ( is-exact-set-truncation-loop-boundary-fiber-sequence S)
      ( is-exact-set-truncation-boundary-fiber-sequence S)
      ( is-exact-set-truncation-fiber-sequence S)
```
