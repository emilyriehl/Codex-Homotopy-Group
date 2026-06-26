# Set-truncated iterated exactness of homotopy groups of fiber sequences

```agda
module synthetic-homotopy-theory.set-truncated-iterated-exactness-homotopy-groups-fiber-sequences where

open import synthetic-homotopy-theory.set-truncated-canonical-iterated-exactness-homotopy-groups-fiber-sequences public
open import synthetic-homotopy-theory.signed-boundary-comparisons-fiber-sequences public
open import synthetic-homotopy-theory.set-truncated-iterated-maps-homotopy-groups-fiber-sequences public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-set-truncation
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import structured-types.exact-sequences-pointed-sets
open import structured-types.fiber-sequences
open import structured-types.fibers-of-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.cavallos-trick
open import synthetic-homotopy-theory.connecting-fiber-sequences
open import synthetic-homotopy-theory.fibers-boundary-maps-pointed-maps
open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.iterated-boundary-maps-fiber-sequences
open import synthetic-homotopy-theory.iterated-loop-fiber-sequences
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces-fibers-of-pointed-maps
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.reassociation-iterated-loop-spaces
open import synthetic-homotopy-theory.set-truncated-exactness-homotopy-groups-fiber-sequences
```

</details>

## Idea

The group-level long exact sequence of homotopy groups needs exactness after
applying set truncation to the loop spaces of iterated loop spaces. This file
records that set-level iterated exactness separately from the later transport to
ordinary group exactness.

The set-truncated maps themselves are defined in
[`set-truncated-iterated-maps-homotopy-groups-fiber-sequences`](synthetic-homotopy-theory.set-truncated-iterated-maps-homotopy-groups-fiber-sequences.md).

The signed boundary comparison machinery is defined in
[`signed-boundary-comparisons-fiber-sequences`](synthetic-homotopy-theory.signed-boundary-comparisons-fiber-sequences.md).

For a fiber sequence `F ->* E ->* B`, the first target says that the maps

```text
  Ω Ω^n F ->* Ω Ω^n E ->* Ω Ω^n B
```

are exact after set truncation. The second checked target says that the maps

```text
  Ω Ω^(n+1) E ->* Ω Ω^(n+1) B ->* Ω Ω^n F
```

are exact after set truncation when the final map is the canonical shifted
boundary map of the iterated loop fiber sequence. The recursive looped
boundary map is retained separately because it is the map classifying the
concrete homotopy-group homomorphism. The shifted connecting fiber sequence is
provided structurally by
[`connecting-fiber-sequences`](synthetic-homotopy-theory.connecting-fiber-sequences.md);
the older `direct` names below are compatibility aliases for that structural
route. Reassociation identifies the natural `Ω^n(Ω X)` indexing with the public
shifted `Ω^(n+1) X` indexing.

## Theorems

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  is-exact-set-truncation-iterated-loop-connecting-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( Ω (total-space-fiber-sequence-Pointed-Type S)))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( Ω (base-fiber-sequence-Pointed-Type S)))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-connecting-fibration-fiber-sequence S n)
      ( hom-trunc-iterated-loop-connecting-map-fiber-sequence S n)
  is-exact-set-truncation-iterated-loop-connecting-fiber-sequence
    zero-ℕ =
    is-exact-set-truncation-loop-fiber-sequence
      ( fiber-sequence-connecting-map-fiber-sequence-Pointed-Type S)
  is-exact-set-truncation-iterated-loop-connecting-fiber-sequence
    ( succ-ℕ n) =
    is-exact-set-truncation-loop-fiber-sequence
      ( iterated-loop-fiber-sequence
        ( fiber-sequence-connecting-map-fiber-sequence-Pointed-Type S)
        ( succ-ℕ n))

  is-exact-set-truncation-direct-iterated-loop-fibration-boundary-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( Ω (total-space-fiber-sequence-Pointed-Type S)))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( Ω (base-fiber-sequence-Pointed-Type S)))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-direct-iterated-loop-fibration-fiber-sequence S n)
      ( hom-trunc-direct-iterated-loop-boundary-fiber-sequence S n)
  is-exact-set-truncation-direct-iterated-loop-fibration-boundary-fiber-sequence =
    is-exact-set-truncation-iterated-loop-connecting-fiber-sequence

  eq-tr-hom-trunc-reassociate-iterated-loop-fibration-fiber-sequence :
    (n : ℕ) →
    tr
      (λ X →
        hom-Pointed-Set X
          ( trunc-Pointed-Set
            ( Ω
              ( iterated-loop-space
                ( n)
                ( Ω (base-fiber-sequence-Pointed-Type S))))))
      ( ap
        ( trunc-Pointed-Set)
        ( reassociate-Ω-succ-iterated-loop-space
          ( n)
          ( total-space-fiber-sequence-Pointed-Type S)))
      ( tr
        (λ Y →
          hom-Pointed-Set
            ( trunc-Pointed-Set
              ( Ω
                ( iterated-loop-space
                  ( succ-ℕ n)
                  ( total-space-fiber-sequence-Pointed-Type S))))
            ( Y))
        ( ap
          ( trunc-Pointed-Set)
          ( reassociate-Ω-succ-iterated-loop-space
            ( n)
            ( base-fiber-sequence-Pointed-Type S)))
        ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))) ＝
    hom-trunc-direct-iterated-loop-fibration-fiber-sequence S n
  eq-tr-hom-trunc-reassociate-iterated-loop-fibration-fiber-sequence n =
    tr-hom-trunc-Pointed-Set
      ( reassociate-Ω-succ-iterated-loop-space
        ( n)
        ( total-space-fiber-sequence-Pointed-Type S))
      ( reassociate-Ω-succ-iterated-loop-space
        ( n)
        ( base-fiber-sequence-Pointed-Type S))
      ( pointed-map-Ω
        ( pointed-map-iterated-loop-space
          ( succ-ℕ n)
          ( fibration-fiber-sequence-Pointed-Type S))) ∙
    ap
      ( hom-trunc-Pointed-Set)
      ( reassociate-Ω-pointed-map-iterated-loop-space
        ( n)
        ( fibration-fiber-sequence-Pointed-Type S))

  eq-tr-hom-trunc-reassociate-iterated-loop-boundary-fiber-sequence :
    (n : ℕ) →
    tr
      (λ X →
        hom-Pointed-Set X
          ( trunc-Pointed-Set
            ( Ω
              ( iterated-loop-space
                ( n)
                ( fiber-fiber-sequence-Pointed-Type S)))))
      ( ap
        ( trunc-Pointed-Set)
        ( reassociate-Ω-succ-iterated-loop-space
          ( n)
          ( base-fiber-sequence-Pointed-Type S)))
      ( tr
        (λ Y →
          hom-Pointed-Set
            ( trunc-Pointed-Set
              ( Ω
                ( iterated-loop-space
                  ( succ-ℕ n)
                  ( base-fiber-sequence-Pointed-Type S))))
            ( Y))
        ( refl
          { x =
            trunc-Pointed-Set
              ( Ω
                ( iterated-loop-space
                  ( n)
                  ( fiber-fiber-sequence-Pointed-Type S)))})
        ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)) ＝
    hom-trunc-direct-iterated-loop-boundary-fiber-sequence S n
  eq-tr-hom-trunc-reassociate-iterated-loop-boundary-fiber-sequence n =
    tr-hom-trunc-Pointed-Set
      ( reassociate-Ω-succ-iterated-loop-space
        ( n)
        ( base-fiber-sequence-Pointed-Type S))
      ( refl
        { x =
          Ω
            ( iterated-loop-space
              ( n)
              ( fiber-fiber-sequence-Pointed-Type S))})
      ( pointed-map-Ω (pointed-map-iterated-boundary-fiber-sequence S n)) ∙
    ap
      ( hom-trunc-Pointed-Set)
      ( reassociate-Ω-pointed-map-iterated-boundary-fiber-sequence S n)

  is-exact-set-truncation-iterated-loop-fibration-connecting-map-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
          ( fiber-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)
  is-exact-set-truncation-iterated-loop-fibration-connecting-map-fiber-sequence n =
    is-exact-hom-Pointed-Set-tr
      ( ap
        ( trunc-Pointed-Set)
        ( reassociate-Ω-succ-iterated-loop-space
          ( n)
          ( total-space-fiber-sequence-Pointed-Type S)))
      ( ap
        ( trunc-Pointed-Set)
        ( reassociate-Ω-succ-iterated-loop-space
          ( n)
          ( base-fiber-sequence-Pointed-Type S)))
      ( refl
        { x =
          trunc-Pointed-Set
            ( Ω
              ( iterated-loop-space
                ( n)
                ( fiber-fiber-sequence-Pointed-Type S)))})
      ( hom-trunc-direct-iterated-loop-fibration-fiber-sequence S n)
      ( hom-trunc-direct-iterated-loop-boundary-fiber-sequence S n)
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)
      ( eq-tr-hom-trunc-reassociate-iterated-loop-fibration-fiber-sequence n)
      ( eq-tr-hom-trunc-reassociate-iterated-loop-boundary-fiber-sequence n)
      ( is-exact-set-truncation-direct-iterated-loop-fibration-boundary-fiber-sequence n)

  is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-direct :
    (n : ℕ) →
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)
  is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-direct =
    is-exact-set-truncation-iterated-loop-fibration-connecting-map-fiber-sequence

  is-exact-set-truncation-first-iterated-loop-fibration-boundary-fiber-sequence-direct :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( 1)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( 1)
            ( base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( 0)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S 1)
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S 0)
  is-exact-set-truncation-first-iterated-loop-fibration-boundary-fiber-sequence-direct =
    is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-direct
      ( 0)

  is-exact-set-truncation-second-iterated-loop-fibration-boundary-fiber-sequence-direct :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( 2)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( 2)
            ( base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( 1)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S 2)
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S 1)
  is-exact-set-truncation-second-iterated-loop-fibration-boundary-fiber-sequence-direct =
    is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-direct
      ( 1)

  is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-kernel :
    (n : ℕ) →
    ((x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω
            ( iterated-loop-space
              ( succ-ℕ n)
              ( base-fiber-sequence-Pointed-Type S))))) →
      is-in-kernel-hom-Pointed-Set
        { A =
          trunc-Pointed-Set
            ( Ω
              ( iterated-loop-space
                ( succ-ℕ n)
                ( base-fiber-sequence-Pointed-Type S)))}
        { B =
          trunc-Pointed-Set
            ( Ω
              ( iterated-loop-space
                ( n)
                ( fiber-fiber-sequence-Pointed-Type S)))}
        ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)
        ( x) ↔
      is-in-kernel-hom-Pointed-Set
        { A =
          trunc-Pointed-Set
            ( Ω
              ( iterated-loop-space
                ( succ-ℕ n)
                ( base-fiber-sequence-Pointed-Type S)))}
        { B =
          trunc-Pointed-Set
            ( Ω
              ( iterated-loop-space
                ( n)
                ( fiber-fiber-sequence-Pointed-Type S)))}
        ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence S n)
        ( x)) →
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)
  is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-kernel
    n K =
    is-exact-hom-Pointed-Set-iff-kernel-right
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence S n)
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)
      ( K)
      ( is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence
        S
        ( n))

  is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence :
    (n : ℕ) →
    ((x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω
            ( iterated-loop-space
              ( succ-ℕ n)
              ( base-fiber-sequence-Pointed-Type S))))) →
      map-pointed-map (hom-trunc-iterated-loop-boundary-fiber-sequence S n) x ＝
      map-pointed-map
        ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence S n)
        ( x)) →
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)
  is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence n H =
    is-exact-hom-Pointed-Set-htpy-right
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence S n)
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)
      ( H)
      ( is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence
        S
        ( n))

  is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-pointed-htpy :
    (n : ℕ) →
    ( pointed-map-Ω (pointed-map-iterated-boundary-fiber-sequence S n)) ~∗
    ( boundary-pointed-map-fiber-sequence
      ( iterated-loop-fiber-sequence S (succ-ℕ n))) →
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)
  is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-pointed-htpy
    n H =
    is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence
      ( n)
      ( htpy-hom-trunc-Pointed-Set
        { f = pointed-map-Ω (pointed-map-iterated-boundary-fiber-sequence S n)}
        { g =
          boundary-pointed-map-fiber-sequence
            ( iterated-loop-fiber-sequence S (succ-ℕ n))}
        ( htpy-pointed-htpy H))
```
