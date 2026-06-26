# Set-truncated iterated exactness of homotopy groups of fiber sequences

```agda
module synthetic-homotopy-theory.set-truncated-iterated-exactness-homotopy-groups-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import structured-types.exact-sequences-pointed-sets
open import structured-types.fiber-sequences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.long-exact-sequence-homotopy-groups
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.reassociation-iterated-loop-spaces
```

</details>

## Idea

The group-level long exact sequence of homotopy groups needs exactness after
applying set truncation to the loop spaces of iterated loop spaces. This file
records that set-level iterated exactness separately from the later transport to
ordinary group exactness.

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
concrete homotopy-group homomorphism. The direct shifted connecting fiber
sequence gives checked recursive exactness for all iterates in its natural
`Ω^n(Ω X)` indexing; its first two instances reduce definitionally to the
public shifted indexing needed for the Hopf `π₃(S²)` computation. The fully
arbitrary-index public theorem still needs a functorial reassociation comparison
between `Ω^n(Ω X)` and `Ω^(n+1) X`, including the induced maps.

## Definitions

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  hom-trunc-iterated-loop-fiber-inclusion-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( total-space-fiber-sequence-Pointed-Type S))))
  hom-trunc-iterated-loop-fiber-inclusion-fiber-sequence n =
    hom-trunc-Pointed-Set
      ( pointed-map-Ω
        ( pointed-map-iterated-loop-space
          ( n)
          ( fiber-inclusion-fiber-sequence-Pointed-Type S)))

  hom-trunc-iterated-loop-fibration-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( base-fiber-sequence-Pointed-Type S))))
  hom-trunc-iterated-loop-fibration-fiber-sequence n =
    hom-trunc-Pointed-Set
      ( pointed-map-Ω
        ( pointed-map-iterated-loop-space
          ( n)
          ( fibration-fiber-sequence-Pointed-Type S)))

  hom-trunc-iterated-loop-boundary-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
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
  hom-trunc-iterated-loop-boundary-fiber-sequence n =
    hom-trunc-Pointed-Set
      ( pointed-map-Ω (pointed-map-iterated-boundary-fiber-sequence S n))

  hom-trunc-canonical-iterated-loop-boundary-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
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
  hom-trunc-canonical-iterated-loop-boundary-fiber-sequence n =
    hom-trunc-boundary-fiber-sequence-Pointed-Type
      ( iterated-loop-fiber-sequence S (succ-ℕ n))

  hom-trunc-direct-iterated-loop-fibration-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
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
  hom-trunc-direct-iterated-loop-fibration-fiber-sequence n =
    hom-trunc-Pointed-Set
      ( pointed-map-Ω
        ( pointed-map-iterated-loop-space
          ( n)
          ( pointed-map-Ω (fibration-fiber-sequence-Pointed-Type S))))

  hom-trunc-direct-iterated-loop-boundary-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
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
  hom-trunc-direct-iterated-loop-boundary-fiber-sequence n =
    hom-trunc-Pointed-Set
      ( pointed-map-Ω
        ( pointed-map-iterated-loop-space
          ( n)
          ( boundary-pointed-map-fiber-sequence S)))
```

## Theorems

```agda
  is-exact-set-truncation-iterated-loop-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( base-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-fiber-inclusion-fiber-sequence n)
      ( hom-trunc-iterated-loop-fibration-fiber-sequence n)
  is-exact-set-truncation-iterated-loop-fiber-sequence zero-ℕ =
    is-exact-set-truncation-loop-fiber-sequence S
  is-exact-set-truncation-iterated-loop-fiber-sequence (succ-ℕ n) =
    is-exact-set-truncation-loop-fiber-sequence
      ( iterated-loop-fiber-sequence S (succ-ℕ n))

  hom-trunc-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
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
  hom-trunc-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence
    n =
    hom-trunc-loop-boundary-fiber-sequence-Pointed-Type
      ( iterated-loop-fiber-sequence S n)

  is-exact-set-truncation-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Pointed-Set
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
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence
        n)
      ( hom-trunc-iterated-loop-fiber-inclusion-fiber-sequence n)
  is-exact-set-truncation-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence
    n =
    is-exact-set-truncation-loop-boundary-fiber-inclusion-fiber-sequence
      ( iterated-loop-fiber-sequence S n)

  is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence :
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
      ( hom-trunc-iterated-loop-fibration-fiber-sequence (succ-ℕ n))
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence n)
  is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence n =
    is-exact-set-truncation-loop-boundary-fiber-sequence
      ( iterated-loop-fiber-sequence S (succ-ℕ n))

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
      ( hom-trunc-direct-iterated-loop-fibration-fiber-sequence n)
      ( hom-trunc-direct-iterated-loop-boundary-fiber-sequence n)
  is-exact-set-truncation-direct-iterated-loop-fibration-boundary-fiber-sequence
    zero-ℕ =
    is-exact-set-truncation-loop-fiber-sequence
      ( fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type S)
  is-exact-set-truncation-direct-iterated-loop-fibration-boundary-fiber-sequence
    ( succ-ℕ n) =
    is-exact-set-truncation-loop-fiber-sequence
      ( iterated-loop-fiber-sequence
        ( fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type S)
        ( succ-ℕ n))

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
        ( hom-trunc-iterated-loop-fibration-fiber-sequence (succ-ℕ n))) ＝
    hom-trunc-direct-iterated-loop-fibration-fiber-sequence n
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
        ( hom-trunc-iterated-loop-boundary-fiber-sequence n)) ＝
    hom-trunc-direct-iterated-loop-boundary-fiber-sequence n
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
      ( hom-trunc-iterated-loop-fibration-fiber-sequence (succ-ℕ n))
      ( hom-trunc-iterated-loop-boundary-fiber-sequence n)
  is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-direct n =
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
      ( hom-trunc-direct-iterated-loop-fibration-fiber-sequence n)
      ( hom-trunc-direct-iterated-loop-boundary-fiber-sequence n)
      ( hom-trunc-iterated-loop-fibration-fiber-sequence (succ-ℕ n))
      ( hom-trunc-iterated-loop-boundary-fiber-sequence n)
      ( eq-tr-hom-trunc-reassociate-iterated-loop-fibration-fiber-sequence n)
      ( eq-tr-hom-trunc-reassociate-iterated-loop-boundary-fiber-sequence n)
      ( is-exact-set-truncation-direct-iterated-loop-fibration-boundary-fiber-sequence n)

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
      ( hom-trunc-iterated-loop-fibration-fiber-sequence 1)
      ( hom-trunc-iterated-loop-boundary-fiber-sequence 0)
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
      ( hom-trunc-iterated-loop-fibration-fiber-sequence 2)
      ( hom-trunc-iterated-loop-boundary-fiber-sequence 1)
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
        ( hom-trunc-iterated-loop-boundary-fiber-sequence n)
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
        ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence n)
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
      ( hom-trunc-iterated-loop-fibration-fiber-sequence (succ-ℕ n))
      ( hom-trunc-iterated-loop-boundary-fiber-sequence n)
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
      ( hom-trunc-iterated-loop-fibration-fiber-sequence (succ-ℕ n))
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence n)
      ( hom-trunc-iterated-loop-boundary-fiber-sequence n)
      ( K)
      ( is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence
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
      map-pointed-map (hom-trunc-iterated-loop-boundary-fiber-sequence n) x ＝
      map-pointed-map
        ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence n)
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
      ( hom-trunc-iterated-loop-fibration-fiber-sequence (succ-ℕ n))
      ( hom-trunc-iterated-loop-boundary-fiber-sequence n)
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
      ( hom-trunc-iterated-loop-fibration-fiber-sequence (succ-ℕ n))
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence n)
      ( hom-trunc-iterated-loop-boundary-fiber-sequence n)
      ( H)
      ( is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence
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
      ( hom-trunc-iterated-loop-fibration-fiber-sequence (succ-ℕ n))
      ( hom-trunc-iterated-loop-boundary-fiber-sequence n)
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
