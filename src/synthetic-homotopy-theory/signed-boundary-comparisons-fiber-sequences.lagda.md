# Signed boundary comparisons for fiber sequences

```agda
module synthetic-homotopy-theory.signed-boundary-comparisons-fiber-sequences where
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
open import foundation.universe-levels

open import structured-types.exact-sequences-pointed-sets
open import structured-types.fiber-sequences
open import structured-types.fibers-of-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.cavallos-trick
open import synthetic-homotopy-theory.fibers-boundary-maps-pointed-maps
open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.iterated-boundary-maps-fiber-sequences
open import synthetic-homotopy-theory.iterated-loop-fiber-sequences
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces-fibers-of-pointed-maps
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.set-truncated-canonical-iterated-exactness-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.set-truncated-exactness-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.set-truncated-iterated-maps-homotopy-groups-fiber-sequences
```

</details>

## Idea

The **signed boundary comparisons** identify the fresh canonical shifted
boundary maps with looped canonical boundary maps only after the systematic
loop-inversion adapter. This module keeps that sign and transport machinery out
of the public long exact sequence package.

## Lemmas

```agda
equiv-inv-Ω :
  {l : Level} (A : Pointed-Type l) → type-Ω A ≃ type-Ω A
pr1 (equiv-inv-Ω A) = inv-Ω A
pr2 (equiv-inv-Ω A) =
  is-equiv-is-invertible
    ( inv-Ω A)
    ( inv-inv)
    ( inv-inv)

pointed-equiv-inv-Ω :
  {l : Level} (A : Pointed-Type l) → Ω A ≃∗ Ω A
pr1 (pointed-equiv-inv-Ω A) = equiv-inv-Ω A
pr2 (pointed-equiv-inv-Ω A) = refl

pointed-equiv-ap-inv-Ω :
  {l : Level} (A : Pointed-Type l) → Ω (Ω A) ≃∗ Ω (Ω A)
pointed-equiv-ap-inv-Ω A =
  pointed-equiv-Ω-pointed-equiv (pointed-equiv-inv-Ω A)
```

## Definitions

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  pointed-equiv-ap-inv-Ω-iterated-loop-base-fiber-sequence :
    (n : ℕ) →
    Ω
      ( iterated-loop-space
        ( succ-ℕ n)
        ( base-fiber-sequence-Pointed-Type S)) ≃∗
    Ω
      ( iterated-loop-space
        ( succ-ℕ n)
        ( base-fiber-sequence-Pointed-Type S))
  pointed-equiv-ap-inv-Ω-iterated-loop-base-fiber-sequence n =
    pointed-equiv-ap-inv-Ω
      ( iterated-loop-space n (base-fiber-sequence-Pointed-Type S))

  pointed-equiv-ap-inv-Ω-iterated-loop-total-space-fiber-sequence :
    (n : ℕ) →
    Ω
      ( iterated-loop-space
        ( succ-ℕ n)
        ( total-space-fiber-sequence-Pointed-Type S)) ≃∗
    Ω
      ( iterated-loop-space
        ( succ-ℕ n)
        ( total-space-fiber-sequence-Pointed-Type S))
  pointed-equiv-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n =
    pointed-equiv-ap-inv-Ω
      ( iterated-loop-space n (total-space-fiber-sequence-Pointed-Type S))

  pointed-map-ap-inv-Ω-iterated-loop-base-fiber-sequence :
    (n : ℕ) →
    Ω
      ( iterated-loop-space
        ( succ-ℕ n)
        ( base-fiber-sequence-Pointed-Type S)) →∗
    Ω
      ( iterated-loop-space
        ( succ-ℕ n)
        ( base-fiber-sequence-Pointed-Type S))
  pointed-map-ap-inv-Ω-iterated-loop-base-fiber-sequence n =
    pointed-map-pointed-equiv
      ( pointed-equiv-ap-inv-Ω-iterated-loop-base-fiber-sequence n)

  pointed-map-ap-inv-Ω-iterated-loop-total-space-fiber-sequence :
    (n : ℕ) →
    Ω
      ( iterated-loop-space
        ( succ-ℕ n)
        ( total-space-fiber-sequence-Pointed-Type S)) →∗
    Ω
      ( iterated-loop-space
        ( succ-ℕ n)
        ( total-space-fiber-sequence-Pointed-Type S))
  pointed-map-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n =
    pointed-map-pointed-equiv
      ( pointed-equiv-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n)

  pointed-map-inv-ap-inv-Ω-iterated-loop-base-fiber-sequence :
    (n : ℕ) →
    Ω
      ( iterated-loop-space
        ( succ-ℕ n)
        ( base-fiber-sequence-Pointed-Type S)) →∗
    Ω
      ( iterated-loop-space
        ( succ-ℕ n)
        ( base-fiber-sequence-Pointed-Type S))
  pointed-map-inv-ap-inv-Ω-iterated-loop-base-fiber-sequence n =
    pointed-map-inv-pointed-equiv
      ( pointed-equiv-ap-inv-Ω-iterated-loop-base-fiber-sequence n)

  pointed-map-inv-ap-inv-Ω-iterated-loop-total-space-fiber-sequence :
    (n : ℕ) →
    Ω
      ( iterated-loop-space
        ( succ-ℕ n)
        ( total-space-fiber-sequence-Pointed-Type S)) →∗
    Ω
      ( iterated-loop-space
        ( succ-ℕ n)
        ( total-space-fiber-sequence-Pointed-Type S))
  pointed-map-inv-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n =
    pointed-map-inv-pointed-equiv
      ( pointed-equiv-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n)

  hom-trunc-ap-inv-Ω-iterated-loop-base-fiber-sequence :
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
            ( succ-ℕ n)
            ( base-fiber-sequence-Pointed-Type S))))
  hom-trunc-ap-inv-Ω-iterated-loop-base-fiber-sequence n =
    hom-trunc-Pointed-Set
      ( pointed-map-ap-inv-Ω-iterated-loop-base-fiber-sequence n)

  hom-trunc-ap-inv-Ω-iterated-loop-total-space-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( total-space-fiber-sequence-Pointed-Type S))))
  hom-trunc-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n =
    hom-trunc-Pointed-Set
      ( pointed-map-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n)

  hom-trunc-inv-ap-inv-Ω-iterated-loop-base-fiber-sequence :
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
            ( succ-ℕ n)
            ( base-fiber-sequence-Pointed-Type S))))
  hom-trunc-inv-ap-inv-Ω-iterated-loop-base-fiber-sequence n =
    hom-trunc-Pointed-Set
      ( pointed-map-inv-ap-inv-Ω-iterated-loop-base-fiber-sequence n)

  hom-trunc-inv-ap-inv-Ω-iterated-loop-total-space-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( total-space-fiber-sequence-Pointed-Type S))))
  hom-trunc-inv-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n =
    hom-trunc-Pointed-Set
      ( pointed-map-inv-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n)

  is-section-hom-trunc-inv-ap-inv-Ω-iterated-loop-base-fiber-sequence :
    (n : ℕ)
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω
            ( iterated-loop-space
              ( succ-ℕ n)
              ( base-fiber-sequence-Pointed-Type S))))) →
    map-pointed-map
      ( hom-trunc-ap-inv-Ω-iterated-loop-base-fiber-sequence n)
      ( map-pointed-map
        ( hom-trunc-inv-ap-inv-Ω-iterated-loop-base-fiber-sequence n)
        ( x)) ＝
    x
  is-section-hom-trunc-inv-ap-inv-Ω-iterated-loop-base-fiber-sequence n x =
    ( inv
      ( preserves-comp-map-trunc-Set
        ( map-pointed-map
          ( pointed-map-ap-inv-Ω-iterated-loop-base-fiber-sequence n))
        ( map-pointed-map
          ( pointed-map-inv-ap-inv-Ω-iterated-loop-base-fiber-sequence n))
        ( x))) ∙
    ( htpy-trunc-Set
      ( is-section-map-inv-pointed-equiv
        ( pointed-equiv-ap-inv-Ω-iterated-loop-base-fiber-sequence n))
      ( x)) ∙
    ( id-map-trunc-Set x)

  is-section-hom-trunc-inv-ap-inv-Ω-iterated-loop-total-space-fiber-sequence :
    (n : ℕ)
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω
            ( iterated-loop-space
              ( succ-ℕ n)
              ( total-space-fiber-sequence-Pointed-Type S))))) →
    map-pointed-map
      ( hom-trunc-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n)
      ( map-pointed-map
        ( hom-trunc-inv-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n)
        ( x)) ＝
    x
  is-section-hom-trunc-inv-ap-inv-Ω-iterated-loop-total-space-fiber-sequence
    n x =
    ( inv
      ( preserves-comp-map-trunc-Set
        ( map-pointed-map
          ( pointed-map-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n))
        ( map-pointed-map
          ( pointed-map-inv-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n))
        ( x))) ∙
    ( htpy-trunc-Set
      ( is-section-map-inv-pointed-equiv
        ( pointed-equiv-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n))
      ( x)) ∙
    ( id-map-trunc-Set x)

  pointed-htpy-ap-inv-Ω-iterated-loop-fibration-fiber-sequence :
    (n : ℕ) →
    ( pointed-map-pointed-equiv
      ( pointed-equiv-inv-Ω
        ( iterated-loop-space n (base-fiber-sequence-Pointed-Type S))) ∘∗
      pointed-map-iterated-loop-space
        ( succ-ℕ n)
        ( fibration-fiber-sequence-Pointed-Type S)) ~∗
    ( pointed-map-iterated-loop-space
      ( succ-ℕ n)
      ( fibration-fiber-sequence-Pointed-Type S) ∘∗
      pointed-map-pointed-equiv
        ( pointed-equiv-inv-Ω
          ( iterated-loop-space n
            ( total-space-fiber-sequence-Pointed-Type S))))
  pointed-htpy-ap-inv-Ω-iterated-loop-fibration-fiber-sequence n =
    cavallos-trick-H-Space'
      ( Ω (iterated-loop-space n (total-space-fiber-sequence-Pointed-Type S)))
      ( Ω-H-Space
        ( iterated-loop-space n (base-fiber-sequence-Pointed-Type S)))
      ( pointed-map-pointed-equiv
        ( pointed-equiv-inv-Ω
          ( iterated-loop-space n (base-fiber-sequence-Pointed-Type S))) ∘∗
        pointed-map-iterated-loop-space
          ( succ-ℕ n)
          ( fibration-fiber-sequence-Pointed-Type S))
      ( pointed-map-iterated-loop-space
        ( succ-ℕ n)
        ( fibration-fiber-sequence-Pointed-Type S) ∘∗
        pointed-map-pointed-equiv
          ( pointed-equiv-inv-Ω
            ( iterated-loop-space n
              ( total-space-fiber-sequence-Pointed-Type S))))
      ( λ p →
        inv
          ( preserves-inv-map-Ω
            ( pointed-map-iterated-loop-space
              n
              ( fibration-fiber-sequence-Pointed-Type S))
            ( p)))

  coherence-square-pointed-map-ap-inv-Ω-iterated-loop-fibration-fiber-sequence :
    (n : ℕ)
    (q :
      type-Ω
        ( iterated-loop-space
          ( succ-ℕ n)
          ( total-space-fiber-sequence-Pointed-Type S))) →
    map-pointed-map
      ( pointed-map-ap-inv-Ω-iterated-loop-base-fiber-sequence n)
      ( map-pointed-map
        ( pointed-map-Ω
          ( pointed-map-iterated-loop-space
            ( succ-ℕ n)
            ( fibration-fiber-sequence-Pointed-Type S)))
        ( q)) ＝
    map-pointed-map
      ( pointed-map-Ω
        ( pointed-map-iterated-loop-space
          ( succ-ℕ n)
          ( fibration-fiber-sequence-Pointed-Type S)))
      ( map-pointed-map
        ( pointed-map-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n)
        ( q))
  coherence-square-pointed-map-ap-inv-Ω-iterated-loop-fibration-fiber-sequence
    n q =
    ( inv
      ( preserves-comp-map-Ω
        ( pointed-map-pointed-equiv
          ( pointed-equiv-inv-Ω
            ( iterated-loop-space n
              ( base-fiber-sequence-Pointed-Type S))))
        ( pointed-map-iterated-loop-space
          ( succ-ℕ n)
          ( fibration-fiber-sequence-Pointed-Type S))
        ( q))) ∙
    ( htpy-map-Ω
      ( pointed-map-pointed-equiv
        ( pointed-equiv-inv-Ω
          ( iterated-loop-space n (base-fiber-sequence-Pointed-Type S))) ∘∗
        pointed-map-iterated-loop-space
          ( succ-ℕ n)
          ( fibration-fiber-sequence-Pointed-Type S))
      ( pointed-map-iterated-loop-space
        ( succ-ℕ n)
        ( fibration-fiber-sequence-Pointed-Type S) ∘∗
        pointed-map-pointed-equiv
          ( pointed-equiv-inv-Ω
            ( iterated-loop-space n
              ( total-space-fiber-sequence-Pointed-Type S))))
      ( pointed-htpy-ap-inv-Ω-iterated-loop-fibration-fiber-sequence n)
      ( q)) ∙
    ( preserves-comp-map-Ω
      ( pointed-map-iterated-loop-space
        ( succ-ℕ n)
        ( fibration-fiber-sequence-Pointed-Type S))
      ( pointed-map-pointed-equiv
        ( pointed-equiv-inv-Ω
          ( iterated-loop-space n
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( q))

  coherence-square-hom-trunc-ap-inv-Ω-iterated-loop-fibration-fiber-sequence :
    (n : ℕ)
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω
            ( iterated-loop-space
              ( succ-ℕ n)
              ( total-space-fiber-sequence-Pointed-Type S))))) →
    map-pointed-map
      ( hom-trunc-ap-inv-Ω-iterated-loop-base-fiber-sequence n)
      ( map-pointed-map
        ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
        ( x)) ＝
    map-pointed-map
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
      ( map-pointed-map
        ( hom-trunc-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n)
        ( x))
  coherence-square-hom-trunc-ap-inv-Ω-iterated-loop-fibration-fiber-sequence
    n x =
    ( inv
      ( preserves-comp-map-trunc-Set
        ( map-pointed-map
          ( pointed-map-ap-inv-Ω-iterated-loop-base-fiber-sequence n))
        ( map-pointed-map
          ( pointed-map-Ω
            ( pointed-map-iterated-loop-space
              ( succ-ℕ n)
              ( fibration-fiber-sequence-Pointed-Type S))))
        ( x))) ∙
    ( htpy-trunc-Set
      ( coherence-square-pointed-map-ap-inv-Ω-iterated-loop-fibration-fiber-sequence
        n)
      ( x)) ∙
    ( preserves-comp-map-trunc-Set
      ( map-pointed-map
        ( pointed-map-Ω
          ( pointed-map-iterated-loop-space
            ( succ-ℕ n)
            ( fibration-fiber-sequence-Pointed-Type S))))
      ( map-pointed-map
        ( pointed-map-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n))
      ( x))

  coherence-square-hom-trunc-inv-ap-inv-Ω-iterated-loop-fibration-fiber-sequence :
    (n : ℕ)
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω
            ( iterated-loop-space
              ( succ-ℕ n)
              ( total-space-fiber-sequence-Pointed-Type S))))) →
    map-pointed-map
      ( hom-trunc-inv-ap-inv-Ω-iterated-loop-base-fiber-sequence n)
      ( map-pointed-map
        ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
        ( x)) ＝
    map-pointed-map
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
      ( map-pointed-map
        ( hom-trunc-inv-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n)
        ( x))
  coherence-square-hom-trunc-inv-ap-inv-Ω-iterated-loop-fibration-fiber-sequence
    n x =
    is-injective-equiv
      ( equiv-trunc-Set
        ( equiv-pointed-equiv
          ( pointed-equiv-ap-inv-Ω-iterated-loop-base-fiber-sequence n)))
      ( ( is-section-hom-trunc-inv-ap-inv-Ω-iterated-loop-base-fiber-sequence
          ( n)
          ( map-pointed-map
            ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
            ( x))) ∙
        ( inv
          ( ( coherence-square-hom-trunc-ap-inv-Ω-iterated-loop-fibration-fiber-sequence
              ( n)
              ( map-pointed-map
                ( hom-trunc-inv-ap-inv-Ω-iterated-loop-total-space-fiber-sequence
                  n)
                ( x))) ∙
            ( ap
              ( map-pointed-map
                ( hom-trunc-iterated-loop-fibration-fiber-sequence
                  S
                  ( succ-ℕ n)))
              ( is-section-hom-trunc-inv-ap-inv-Ω-iterated-loop-total-space-fiber-sequence
                ( n)
                ( x))))))

  iff-image-hom-trunc-inv-ap-inv-Ω-iterated-loop-base-fibration-fiber-sequence :
    (n : ℕ)
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω
            ( iterated-loop-space
              ( succ-ℕ n)
              ( base-fiber-sequence-Pointed-Type S))))) →
    is-in-image-hom-Pointed-Set
      { A =
        trunc-Pointed-Set
          ( Ω
            ( iterated-loop-space
              ( succ-ℕ n)
              ( total-space-fiber-sequence-Pointed-Type S)))}
      { B =
        trunc-Pointed-Set
          ( Ω
            ( iterated-loop-space
              ( succ-ℕ n)
              ( base-fiber-sequence-Pointed-Type S)))}
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
      ( map-pointed-map
        ( hom-trunc-inv-ap-inv-Ω-iterated-loop-base-fiber-sequence n)
        ( x)) ↔
    is-in-image-hom-Pointed-Set
      { A =
        trunc-Pointed-Set
          ( Ω
            ( iterated-loop-space
              ( succ-ℕ n)
              ( total-space-fiber-sequence-Pointed-Type S)))}
      { B =
        trunc-Pointed-Set
          ( Ω
            ( iterated-loop-space
              ( succ-ℕ n)
              ( base-fiber-sequence-Pointed-Type S)))}
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
      ( x)
  iff-image-hom-trunc-inv-ap-inv-Ω-iterated-loop-base-fibration-fiber-sequence
    n =
    iff-image-hom-Pointed-Set-middle-self-map
      { A =
        trunc-Pointed-Set
          ( Ω
            ( iterated-loop-space
              ( succ-ℕ n)
              ( total-space-fiber-sequence-Pointed-Type S)))}
      { B =
        trunc-Pointed-Set
          ( Ω
            ( iterated-loop-space
              ( succ-ℕ n)
              ( base-fiber-sequence-Pointed-Type S)))}
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
      ( hom-trunc-inv-ap-inv-Ω-iterated-loop-base-fiber-sequence n)
      ( hom-trunc-ap-inv-Ω-iterated-loop-base-fiber-sequence n)
      ( map-pointed-map
        ( hom-trunc-inv-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n))
      ( map-pointed-map
        ( hom-trunc-ap-inv-Ω-iterated-loop-total-space-fiber-sequence n))
      ( coherence-square-hom-trunc-inv-ap-inv-Ω-iterated-loop-fibration-fiber-sequence
        n)
      ( coherence-square-hom-trunc-ap-inv-Ω-iterated-loop-fibration-fiber-sequence
        n)
      ( is-section-hom-trunc-inv-ap-inv-Ω-iterated-loop-base-fiber-sequence
        n)

  pointed-equiv-ap-inv-Ω-base-fiber-sequence :
    Ω (Ω (base-fiber-sequence-Pointed-Type S)) ≃∗
    Ω (Ω (base-fiber-sequence-Pointed-Type S))
  pointed-equiv-ap-inv-Ω-base-fiber-sequence =
    pointed-equiv-ap-inv-Ω (base-fiber-sequence-Pointed-Type S)

  pointed-equiv-ap-inv-Ω-total-space-fiber-sequence :
    Ω (Ω (total-space-fiber-sequence-Pointed-Type S)) ≃∗
    Ω (Ω (total-space-fiber-sequence-Pointed-Type S))
  pointed-equiv-ap-inv-Ω-total-space-fiber-sequence =
    pointed-equiv-ap-inv-Ω (total-space-fiber-sequence-Pointed-Type S)

  pointed-map-ap-inv-Ω-base-fiber-sequence :
    Ω (Ω (base-fiber-sequence-Pointed-Type S)) →∗
    Ω (Ω (base-fiber-sequence-Pointed-Type S))
  pointed-map-ap-inv-Ω-base-fiber-sequence =
    pointed-map-pointed-equiv pointed-equiv-ap-inv-Ω-base-fiber-sequence

  pointed-map-ap-inv-Ω-total-space-fiber-sequence :
    Ω (Ω (total-space-fiber-sequence-Pointed-Type S)) →∗
    Ω (Ω (total-space-fiber-sequence-Pointed-Type S))
  pointed-map-ap-inv-Ω-total-space-fiber-sequence =
    pointed-map-pointed-equiv
      pointed-equiv-ap-inv-Ω-total-space-fiber-sequence

  pointed-map-inv-ap-inv-Ω-base-fiber-sequence :
    Ω (Ω (base-fiber-sequence-Pointed-Type S)) →∗
    Ω (Ω (base-fiber-sequence-Pointed-Type S))
  pointed-map-inv-ap-inv-Ω-base-fiber-sequence =
    pointed-map-inv-pointed-equiv
      pointed-equiv-ap-inv-Ω-base-fiber-sequence

  pointed-map-inv-ap-inv-Ω-total-space-fiber-sequence :
    Ω (Ω (total-space-fiber-sequence-Pointed-Type S)) →∗
    Ω (Ω (total-space-fiber-sequence-Pointed-Type S))
  pointed-map-inv-ap-inv-Ω-total-space-fiber-sequence =
    pointed-map-inv-pointed-equiv
      pointed-equiv-ap-inv-Ω-total-space-fiber-sequence

  hom-trunc-ap-inv-Ω-base-fiber-sequence :
    hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω (Ω (base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω (Ω (base-fiber-sequence-Pointed-Type S))))
  hom-trunc-ap-inv-Ω-base-fiber-sequence =
    hom-trunc-Pointed-Set pointed-map-ap-inv-Ω-base-fiber-sequence

  hom-trunc-ap-inv-Ω-total-space-fiber-sequence :
    hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω (Ω (total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω (Ω (total-space-fiber-sequence-Pointed-Type S))))
  hom-trunc-ap-inv-Ω-total-space-fiber-sequence =
    hom-trunc-Pointed-Set pointed-map-ap-inv-Ω-total-space-fiber-sequence

  hom-trunc-inv-ap-inv-Ω-base-fiber-sequence :
    hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω (Ω (base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω (Ω (base-fiber-sequence-Pointed-Type S))))
  hom-trunc-inv-ap-inv-Ω-base-fiber-sequence =
    hom-trunc-Pointed-Set pointed-map-inv-ap-inv-Ω-base-fiber-sequence

  hom-trunc-inv-ap-inv-Ω-total-space-fiber-sequence :
    hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω (Ω (total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω (Ω (total-space-fiber-sequence-Pointed-Type S))))
  hom-trunc-inv-ap-inv-Ω-total-space-fiber-sequence =
    hom-trunc-Pointed-Set
      pointed-map-inv-ap-inv-Ω-total-space-fiber-sequence

  is-section-hom-trunc-inv-ap-inv-Ω-base-fiber-sequence :
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω (Ω (base-fiber-sequence-Pointed-Type S))))) →
    map-pointed-map hom-trunc-ap-inv-Ω-base-fiber-sequence
      ( map-pointed-map hom-trunc-inv-ap-inv-Ω-base-fiber-sequence x) ＝
    x
  is-section-hom-trunc-inv-ap-inv-Ω-base-fiber-sequence x =
    ( inv
      ( preserves-comp-map-trunc-Set
        ( map-pointed-map pointed-map-ap-inv-Ω-base-fiber-sequence)
        ( map-pointed-map pointed-map-inv-ap-inv-Ω-base-fiber-sequence)
        ( x))) ∙
    ( htpy-trunc-Set
      ( is-section-map-inv-pointed-equiv
        pointed-equiv-ap-inv-Ω-base-fiber-sequence)
      ( x)) ∙
    ( id-map-trunc-Set x)

  is-section-hom-trunc-inv-ap-inv-Ω-total-space-fiber-sequence :
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω (Ω (total-space-fiber-sequence-Pointed-Type S))))) →
    map-pointed-map hom-trunc-ap-inv-Ω-total-space-fiber-sequence
      ( map-pointed-map
        hom-trunc-inv-ap-inv-Ω-total-space-fiber-sequence
        x) ＝
    x
  is-section-hom-trunc-inv-ap-inv-Ω-total-space-fiber-sequence x =
    ( inv
      ( preserves-comp-map-trunc-Set
        ( map-pointed-map
          pointed-map-ap-inv-Ω-total-space-fiber-sequence)
        ( map-pointed-map
          pointed-map-inv-ap-inv-Ω-total-space-fiber-sequence)
        ( x))) ∙
    ( htpy-trunc-Set
      ( is-section-map-inv-pointed-equiv
        pointed-equiv-ap-inv-Ω-total-space-fiber-sequence)
      ( x)) ∙
    ( id-map-trunc-Set x)

  pointed-htpy-ap-inv-Ω-fibration-fiber-sequence :
    ( pointed-map-pointed-equiv
      ( pointed-equiv-inv-Ω (base-fiber-sequence-Pointed-Type S)) ∘∗
      pointed-map-iterated-loop-space
        ( 1)
        ( fibration-fiber-sequence-Pointed-Type S)) ~∗
    ( pointed-map-iterated-loop-space
      ( 1)
      ( fibration-fiber-sequence-Pointed-Type S) ∘∗
      pointed-map-pointed-equiv
        ( pointed-equiv-inv-Ω
          ( total-space-fiber-sequence-Pointed-Type S)))
  pointed-htpy-ap-inv-Ω-fibration-fiber-sequence =
    cavallos-trick-H-Space'
      ( Ω (total-space-fiber-sequence-Pointed-Type S))
      ( Ω-H-Space (base-fiber-sequence-Pointed-Type S))
      ( pointed-map-pointed-equiv
        ( pointed-equiv-inv-Ω (base-fiber-sequence-Pointed-Type S)) ∘∗
        pointed-map-iterated-loop-space
          ( 1)
          ( fibration-fiber-sequence-Pointed-Type S))
      ( pointed-map-iterated-loop-space
        ( 1)
        ( fibration-fiber-sequence-Pointed-Type S) ∘∗
        pointed-map-pointed-equiv
          ( pointed-equiv-inv-Ω
            ( total-space-fiber-sequence-Pointed-Type S)))
      ( λ p →
        inv
          ( preserves-inv-map-Ω
            ( fibration-fiber-sequence-Pointed-Type S)
            ( p)))

  coherence-square-pointed-map-ap-inv-Ω-fibration-fiber-sequence :
    (q : type-Ω (Ω (total-space-fiber-sequence-Pointed-Type S))) →
    map-pointed-map pointed-map-ap-inv-Ω-base-fiber-sequence
      ( map-pointed-map
        ( pointed-map-Ω
          ( pointed-map-iterated-loop-space
            ( 1)
            ( fibration-fiber-sequence-Pointed-Type S)))
        ( q)) ＝
    map-pointed-map
      ( pointed-map-Ω
        ( pointed-map-iterated-loop-space
          ( 1)
          ( fibration-fiber-sequence-Pointed-Type S)))
      ( map-pointed-map
        pointed-map-ap-inv-Ω-total-space-fiber-sequence
        q)
  coherence-square-pointed-map-ap-inv-Ω-fibration-fiber-sequence q =
    ( inv
      ( preserves-comp-map-Ω
        ( pointed-map-pointed-equiv
          ( pointed-equiv-inv-Ω (base-fiber-sequence-Pointed-Type S)))
        ( pointed-map-iterated-loop-space
          ( 1)
          ( fibration-fiber-sequence-Pointed-Type S))
        ( q))) ∙
    ( htpy-map-Ω
      ( pointed-map-pointed-equiv
        ( pointed-equiv-inv-Ω (base-fiber-sequence-Pointed-Type S)) ∘∗
        pointed-map-iterated-loop-space
          ( 1)
          ( fibration-fiber-sequence-Pointed-Type S))
      ( pointed-map-iterated-loop-space
        ( 1)
        ( fibration-fiber-sequence-Pointed-Type S) ∘∗
        pointed-map-pointed-equiv
          ( pointed-equiv-inv-Ω
            ( total-space-fiber-sequence-Pointed-Type S)))
      ( pointed-htpy-ap-inv-Ω-fibration-fiber-sequence)
      ( q)) ∙
    ( preserves-comp-map-Ω
      ( pointed-map-iterated-loop-space
        ( 1)
        ( fibration-fiber-sequence-Pointed-Type S))
      ( pointed-map-pointed-equiv
        ( pointed-equiv-inv-Ω
          ( total-space-fiber-sequence-Pointed-Type S)))
      ( q))

  coherence-square-hom-trunc-ap-inv-Ω-fibration-fiber-sequence :
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω (Ω (total-space-fiber-sequence-Pointed-Type S))))) →
    map-pointed-map hom-trunc-ap-inv-Ω-base-fiber-sequence
      ( map-pointed-map
        ( hom-trunc-iterated-loop-fibration-fiber-sequence S 1)
        ( x)) ＝
    map-pointed-map
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S 1)
      ( map-pointed-map
        hom-trunc-ap-inv-Ω-total-space-fiber-sequence
        x)
  coherence-square-hom-trunc-ap-inv-Ω-fibration-fiber-sequence x =
    ( inv
      ( preserves-comp-map-trunc-Set
        ( map-pointed-map pointed-map-ap-inv-Ω-base-fiber-sequence)
        ( map-pointed-map
          ( pointed-map-Ω
            ( pointed-map-iterated-loop-space
              ( 1)
              ( fibration-fiber-sequence-Pointed-Type S))))
        ( x))) ∙
    ( htpy-trunc-Set
      ( coherence-square-pointed-map-ap-inv-Ω-fibration-fiber-sequence)
      ( x)) ∙
    ( preserves-comp-map-trunc-Set
      ( map-pointed-map
        ( pointed-map-Ω
          ( pointed-map-iterated-loop-space
            ( 1)
            ( fibration-fiber-sequence-Pointed-Type S))))
      ( map-pointed-map pointed-map-ap-inv-Ω-total-space-fiber-sequence)
      ( x))

  coherence-square-hom-trunc-inv-ap-inv-Ω-fibration-fiber-sequence :
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω (Ω (total-space-fiber-sequence-Pointed-Type S))))) →
    map-pointed-map hom-trunc-inv-ap-inv-Ω-base-fiber-sequence
      ( map-pointed-map
        ( hom-trunc-iterated-loop-fibration-fiber-sequence S 1)
        ( x)) ＝
    map-pointed-map
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S 1)
      ( map-pointed-map
        hom-trunc-inv-ap-inv-Ω-total-space-fiber-sequence
        x)
  coherence-square-hom-trunc-inv-ap-inv-Ω-fibration-fiber-sequence x =
    is-injective-equiv
      ( equiv-trunc-Set
        ( equiv-pointed-equiv
          pointed-equiv-ap-inv-Ω-base-fiber-sequence))
      ( ( is-section-hom-trunc-inv-ap-inv-Ω-base-fiber-sequence
          ( map-pointed-map
            ( hom-trunc-iterated-loop-fibration-fiber-sequence S 1)
            ( x))) ∙
        ( inv
          ( ( coherence-square-hom-trunc-ap-inv-Ω-fibration-fiber-sequence
              ( map-pointed-map
                hom-trunc-inv-ap-inv-Ω-total-space-fiber-sequence
                x)) ∙
            ( ap
              ( map-pointed-map
                ( hom-trunc-iterated-loop-fibration-fiber-sequence S 1))
              ( is-section-hom-trunc-inv-ap-inv-Ω-total-space-fiber-sequence
                ( x))))))

  iff-image-hom-trunc-inv-ap-inv-Ω-base-fibration-fiber-sequence :
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω (Ω (base-fiber-sequence-Pointed-Type S))))) →
    is-in-image-hom-Pointed-Set
      { A =
        trunc-Pointed-Set
          ( Ω (Ω (total-space-fiber-sequence-Pointed-Type S)))}
      { B =
        trunc-Pointed-Set
          ( Ω (Ω (base-fiber-sequence-Pointed-Type S)))}
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S 1)
      ( map-pointed-map hom-trunc-inv-ap-inv-Ω-base-fiber-sequence x) ↔
    is-in-image-hom-Pointed-Set
      { A =
        trunc-Pointed-Set
          ( Ω (Ω (total-space-fiber-sequence-Pointed-Type S)))}
      { B =
        trunc-Pointed-Set
          ( Ω (Ω (base-fiber-sequence-Pointed-Type S)))}
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S 1)
      ( x)
  iff-image-hom-trunc-inv-ap-inv-Ω-base-fibration-fiber-sequence =
    iff-image-hom-Pointed-Set-middle-self-map
      { A =
        trunc-Pointed-Set
          ( Ω (Ω (total-space-fiber-sequence-Pointed-Type S)))}
      { B =
        trunc-Pointed-Set
          ( Ω (Ω (base-fiber-sequence-Pointed-Type S)))}
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S 1)
      ( hom-trunc-inv-ap-inv-Ω-base-fiber-sequence)
      ( hom-trunc-ap-inv-Ω-base-fiber-sequence)
      ( map-pointed-map
        hom-trunc-inv-ap-inv-Ω-total-space-fiber-sequence)
      ( map-pointed-map hom-trunc-ap-inv-Ω-total-space-fiber-sequence)
      ( coherence-square-hom-trunc-inv-ap-inv-Ω-fibration-fiber-sequence)
      ( coherence-square-hom-trunc-ap-inv-Ω-fibration-fiber-sequence)
      ( is-section-hom-trunc-inv-ap-inv-Ω-base-fiber-sequence)

  eq-map-Ω-pointed-map-fiber-fiber-canonical-first-loop-boundary-fiber-sequence :
    (q : type-Ω (Ω (base-fiber-sequence-Pointed-Type S))) →
    map-Ω (pointed-map-fiber-fiber-sequence-Pointed-Type S)
      ( map-pointed-map
        ( boundary-pointed-map-fiber-sequence
          ( iterated-loop-fiber-sequence S 1))
        ( q)) ＝
    map-Ω
      ( boundary-fiber-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))
      ( map-pointed-map pointed-map-ap-inv-Ω-base-fiber-sequence q)
  eq-map-Ω-pointed-map-fiber-fiber-canonical-first-loop-boundary-fiber-sequence q =
    ( is-injective-equiv
      ( equiv-pointed-equiv
        ( pointed-equiv-loop-fiber-Pointed-Type
          ( fibration-fiber-sequence-Pointed-Type S)))
      ( ( is-section-map-inv-pointed-equiv
          ( pointed-equiv-iterated-loop-fiber-fiber-sequence S 1)
          ( map-pointed-map
            ( boundary-fiber-Pointed-Type
              ( pointed-map-Ω (fibration-fiber-sequence-Pointed-Type S)))
            ( q))) ∙
        ( inv
          ( is-section-map-inv-pointed-equiv
            ( pointed-equiv-loop-fiber-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S))
            ( map-pointed-map
              ( boundary-fiber-Pointed-Type
                ( pointed-map-Ω (fibration-fiber-sequence-Pointed-Type S)))
              ( q)))))) ∙
    ( is-injective-equiv
      ( equiv-pointed-equiv
        ( pointed-equiv-loop-fiber-Pointed-Type
          ( fibration-fiber-sequence-Pointed-Type S)))
      ( ( is-section-map-inv-pointed-equiv
          ( pointed-equiv-loop-fiber-Pointed-Type
            ( fibration-fiber-sequence-Pointed-Type S))
          ( map-pointed-map
            ( boundary-fiber-Pointed-Type
              ( pointed-map-Ω (fibration-fiber-sequence-Pointed-Type S)))
            ( q))) ∙
        ( inv
          ( eq-map-loop-fiber-map-Ω-boundary-fiber-Pointed-Type
            ( fibration-fiber-sequence-Pointed-Type S)
            ( q)))))

  eq-map-hom-trunc-loop-pointed-map-fiber-fiber-canonical-first-loop-boundary-fiber-sequence :
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω (Ω (base-fiber-sequence-Pointed-Type S))))) →
    map-pointed-map
      ( hom-trunc-loop-pointed-map-fiber-fiber-sequence-Pointed-Type S)
      ( map-pointed-map
        ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence S zero-ℕ)
        ( x)) ＝
    map-pointed-map
      ( hom-trunc-loop-boundary-boundary-fiber-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))
      ( map-pointed-map hom-trunc-ap-inv-Ω-base-fiber-sequence x)
  eq-map-hom-trunc-loop-pointed-map-fiber-fiber-canonical-first-loop-boundary-fiber-sequence =
    apply-dependent-universal-property-trunc-Set'
      ( λ x →
        set-Prop
          ( Id-Prop
            ( set-Pointed-Set
              ( trunc-Pointed-Set
                ( Ω
                  ( fiber-Pointed-Type
                    ( fibration-fiber-sequence-Pointed-Type S)))))
            ( map-pointed-map
              ( hom-trunc-loop-pointed-map-fiber-fiber-sequence-Pointed-Type S)
              ( map-pointed-map
                ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence
                  S
                  zero-ℕ)
                ( x)))
            ( map-pointed-map
              ( hom-trunc-loop-boundary-boundary-fiber-Pointed-Type
                ( fibration-fiber-sequence-Pointed-Type S))
              ( map-pointed-map hom-trunc-ap-inv-Ω-base-fiber-sequence x))))
      ( λ q →
        ( ap
          ( map-pointed-map
            ( hom-trunc-loop-pointed-map-fiber-fiber-sequence-Pointed-Type S))
          ( naturality-unit-trunc-Set
            ( map-pointed-map
              ( boundary-pointed-map-fiber-sequence
                ( iterated-loop-fiber-sequence S 1)))
            ( q))) ∙
        ( naturality-unit-trunc-Set
          ( map-pointed-map
            ( pointed-map-Ω
              ( pointed-map-fiber-fiber-sequence-Pointed-Type S)))
          ( map-pointed-map
            ( boundary-pointed-map-fiber-sequence
              ( iterated-loop-fiber-sequence S 1))
            ( q))) ∙
        ( ap
          ( unit-trunc-Set)
          ( eq-map-Ω-pointed-map-fiber-fiber-canonical-first-loop-boundary-fiber-sequence
            ( q))) ∙
        ( inv
          ( naturality-unit-trunc-Set
            ( map-pointed-map
              ( pointed-map-Ω
                ( boundary-fiber-Pointed-Type
                  ( fibration-fiber-sequence-Pointed-Type S))))
            ( map-pointed-map
              pointed-map-ap-inv-Ω-base-fiber-sequence
              q))) ∙
        ( ap
          ( map-pointed-map
            ( hom-trunc-loop-boundary-boundary-fiber-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S)))
          ( inv
            ( naturality-unit-trunc-Set
              ( map-pointed-map pointed-map-ap-inv-Ω-base-fiber-sequence)
              ( q)))))

  coherence-square-first-loop-canonical-iterated-boundary-fiber-sequence-signed :
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω (Ω (base-fiber-sequence-Pointed-Type S))))) →
    map-pointed-map
      ( hom-trunc-loop-canonical-iterated-boundary-fiber-sequence S zero-ℕ)
      ( map-pointed-map hom-trunc-ap-inv-Ω-base-fiber-sequence x) ＝
    map-pointed-map
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence S zero-ℕ)
      ( x)
  coherence-square-first-loop-canonical-iterated-boundary-fiber-sequence-signed x =
    is-injective-map-trunc-Set
      ( map-Ω (pointed-map-fiber-fiber-sequence-Pointed-Type S))
      ( is-injective-equiv
        ( equiv-Ω-pointed-equiv
          ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S)))
      ( ( eq-map-hom-trunc-loop-boundary-fiber-sequence-Pointed-Type S
          ( map-pointed-map hom-trunc-ap-inv-Ω-base-fiber-sequence x)) ∙
        ( inv
          ( eq-map-hom-trunc-loop-pointed-map-fiber-fiber-canonical-first-loop-boundary-fiber-sequence
            ( x))))

```

## Theorems

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  is-exact-set-truncation-loop-canonical-iterated-boundary-fiber-sequence-first-loop-signed :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω (Ω (total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω (Ω (base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω (fiber-fiber-sequence-Pointed-Type S)))
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S 1)
      ( hom-trunc-loop-canonical-iterated-boundary-fiber-sequence S zero-ℕ)
  is-exact-set-truncation-loop-canonical-iterated-boundary-fiber-sequence-first-loop-signed =
    is-exact-hom-Pointed-Set-image-kernel-shift-right-inverse
      ( trunc-Pointed-Set
        ( Ω (Ω (total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω (Ω (base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω (fiber-fiber-sequence-Pointed-Type S)))
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S 1)
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence S zero-ℕ)
      ( hom-trunc-loop-canonical-iterated-boundary-fiber-sequence S zero-ℕ)
      ( hom-trunc-ap-inv-Ω-base-fiber-sequence S)
      ( hom-trunc-inv-ap-inv-Ω-base-fiber-sequence S)
      ( iff-image-hom-trunc-inv-ap-inv-Ω-base-fibration-fiber-sequence S)
      ( coherence-square-first-loop-canonical-iterated-boundary-fiber-sequence-signed S)
      ( is-section-hom-trunc-inv-ap-inv-Ω-base-fiber-sequence S)
      ( is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence
        S
        ( zero-ℕ))

```

## All-index signed comparison between looped and shifted boundaries

The looped canonical boundary is the group-facing boundary convention. The
fresh shifted boundary is the convention for which the loop-boundary exactness
theorem applies directly. The comparison between them is the first-loop
comparison applied to the iterated loop fiber sequence.

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  coherence-square-canonical-iterated-boundary-fiber-sequence-signed :
    (n : ℕ)
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω
            ( iterated-loop-space
              ( succ-ℕ n)
              ( base-fiber-sequence-Pointed-Type S))))) →
    map-pointed-map
      ( hom-trunc-loop-canonical-iterated-boundary-fiber-sequence S n)
      ( map-pointed-map
        ( hom-trunc-ap-inv-Ω-iterated-loop-base-fiber-sequence S n)
        ( x)) ＝
    map-pointed-map
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence S n)
      ( x)
  coherence-square-canonical-iterated-boundary-fiber-sequence-signed
    n =
    coherence-square-first-loop-canonical-iterated-boundary-fiber-sequence-signed
      ( iterated-loop-fiber-sequence S n)

  is-exact-set-truncation-loop-canonical-iterated-boundary-fiber-sequence-signed :
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
      ( hom-trunc-loop-canonical-iterated-boundary-fiber-sequence S n)
  is-exact-set-truncation-loop-canonical-iterated-boundary-fiber-sequence-signed
    n =
    is-exact-hom-Pointed-Set-image-kernel-shift-right-inverse
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
      ( hom-trunc-loop-canonical-iterated-boundary-fiber-sequence S n)
      ( hom-trunc-ap-inv-Ω-iterated-loop-base-fiber-sequence S n)
      ( hom-trunc-inv-ap-inv-Ω-iterated-loop-base-fiber-sequence S n)
      ( iff-image-hom-trunc-inv-ap-inv-Ω-iterated-loop-base-fibration-fiber-sequence
        ( S)
        ( n))
      ( coherence-square-canonical-iterated-boundary-fiber-sequence-signed n)
      ( is-section-hom-trunc-inv-ap-inv-Ω-iterated-loop-base-fiber-sequence
        ( S)
        ( n))
      ( is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence
        ( S)
        ( n))
```
