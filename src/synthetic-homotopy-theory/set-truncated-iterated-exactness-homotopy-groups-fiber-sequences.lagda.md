# Set-truncated iterated exactness of homotopy groups of fiber sequences

```agda
module synthetic-homotopy-theory.set-truncated-iterated-exactness-homotopy-groups-fiber-sequences where
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
open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.long-exact-sequence-homotopy-groups
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.reassociation-iterated-loop-spaces
```

</details>

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

  hom-trunc-loop-canonical-iterated-boundary-fiber-sequence :
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
  hom-trunc-loop-canonical-iterated-boundary-fiber-sequence n =
    hom-trunc-Pointed-Set
      ( pointed-map-Ω
        ( canonical-pointed-map-iterated-boundary-fiber-sequence S n))

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
        ( hom-trunc-iterated-loop-fibration-fiber-sequence 1)
        ( x)) ＝
    map-pointed-map
      ( hom-trunc-iterated-loop-fibration-fiber-sequence 1)
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
        ( hom-trunc-iterated-loop-fibration-fiber-sequence 1)
        ( x)) ＝
    map-pointed-map
      ( hom-trunc-iterated-loop-fibration-fiber-sequence 1)
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
            ( hom-trunc-iterated-loop-fibration-fiber-sequence 1)
            ( x))) ∙
        ( inv
          ( ( coherence-square-hom-trunc-ap-inv-Ω-fibration-fiber-sequence
              ( map-pointed-map
                hom-trunc-inv-ap-inv-Ω-total-space-fiber-sequence
                x)) ∙
            ( ap
              ( map-pointed-map
                ( hom-trunc-iterated-loop-fibration-fiber-sequence 1))
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
      ( hom-trunc-iterated-loop-fibration-fiber-sequence 1)
      ( map-pointed-map hom-trunc-inv-ap-inv-Ω-base-fiber-sequence x) ↔
    is-in-image-hom-Pointed-Set
      { A =
        trunc-Pointed-Set
          ( Ω (Ω (total-space-fiber-sequence-Pointed-Type S)))}
      { B =
        trunc-Pointed-Set
          ( Ω (Ω (base-fiber-sequence-Pointed-Type S)))}
      ( hom-trunc-iterated-loop-fibration-fiber-sequence 1)
      ( x)
  iff-image-hom-trunc-inv-ap-inv-Ω-base-fibration-fiber-sequence =
    iff-image-hom-Pointed-Set-middle-self-map
      { A =
        trunc-Pointed-Set
          ( Ω (Ω (total-space-fiber-sequence-Pointed-Type S)))}
      { B =
        trunc-Pointed-Set
          ( Ω (Ω (base-fiber-sequence-Pointed-Type S)))}
      ( hom-trunc-iterated-loop-fibration-fiber-sequence 1)
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
        ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence zero-ℕ)
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
      ( hom-trunc-loop-canonical-iterated-boundary-fiber-sequence zero-ℕ)
      ( map-pointed-map hom-trunc-ap-inv-Ω-base-fiber-sequence x) ＝
    map-pointed-map
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence zero-ℕ)
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

The canonical long exact sequence package records the two adjacent uses of the
boundary map separately. The fibration-boundary segment uses the fresh
boundary map of the shifted iterated loop fiber sequence, while the
boundary-fiber-inclusion segment uses the loop-boundary map of the current
iterated loop fiber sequence. These have the same displayed source and target,
but this package does not assert that they are equal.

```agda

  record Set-Truncated-Canonical-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence :
    UU (l1 ⊔ l2 ⊔ l3)
    where
    constructor
      make-Set-Truncated-Canonical-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence
    field
      hom-fiber-inclusion-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence :
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
      hom-fibration-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence :
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
      hom-fibration-boundary-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence :
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
      hom-boundary-fiber-inclusion-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence :
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
      is-exact-fiber-inclusion-fibration-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence :
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
          ( hom-fiber-inclusion-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence
            ( n))
          ( hom-fibration-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence
            ( n))
      is-exact-fibration-boundary-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence :
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
          ( hom-fibration-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence
            ( succ-ℕ n))
          ( hom-fibration-boundary-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence
            ( n))
      is-exact-boundary-fiber-inclusion-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence :
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
          ( hom-boundary-fiber-inclusion-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence
            ( n))
          ( hom-fiber-inclusion-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence
            ( n))

  open Set-Truncated-Canonical-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence
    public
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

  is-exact-set-truncation-loop-canonical-iterated-boundary-fiber-sequence-first-loop-signed :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω (Ω (total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω (Ω (base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω (fiber-fiber-sequence-Pointed-Type S)))
      ( hom-trunc-iterated-loop-fibration-fiber-sequence 1)
      ( hom-trunc-loop-canonical-iterated-boundary-fiber-sequence zero-ℕ)
  is-exact-set-truncation-loop-canonical-iterated-boundary-fiber-sequence-first-loop-signed =
    is-exact-hom-Pointed-Set-image-kernel-shift-right-inverse
      ( trunc-Pointed-Set
        ( Ω (Ω (total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω (Ω (base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω (fiber-fiber-sequence-Pointed-Type S)))
      ( hom-trunc-iterated-loop-fibration-fiber-sequence 1)
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence zero-ℕ)
      ( hom-trunc-loop-canonical-iterated-boundary-fiber-sequence zero-ℕ)
      ( hom-trunc-ap-inv-Ω-base-fiber-sequence)
      ( hom-trunc-inv-ap-inv-Ω-base-fiber-sequence)
      ( iff-image-hom-trunc-inv-ap-inv-Ω-base-fibration-fiber-sequence)
      ( coherence-square-first-loop-canonical-iterated-boundary-fiber-sequence-signed)
      ( is-section-hom-trunc-inv-ap-inv-Ω-base-fiber-sequence)
      ( is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence
        ( zero-ℕ))

  set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence :
    Set-Truncated-Canonical-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence
  set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence =
    make-Set-Truncated-Canonical-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence
      ( hom-trunc-iterated-loop-fiber-inclusion-fiber-sequence)
      ( hom-trunc-iterated-loop-fibration-fiber-sequence)
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence)
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence)
      ( is-exact-set-truncation-iterated-loop-fiber-sequence)
      ( is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence)
      ( is-exact-set-truncation-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence)

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
