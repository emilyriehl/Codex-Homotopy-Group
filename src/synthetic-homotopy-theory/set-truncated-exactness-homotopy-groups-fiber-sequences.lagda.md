# Set-truncated exactness of homotopy groups of fiber sequences

```agda
module synthetic-homotopy-theory.set-truncated-exactness-homotopy-groups-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equality-fibers-of-maps
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-set-truncation
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.exact-sequences-groups
open import group-theory.functoriality-homotopy-automorphism-groups
open import group-theory.homomorphisms-concrete-groups

open import structured-types.constant-pointed-maps
open import structured-types.exact-sequences-pointed-sets
open import structured-types.fiber-sequences
open import structured-types.fibers-of-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.whiskering-pointed-homotopies-composition

open import synthetic-homotopy-theory.connecting-fiber-sequences
open import synthetic-homotopy-theory.fibers-boundary-maps-pointed-maps
open import synthetic-homotopy-theory.fiber-sequences-fiber-inclusions
open import synthetic-homotopy-theory.functoriality-homotopy-groups
open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.long-exact-sequence-homotopy-groups
open import synthetic-homotopy-theory.loop-spaces-fibers-of-pointed-maps
open import synthetic-homotopy-theory.loop-spaces-pointed-equivalences
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.reassociation-iterated-loop-spaces
```

</details>

## Idea

The **set-truncated exactness** layer of the homotopy long exact sequence
proves exactness of the adjacent pointed-set triples obtained from a pointed
fiber sequence. It is separated from the definition-level boundary and
homotopy-group maps so that those structural definitions can be reused without
also importing the proof-heavy exactness package.

## Properties

### Set-truncated canonical fiber sequences are exact

This is the first substantive step in the proof of the
[long exact sequence](#idea): the `0`-truncation of any adjacent canonical
fiber-projection triple

```text
  fiber g →∗ E →∗ B
```

is exact as a sequence of pointed sets.

```agda
module _
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B)
  where

  is-exact-set-truncation-fiber-sequence-Pointed-Type :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (fiber-Pointed-Type g))
      ( trunc-Pointed-Set E)
      ( trunc-Pointed-Set B)
      ( hom-trunc-Pointed-Set (inclusion-fiber-Pointed-Type g))
      ( hom-trunc-Pointed-Set g)
  is-exact-set-truncation-fiber-sequence-Pointed-Type =
    is-exact-trunc-fiber-inclusion-Pointed-Type g
```

### Set-truncated packaged fiber sequences are exact

The previous theorem is stated for the canonical fiber sequence of a pointed
map. For an arbitrary packaged fiber sequence, exactness follows by comparing
its fiber term with the canonical pointed fiber of its fibration.

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  hom-trunc-fiber-inclusion-fiber-sequence-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))
      ( trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S))
  hom-trunc-fiber-inclusion-fiber-sequence-Pointed-Type =
    hom-trunc-Pointed-Set (fiber-inclusion-fiber-sequence-Pointed-Type S)

  hom-trunc-fibration-fiber-sequence-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S))
      ( trunc-Pointed-Set (base-fiber-sequence-Pointed-Type S))
  hom-trunc-fibration-fiber-sequence-Pointed-Type =
    hom-trunc-Pointed-Set (fibration-fiber-sequence-Pointed-Type S)

  hom-trunc-canonical-fiber-inclusion-fiber-sequence-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set
        ( fiber-Pointed-Type (fibration-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S))
  hom-trunc-canonical-fiber-inclusion-fiber-sequence-Pointed-Type =
    hom-trunc-Pointed-Set
      ( inclusion-fiber-Pointed-Type (fibration-fiber-sequence-Pointed-Type S))

  is-in-image-trunc-canonical-fiber-inclusion-is-in-image-trunc-fiber-inclusion-fiber-sequence-Pointed-Type :
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S))) →
    is-in-image-hom-Pointed-Set
      {A = trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S)}
      {B = trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S)}
      hom-trunc-fiber-inclusion-fiber-sequence-Pointed-Type
      x →
    is-in-image-hom-Pointed-Set
      {A =
        trunc-Pointed-Set
          ( fiber-Pointed-Type (fibration-fiber-sequence-Pointed-Type S))}
      {B = trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S)}
      hom-trunc-canonical-fiber-inclusion-fiber-sequence-Pointed-Type
      x
  is-in-image-trunc-canonical-fiber-inclusion-is-in-image-trunc-fiber-inclusion-fiber-sequence-Pointed-Type
    x H =
    apply-universal-property-trunc-Prop H
      ( subtype-image-hom-Pointed-Set
        {A =
          trunc-Pointed-Set
            ( fiber-Pointed-Type (fibration-fiber-sequence-Pointed-Type S))}
        {B = trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S)}
        ( hom-trunc-canonical-fiber-inclusion-fiber-sequence-Pointed-Type)
        ( x))
      ( λ (t , p) →
        apply-dependent-universal-property-trunc-Set'
          ( λ t' →
            function-Set
              ( map-pointed-map
                hom-trunc-fiber-inclusion-fiber-sequence-Pointed-Type
                t' ＝ x)
              ( set-Prop
                ( subtype-image-hom-Pointed-Set
                  {A =
                    trunc-Pointed-Set
                      ( fiber-Pointed-Type
                        ( fibration-fiber-sequence-Pointed-Type S))}
                  {B =
                    trunc-Pointed-Set
                      ( total-space-fiber-sequence-Pointed-Type S)}
                  ( hom-trunc-canonical-fiber-inclusion-fiber-sequence-Pointed-Type)
                  ( x))))
          ( λ q p' →
            unit-trunc-Prop
              ( unit-trunc-Set
                ( map-pointed-map
                  ( pointed-map-fiber-fiber-sequence-Pointed-Type S)
                  ( q)) ,
                ( naturality-unit-trunc-Set
                  ( map-pointed-map
                    ( inclusion-fiber-Pointed-Type
                      ( fibration-fiber-sequence-Pointed-Type S)))
                  ( map-pointed-map
                    ( pointed-map-fiber-fiber-sequence-Pointed-Type S)
                    ( q))) ∙
                ( ap
                  ( unit-trunc-Set)
                  ( inv
                    ( pr1
                      ( pointed-htpy-fiber-inclusion-fiber-sequence-Pointed-Type S)
                      ( q)))) ∙
                ( inv
                  ( naturality-unit-trunc-Set
                    ( map-pointed-map
                      ( fiber-inclusion-fiber-sequence-Pointed-Type S))
                    ( q))) ∙
                ( p')))
          ( t)
          ( p))

  is-in-image-trunc-fiber-inclusion-is-in-image-trunc-canonical-fiber-inclusion-fiber-sequence-Pointed-Type :
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S))) →
    is-in-image-hom-Pointed-Set
      {A =
        trunc-Pointed-Set
          ( fiber-Pointed-Type (fibration-fiber-sequence-Pointed-Type S))}
      {B = trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S)}
      hom-trunc-canonical-fiber-inclusion-fiber-sequence-Pointed-Type
      x →
    is-in-image-hom-Pointed-Set
      {A = trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S)}
      {B = trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S)}
      hom-trunc-fiber-inclusion-fiber-sequence-Pointed-Type
      x
  is-in-image-trunc-fiber-inclusion-is-in-image-trunc-canonical-fiber-inclusion-fiber-sequence-Pointed-Type
    x H =
    apply-universal-property-trunc-Prop H
      ( subtype-image-hom-Pointed-Set
        {A = trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S)}
        {B = trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S)}
        ( hom-trunc-fiber-inclusion-fiber-sequence-Pointed-Type)
        ( x))
      ( λ (t , p) →
        apply-dependent-universal-property-trunc-Set'
          ( λ t' →
            function-Set
              ( map-pointed-map
                hom-trunc-canonical-fiber-inclusion-fiber-sequence-Pointed-Type
                t' ＝ x)
              ( set-Prop
                ( subtype-image-hom-Pointed-Set
                  {A = trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S)}
                  {B =
                    trunc-Pointed-Set
                      ( total-space-fiber-sequence-Pointed-Type S)}
                  ( hom-trunc-fiber-inclusion-fiber-sequence-Pointed-Type)
                  ( x))))
          ( λ q p' →
            unit-trunc-Prop
              ( unit-trunc-Set
                ( map-pointed-map
                  ( pointed-map-inv-pointed-equiv
                    ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))
                  ( q)) ,
                ( naturality-unit-trunc-Set
                  ( map-pointed-map
                    ( fiber-inclusion-fiber-sequence-Pointed-Type S))
                  ( map-pointed-map
                    ( pointed-map-inv-pointed-equiv
                      ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))
                    ( q))) ∙
                ( ap
                  ( unit-trunc-Set)
                  ( pr1
                    ( pointed-htpy-fiber-inclusion-fiber-sequence-Pointed-Type S)
                    ( map-pointed-map
                      ( pointed-map-inv-pointed-equiv
                        ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))
                      ( q)))) ∙
                ( inv
                  ( naturality-unit-trunc-Set
                    ( map-pointed-map
                      ( inclusion-fiber-Pointed-Type
                        ( fibration-fiber-sequence-Pointed-Type S)))
                    ( map-pointed-map
                      ( pointed-map-pointed-equiv
                        ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))
                      ( map-pointed-map
                        ( pointed-map-inv-pointed-equiv
                          ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))
                        ( q))))) ∙
                ( ap
                  ( map-pointed-map
                    ( hom-trunc-canonical-fiber-inclusion-fiber-sequence-Pointed-Type))
                  ( ap
                    ( unit-trunc-Set)
                    ( is-section-map-inv-equiv
                      ( equiv-pointed-equiv
                        ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))
                      ( q)))) ∙
                ( p')))
          ( t)
          ( p))

  is-exact-set-truncation-fiber-sequence :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))
      ( trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S))
      ( trunc-Pointed-Set (base-fiber-sequence-Pointed-Type S))
      ( hom-trunc-fiber-inclusion-fiber-sequence-Pointed-Type)
      ( hom-trunc-fibration-fiber-sequence-Pointed-Type)
  pr1 (is-exact-set-truncation-fiber-sequence x) H =
    pr1
      ( is-exact-set-truncation-fiber-sequence-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S)
        ( x))
      ( is-in-image-trunc-canonical-fiber-inclusion-is-in-image-trunc-fiber-inclusion-fiber-sequence-Pointed-Type
        ( x)
        ( H))
  pr2 (is-exact-set-truncation-fiber-sequence x) H =
    is-in-image-trunc-fiber-inclusion-is-in-image-trunc-canonical-fiber-inclusion-fiber-sequence-Pointed-Type
      ( x)
      ( pr2
        ( is-exact-set-truncation-fiber-sequence-Pointed-Type
          ( fibration-fiber-sequence-Pointed-Type S)
          ( x))
        ( H))
```


### The next set-truncated fiber sequence is exact

The next adjacent triple in the fiber sequence of `g` is

```text
  Ω B →∗ fiber g →∗ E.
```

Using the first fiber-of-the-fiber identification above, its set truncation is
exact by comparison with the canonical fiber sequence of the pointed map
`fiber g →∗ E`.

```agda
module _
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B)
  where

  hom-trunc-boundary-fiber-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set (Ω B))
      ( trunc-Pointed-Set (fiber-Pointed-Type g))
  hom-trunc-boundary-fiber-Pointed-Type =
    hom-trunc-Pointed-Set (boundary-fiber-Pointed-Type g)

  hom-trunc-inclusion-fiber-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set (fiber-Pointed-Type g))
      ( trunc-Pointed-Set E)
  hom-trunc-inclusion-fiber-Pointed-Type =
    hom-trunc-Pointed-Set (inclusion-fiber-Pointed-Type g)

  hom-trunc-inclusion-fiber-inclusion-fiber-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set
        ( fiber-Pointed-Type (inclusion-fiber-Pointed-Type g)))
      ( trunc-Pointed-Set (fiber-Pointed-Type g))
  hom-trunc-inclusion-fiber-inclusion-fiber-Pointed-Type =
    hom-trunc-Pointed-Set
      ( inclusion-fiber-Pointed-Type (inclusion-fiber-Pointed-Type g))

  is-in-image-trunc-inclusion-fiber-is-in-image-trunc-boundary-fiber-Pointed-Type :
    (x : type-Pointed-Set (trunc-Pointed-Set (fiber-Pointed-Type g))) →
    is-in-image-hom-Pointed-Set
      {A = trunc-Pointed-Set (Ω B)}
      {B = trunc-Pointed-Set (fiber-Pointed-Type g)}
      hom-trunc-boundary-fiber-Pointed-Type
      x →
    is-in-image-hom-Pointed-Set
      {A =
        trunc-Pointed-Set
          ( fiber-Pointed-Type (inclusion-fiber-Pointed-Type g))}
      {B = trunc-Pointed-Set (fiber-Pointed-Type g)}
      hom-trunc-inclusion-fiber-inclusion-fiber-Pointed-Type
      x
  is-in-image-trunc-inclusion-fiber-is-in-image-trunc-boundary-fiber-Pointed-Type
    x H =
    apply-universal-property-trunc-Prop H
      ( subtype-image-hom-Pointed-Set
        {A =
          trunc-Pointed-Set
            ( fiber-Pointed-Type (inclusion-fiber-Pointed-Type g))}
        {B = trunc-Pointed-Set (fiber-Pointed-Type g)}
        ( hom-trunc-inclusion-fiber-inclusion-fiber-Pointed-Type)
        ( x))
      ( λ (t , p) →
        apply-dependent-universal-property-trunc-Set'
          ( λ t' →
            function-Set
              ( map-pointed-map hom-trunc-boundary-fiber-Pointed-Type t' ＝ x)
              ( set-Prop
                ( subtype-image-hom-Pointed-Set
                  {A =
                    trunc-Pointed-Set
                      ( fiber-Pointed-Type (inclusion-fiber-Pointed-Type g))}
                  {B = trunc-Pointed-Set (fiber-Pointed-Type g)}
                  ( hom-trunc-inclusion-fiber-inclusion-fiber-Pointed-Type)
                  ( x))))
          ( λ q p' →
            unit-trunc-Prop
              ( unit-trunc-Set
                ( map-pointed-map
                  ( pointed-map-pointed-equiv
                    ( pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type
                      ( g)))
                  ( q)) ,
                ( naturality-unit-trunc-Set
                  ( map-pointed-map
                    ( inclusion-fiber-Pointed-Type
                      ( inclusion-fiber-Pointed-Type g)))
                  ( map-pointed-map
                    ( pointed-map-pointed-equiv
                      ( pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type
                        ( g)))
                    ( q))) ∙
                ( ap
                  ( unit-trunc-Set)
                  ( inv
                    ( pr1
                      ( pointed-htpy-boundary-fiber-inclusion-boundary-fiber-Pointed-Type
                        ( g))
                      ( q)))) ∙
                ( inv
                  ( naturality-unit-trunc-Set
                    ( map-pointed-map (boundary-fiber-Pointed-Type g))
                    ( q))) ∙
                ( p')))
          ( t)
          ( p))

  is-in-image-trunc-boundary-fiber-is-in-image-trunc-inclusion-fiber-Pointed-Type :
    (x : type-Pointed-Set (trunc-Pointed-Set (fiber-Pointed-Type g))) →
    is-in-image-hom-Pointed-Set
      {A =
        trunc-Pointed-Set
          ( fiber-Pointed-Type (inclusion-fiber-Pointed-Type g))}
      {B = trunc-Pointed-Set (fiber-Pointed-Type g)}
      hom-trunc-inclusion-fiber-inclusion-fiber-Pointed-Type
      x →
    is-in-image-hom-Pointed-Set
      {A = trunc-Pointed-Set (Ω B)}
      {B = trunc-Pointed-Set (fiber-Pointed-Type g)}
      hom-trunc-boundary-fiber-Pointed-Type
      x
  is-in-image-trunc-boundary-fiber-is-in-image-trunc-inclusion-fiber-Pointed-Type
    x H =
    apply-universal-property-trunc-Prop H
      ( subtype-image-hom-Pointed-Set
        {A = trunc-Pointed-Set (Ω B)}
        {B = trunc-Pointed-Set (fiber-Pointed-Type g)}
        ( hom-trunc-boundary-fiber-Pointed-Type)
        ( x))
      ( λ (t , p) →
        apply-dependent-universal-property-trunc-Set'
          ( λ t' →
            function-Set
              ( map-pointed-map
                hom-trunc-inclusion-fiber-inclusion-fiber-Pointed-Type
                t' ＝ x)
              ( set-Prop
                ( subtype-image-hom-Pointed-Set
                  {A = trunc-Pointed-Set (Ω B)}
                  {B = trunc-Pointed-Set (fiber-Pointed-Type g)}
                  ( hom-trunc-boundary-fiber-Pointed-Type)
                  ( x))))
          ( λ q p' →
            unit-trunc-Prop
              ( unit-trunc-Set
                ( map-pointed-map
                  ( pointed-map-inv-pointed-equiv
                    ( pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type
                      ( g)))
                  ( q)) ,
                ( naturality-unit-trunc-Set
                  ( map-pointed-map (boundary-fiber-Pointed-Type g))
                  ( map-pointed-map
                    ( pointed-map-inv-pointed-equiv
                      ( pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type
                        ( g)))
                    ( q))) ∙
                ( ap
                  ( unit-trunc-Set)
                  ( pr1
                    ( pointed-htpy-boundary-fiber-inclusion-boundary-fiber-Pointed-Type
                      ( g))
                    ( map-pointed-map
                      ( pointed-map-inv-pointed-equiv
                        ( pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type
                          ( g)))
                      ( q)))) ∙
                ( inv
                  ( naturality-unit-trunc-Set
                    ( map-pointed-map
                      ( inclusion-fiber-Pointed-Type
                        ( inclusion-fiber-Pointed-Type g)))
                    ( map-pointed-map
                      ( pointed-map-pointed-equiv
                        ( pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type
                          ( g)))
                      ( map-pointed-map
                        ( pointed-map-inv-pointed-equiv
                          ( pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type
                            ( g)))
                        ( q))))) ∙
                ( ap
                  ( map-pointed-map
                    ( hom-trunc-inclusion-fiber-inclusion-fiber-Pointed-Type))
                  ( ap
                    ( unit-trunc-Set)
                    ( is-section-map-inv-equiv
                      ( equiv-fiber-inclusion-boundary-fiber-Pointed-Type g)
                      ( q)))) ∙
                ( p')))
          ( t)
          ( p))

  is-exact-set-truncation-boundary-fiber-sequence-Pointed-Type :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (Ω B))
      ( trunc-Pointed-Set (fiber-Pointed-Type g))
      ( trunc-Pointed-Set E)
      ( hom-trunc-boundary-fiber-Pointed-Type)
      ( hom-trunc-inclusion-fiber-Pointed-Type)
  pr1 (is-exact-set-truncation-boundary-fiber-sequence-Pointed-Type x) H =
    pr1
      ( is-exact-set-truncation-fiber-sequence-Pointed-Type
        ( inclusion-fiber-Pointed-Type g)
        ( x))
      ( is-in-image-trunc-inclusion-fiber-is-in-image-trunc-boundary-fiber-Pointed-Type
        ( x)
        ( H))
  pr2 (is-exact-set-truncation-boundary-fiber-sequence-Pointed-Type x) H =
    is-in-image-trunc-boundary-fiber-is-in-image-trunc-inclusion-fiber-Pointed-Type
      ( x)
      ( pr2
        ( is-exact-set-truncation-fiber-sequence-Pointed-Type
          ( inclusion-fiber-Pointed-Type g)
          ( x))
        ( H))

  hom-trunc-loop-map-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set (Ω E))
      ( trunc-Pointed-Set (Ω B))
  hom-trunc-loop-map-Pointed-Type =
    hom-trunc-Pointed-Set (pointed-map-Ω g)

  is-exact-set-truncation-boundary-map-Ω-direct-Pointed-Type :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (Ω E))
      ( trunc-Pointed-Set (Ω B))
      ( trunc-Pointed-Set (fiber-Pointed-Type g))
      ( hom-trunc-loop-map-Pointed-Type)
      ( hom-trunc-boundary-fiber-Pointed-Type)
  is-exact-set-truncation-boundary-map-Ω-direct-Pointed-Type =
    is-exact-set-truncation-fiber-sequence
      ( fiber-sequence-boundary-map-Ω-direct-Pointed-Type g)

  is-exact-set-truncation-loop-boundary-fiber-sequence-Pointed-Type :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (Ω E))
      ( trunc-Pointed-Set (Ω B))
      ( trunc-Pointed-Set (fiber-Pointed-Type g))
      ( hom-trunc-loop-map-Pointed-Type)
      ( hom-trunc-boundary-fiber-Pointed-Type)
  is-exact-set-truncation-loop-boundary-fiber-sequence-Pointed-Type =
    is-exact-set-truncation-boundary-map-Ω-direct-Pointed-Type
```

### Set-truncated boundary sequences of packaged fiber sequences are exact

The preceding boundary exactness theorem is stated for the canonical fiber of a
pointed map. For a packaged fiber sequence, the boundary map lands in its
chosen fiber term. Exactness follows by transporting the canonical boundary
exactness across the pointed equivalence with the canonical fiber.

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  hom-trunc-boundary-fiber-sequence-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))
  hom-trunc-boundary-fiber-sequence-Pointed-Type =
    hom-trunc-Pointed-Set (boundary-pointed-map-fiber-sequence S)

  hom-trunc-pointed-map-fiber-fiber-sequence-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))
      ( trunc-Pointed-Set
        ( fiber-Pointed-Type (fibration-fiber-sequence-Pointed-Type S)))
  hom-trunc-pointed-map-fiber-fiber-sequence-Pointed-Type =
    hom-trunc-Pointed-Set (pointed-map-fiber-fiber-sequence-Pointed-Type S)

  hom-trunc-inv-pointed-map-fiber-fiber-sequence-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set
        ( fiber-Pointed-Type (fibration-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))
  hom-trunc-inv-pointed-map-fiber-fiber-sequence-Pointed-Type =
    hom-trunc-Pointed-Set
      ( pointed-map-inv-pointed-equiv
        ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))

  eq-map-hom-trunc-pointed-map-boundary-fiber-sequence-Pointed-Type :
    (t :
      type-Pointed-Set
        ( trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S)))) →
    map-pointed-map hom-trunc-pointed-map-fiber-fiber-sequence-Pointed-Type
      ( map-pointed-map hom-trunc-boundary-fiber-sequence-Pointed-Type t) ＝
    map-pointed-map
      ( hom-trunc-boundary-fiber-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))
      ( t)
  eq-map-hom-trunc-pointed-map-boundary-fiber-sequence-Pointed-Type =
    apply-dependent-universal-property-trunc-Set'
      ( λ t →
        set-Prop
          ( Id-Prop
            ( trunc-Set
              ( type-Pointed-Type
                ( fiber-Pointed-Type
                  ( fibration-fiber-sequence-Pointed-Type S))))
            ( map-pointed-map
              hom-trunc-pointed-map-fiber-fiber-sequence-Pointed-Type
              ( map-pointed-map
                hom-trunc-boundary-fiber-sequence-Pointed-Type
                t))
            ( map-pointed-map
              ( hom-trunc-boundary-fiber-Pointed-Type
                ( fibration-fiber-sequence-Pointed-Type S))
              ( t))))
      ( λ q →
        ( ap
          ( map-pointed-map
            hom-trunc-pointed-map-fiber-fiber-sequence-Pointed-Type)
          ( naturality-unit-trunc-Set
            ( map-pointed-map (boundary-pointed-map-fiber-sequence S))
            ( q))) ∙
        ( naturality-unit-trunc-Set
          ( map-pointed-map (pointed-map-fiber-fiber-sequence-Pointed-Type S))
          ( map-pointed-map (boundary-pointed-map-fiber-sequence S) q)) ∙
        ( ap
          ( unit-trunc-Set)
          ( is-section-map-inv-equiv
            ( equiv-pointed-equiv
              ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))
            ( map-pointed-map
              ( boundary-fiber-Pointed-Type
                ( fibration-fiber-sequence-Pointed-Type S))
              ( q)))) ∙
        ( inv
          ( naturality-unit-trunc-Set
            ( map-pointed-map
              ( boundary-fiber-Pointed-Type
                ( fibration-fiber-sequence-Pointed-Type S)))
            ( q))))

  is-retraction-hom-trunc-inv-pointed-map-fiber-fiber-sequence-Pointed-Type :
    (x : type-Pointed-Set (trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))) →
    map-pointed-map hom-trunc-inv-pointed-map-fiber-fiber-sequence-Pointed-Type
      ( map-pointed-map hom-trunc-pointed-map-fiber-fiber-sequence-Pointed-Type x) ＝
    x
  is-retraction-hom-trunc-inv-pointed-map-fiber-fiber-sequence-Pointed-Type =
    apply-dependent-universal-property-trunc-Set'
      ( λ x →
        set-Prop
          ( Id-Prop
            ( trunc-Set (type-Pointed-Type (fiber-fiber-sequence-Pointed-Type S)))
            ( map-pointed-map
              hom-trunc-inv-pointed-map-fiber-fiber-sequence-Pointed-Type
              ( map-pointed-map
                hom-trunc-pointed-map-fiber-fiber-sequence-Pointed-Type
                x))
            ( x)))
      ( λ x →
        ( ap
          ( map-pointed-map
            hom-trunc-inv-pointed-map-fiber-fiber-sequence-Pointed-Type)
          ( naturality-unit-trunc-Set
            ( map-pointed-map (pointed-map-fiber-fiber-sequence-Pointed-Type S))
            ( x))) ∙
        ( naturality-unit-trunc-Set
          ( map-pointed-map
            ( pointed-map-inv-pointed-equiv
              ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S)))
          ( map-pointed-map (pointed-map-fiber-fiber-sequence-Pointed-Type S) x)) ∙
        ( ap
          ( unit-trunc-Set)
          ( is-retraction-map-inv-equiv
            ( equiv-pointed-equiv
              ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))
            ( x))))

  eq-map-hom-trunc-fiber-inclusion-fiber-sequence-Pointed-Type :
    (x : type-Pointed-Set (trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))) →
    map-pointed-map
      ( hom-trunc-fiber-inclusion-fiber-sequence-Pointed-Type S)
      ( x) ＝
    map-pointed-map
      ( hom-trunc-canonical-fiber-inclusion-fiber-sequence-Pointed-Type S)
      ( map-pointed-map
        hom-trunc-pointed-map-fiber-fiber-sequence-Pointed-Type
        x)
  eq-map-hom-trunc-fiber-inclusion-fiber-sequence-Pointed-Type =
    apply-dependent-universal-property-trunc-Set'
      ( λ x →
        set-Prop
          ( Id-Prop
            ( trunc-Set
              ( type-Pointed-Type (total-space-fiber-sequence-Pointed-Type S)))
            ( map-pointed-map
              ( hom-trunc-fiber-inclusion-fiber-sequence-Pointed-Type S)
              ( x))
            ( map-pointed-map
              ( hom-trunc-canonical-fiber-inclusion-fiber-sequence-Pointed-Type S)
              ( map-pointed-map
                hom-trunc-pointed-map-fiber-fiber-sequence-Pointed-Type
                x))))
      ( λ x →
        ( naturality-unit-trunc-Set
          ( map-pointed-map (fiber-inclusion-fiber-sequence-Pointed-Type S))
          ( x)) ∙
        ( ap
          ( unit-trunc-Set)
          ( pr1
            ( pointed-htpy-fiber-inclusion-fiber-sequence-Pointed-Type S)
            ( x))) ∙
        ( inv
          ( naturality-unit-trunc-Set
            ( map-pointed-map
              ( inclusion-fiber-Pointed-Type
                ( fibration-fiber-sequence-Pointed-Type S)))
            ( map-pointed-map (pointed-map-fiber-fiber-sequence-Pointed-Type S) x))) ∙
        ( ap
          ( map-pointed-map
            ( hom-trunc-canonical-fiber-inclusion-fiber-sequence-Pointed-Type S))
          ( inv
            ( naturality-unit-trunc-Set
              ( map-pointed-map (pointed-map-fiber-fiber-sequence-Pointed-Type S))
              ( x)))))

  is-in-image-trunc-canonical-boundary-is-in-image-trunc-boundary-fiber-sequence-Pointed-Type :
    (x : type-Pointed-Set (trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))) →
    is-in-image-hom-Pointed-Set
      {A = trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S))}
      {B = trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S)}
      hom-trunc-boundary-fiber-sequence-Pointed-Type
      x →
    is-in-image-hom-Pointed-Set
      {A = trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S))}
      {B =
        trunc-Pointed-Set
          ( fiber-Pointed-Type (fibration-fiber-sequence-Pointed-Type S))}
      ( hom-trunc-boundary-fiber-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))
      ( map-pointed-map
        hom-trunc-pointed-map-fiber-fiber-sequence-Pointed-Type
        x)
  is-in-image-trunc-canonical-boundary-is-in-image-trunc-boundary-fiber-sequence-Pointed-Type
    x H =
    apply-universal-property-trunc-Prop H
      ( subtype-image-hom-Pointed-Set
        {A = trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S))}
        {B =
          trunc-Pointed-Set
            ( fiber-Pointed-Type (fibration-fiber-sequence-Pointed-Type S))}
        ( hom-trunc-boundary-fiber-Pointed-Type
          ( fibration-fiber-sequence-Pointed-Type S))
        ( map-pointed-map
          hom-trunc-pointed-map-fiber-fiber-sequence-Pointed-Type
          x))
      ( λ (t , p) →
        unit-trunc-Prop
          ( t ,
            ( inv
              ( eq-map-hom-trunc-pointed-map-boundary-fiber-sequence-Pointed-Type
                ( t))) ∙
            ( ap
              ( map-pointed-map
                hom-trunc-pointed-map-fiber-fiber-sequence-Pointed-Type)
              ( p))))

  is-in-image-trunc-boundary-is-in-image-trunc-canonical-boundary-fiber-sequence-Pointed-Type :
    (x : type-Pointed-Set (trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))) →
    is-in-image-hom-Pointed-Set
      {A = trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S))}
      {B =
        trunc-Pointed-Set
          ( fiber-Pointed-Type (fibration-fiber-sequence-Pointed-Type S))}
      ( hom-trunc-boundary-fiber-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))
      ( map-pointed-map
        hom-trunc-pointed-map-fiber-fiber-sequence-Pointed-Type
        x) →
    is-in-image-hom-Pointed-Set
      {A = trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S))}
      {B = trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S)}
      hom-trunc-boundary-fiber-sequence-Pointed-Type
      x
  is-in-image-trunc-boundary-is-in-image-trunc-canonical-boundary-fiber-sequence-Pointed-Type
    x H =
    apply-universal-property-trunc-Prop H
      ( subtype-image-hom-Pointed-Set
        {A = trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S))}
        {B = trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S)}
        ( hom-trunc-boundary-fiber-sequence-Pointed-Type)
        ( x))
      ( λ (t , p) →
        unit-trunc-Prop
          ( t ,
            ( inv
              ( is-retraction-hom-trunc-inv-pointed-map-fiber-fiber-sequence-Pointed-Type
                ( map-pointed-map hom-trunc-boundary-fiber-sequence-Pointed-Type t))) ∙
            ( ap
              ( map-pointed-map
                hom-trunc-inv-pointed-map-fiber-fiber-sequence-Pointed-Type)
              ( eq-map-hom-trunc-pointed-map-boundary-fiber-sequence-Pointed-Type
                ( t) ∙ p)) ∙
            ( is-retraction-hom-trunc-inv-pointed-map-fiber-fiber-sequence-Pointed-Type
              ( x))))

  is-exact-set-truncation-boundary-fiber-sequence :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))
      ( trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S))
      ( hom-trunc-boundary-fiber-sequence-Pointed-Type)
      ( hom-trunc-fiber-inclusion-fiber-sequence-Pointed-Type S)
  pr1 (is-exact-set-truncation-boundary-fiber-sequence x) H =
    ( eq-map-hom-trunc-fiber-inclusion-fiber-sequence-Pointed-Type x) ∙
    ( pr1
      ( is-exact-set-truncation-boundary-fiber-sequence-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S)
        ( map-pointed-map
          hom-trunc-pointed-map-fiber-fiber-sequence-Pointed-Type
          x))
      ( is-in-image-trunc-canonical-boundary-is-in-image-trunc-boundary-fiber-sequence-Pointed-Type
        ( x)
        ( H)))
  pr2 (is-exact-set-truncation-boundary-fiber-sequence x) H =
    is-in-image-trunc-boundary-is-in-image-trunc-canonical-boundary-fiber-sequence-Pointed-Type
      ( x)
      ( pr2
        ( is-exact-set-truncation-boundary-fiber-sequence-Pointed-Type
          ( fibration-fiber-sequence-Pointed-Type S)
          ( map-pointed-map
            hom-trunc-pointed-map-fiber-fiber-sequence-Pointed-Type
            x))
        ( ( inv (eq-map-hom-trunc-fiber-inclusion-fiber-sequence-Pointed-Type x)) ∙
          ( H)))
```


### Set-truncated loop-boundary sequences of packaged fiber sequences are exact

The direct `connect_fiberseq` package identifies the adjacent segment one step
to the left as a packaged pointed fiber sequence. Its set truncation is therefore
exact by the generic exactness theorem for packaged fiber sequences.

```agda
  hom-trunc-loop-fibration-fiber-sequence-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set (Ω (total-space-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S)))
  hom-trunc-loop-fibration-fiber-sequence-Pointed-Type =
    hom-trunc-Pointed-Set
      ( pointed-map-Ω (fibration-fiber-sequence-Pointed-Type S))

  is-exact-set-truncation-boundary-fiber-sequence-direct :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (Ω (total-space-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))
      ( hom-trunc-loop-fibration-fiber-sequence-Pointed-Type)
      ( hom-trunc-boundary-fiber-sequence-Pointed-Type)
  is-exact-set-truncation-boundary-fiber-sequence-direct =
    is-exact-set-truncation-fiber-sequence
      ( fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type S)

  is-exact-set-truncation-loop-boundary-fiber-sequence :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (Ω (total-space-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))
      ( hom-trunc-loop-fibration-fiber-sequence-Pointed-Type)
      ( hom-trunc-boundary-fiber-sequence-Pointed-Type)
  is-exact-set-truncation-loop-boundary-fiber-sequence =
    is-exact-set-truncation-boundary-fiber-sequence-direct
```


### Set-truncated looped packaged fiber sequences are exact

The next adjacent segment is obtained by looping the two maps in the packaged
fiber sequence. This is itself the set truncation of the iterated-loop fiber
sequence `iterated-loop-fiber-sequence S (succ-ℕ zero-ℕ)`, so exactness follows
from the generic exactness theorem for packaged fiber sequences.

```agda
  hom-trunc-loop-fiber-inclusion-fiber-sequence-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set (Ω (fiber-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (Ω (total-space-fiber-sequence-Pointed-Type S)))
  hom-trunc-loop-fiber-inclusion-fiber-sequence-Pointed-Type =
    hom-trunc-Pointed-Set
      ( pointed-map-Ω (fiber-inclusion-fiber-sequence-Pointed-Type S))

  is-exact-set-truncation-loop-fiber-sequence-direct :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (Ω (fiber-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (Ω (total-space-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S)))
      ( hom-trunc-loop-fiber-inclusion-fiber-sequence-Pointed-Type)
      ( hom-trunc-loop-fibration-fiber-sequence-Pointed-Type)
  is-exact-set-truncation-loop-fiber-sequence-direct =
    is-exact-set-truncation-fiber-sequence
      ( iterated-loop-fiber-sequence S (succ-ℕ zero-ℕ))

  is-exact-set-truncation-loop-fiber-sequence :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (Ω (fiber-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (Ω (total-space-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S)))
      ( hom-trunc-loop-fiber-inclusion-fiber-sequence-Pointed-Type)
      ( hom-trunc-loop-fibration-fiber-sequence-Pointed-Type)
  is-exact-set-truncation-loop-fiber-sequence =
    is-exact-set-truncation-loop-fiber-sequence-direct

```


### Initial set-truncated long exact sequence segments are exact

The preceding four exactness theorems assemble the first four adjacent triples of
the long exact sequence associated to a packaged pointed fiber sequence.

```agda
  initial-segment-is-exact-set-truncation-fiber-sequence :
    Σ ( is-exact-hom-Pointed-Set
        ( trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))
        ( trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S))
        ( trunc-Pointed-Set (base-fiber-sequence-Pointed-Type S))
        ( hom-trunc-fiber-inclusion-fiber-sequence-Pointed-Type S)
        ( hom-trunc-fibration-fiber-sequence-Pointed-Type S))
      ( λ _ →
        Σ ( is-exact-hom-Pointed-Set
            ( trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S)))
            ( trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))
            ( trunc-Pointed-Set (total-space-fiber-sequence-Pointed-Type S))
            ( hom-trunc-boundary-fiber-sequence-Pointed-Type)
            ( hom-trunc-fiber-inclusion-fiber-sequence-Pointed-Type S))
          ( λ _ →
            Σ ( is-exact-hom-Pointed-Set
                ( trunc-Pointed-Set
                  ( Ω (total-space-fiber-sequence-Pointed-Type S)))
                ( trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S)))
                ( trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))
                ( hom-trunc-loop-fibration-fiber-sequence-Pointed-Type)
                ( hom-trunc-boundary-fiber-sequence-Pointed-Type))
              ( λ _ →
                is-exact-hom-Pointed-Set
                  ( trunc-Pointed-Set
                    ( Ω (fiber-fiber-sequence-Pointed-Type S)))
                  ( trunc-Pointed-Set
                    ( Ω (total-space-fiber-sequence-Pointed-Type S)))
                  ( trunc-Pointed-Set
                    ( Ω (base-fiber-sequence-Pointed-Type S)))
                  ( hom-trunc-loop-fiber-inclusion-fiber-sequence-Pointed-Type)
                  ( hom-trunc-loop-fibration-fiber-sequence-Pointed-Type))))
  pr1 initial-segment-is-exact-set-truncation-fiber-sequence =
    is-exact-set-truncation-fiber-sequence S
  pr1 (pr2 initial-segment-is-exact-set-truncation-fiber-sequence) =
    is-exact-set-truncation-boundary-fiber-sequence
  pr1 (pr2 (pr2 initial-segment-is-exact-set-truncation-fiber-sequence)) =
    is-exact-set-truncation-loop-boundary-fiber-sequence
  pr2 (pr2 (pr2 initial-segment-is-exact-set-truncation-fiber-sequence)) =
    is-exact-set-truncation-loop-fiber-sequence
```



### Set-truncated looped boundary fiber sequences are exact

Applying the looped packaged exactness theorem to the boundary fiber sequence of
`g` gives the next canonical adjacent exact triple, with middle term the loop
space of the canonical fiber of `g`.

```agda
module _
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B)
  where

  hom-trunc-loop-boundary-boundary-fiber-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set (Ω (Ω B)))
      ( trunc-Pointed-Set (Ω (fiber-Pointed-Type g)))
  hom-trunc-loop-boundary-boundary-fiber-Pointed-Type =
    hom-trunc-loop-fiber-inclusion-fiber-sequence-Pointed-Type
      ( fiber-sequence-boundary-fiber-Pointed-Type g)

  hom-trunc-loop-inclusion-fiber-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set (Ω (fiber-Pointed-Type g)))
      ( trunc-Pointed-Set (Ω E))
  hom-trunc-loop-inclusion-fiber-Pointed-Type =
    hom-trunc-loop-fibration-fiber-sequence-Pointed-Type
      ( fiber-sequence-boundary-fiber-Pointed-Type g)

  is-exact-set-truncation-loop-boundary-boundary-fiber-sequence-Pointed-Type :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (Ω (Ω B)))
      ( trunc-Pointed-Set (Ω (fiber-Pointed-Type g)))
      ( trunc-Pointed-Set (Ω E))
      ( hom-trunc-loop-boundary-boundary-fiber-Pointed-Type)
      ( hom-trunc-loop-inclusion-fiber-Pointed-Type)
  is-exact-set-truncation-loop-boundary-boundary-fiber-sequence-Pointed-Type =
    is-exact-set-truncation-loop-fiber-sequence
      ( fiber-sequence-boundary-fiber-Pointed-Type g)
```

### Set-truncated looped boundary sequences of packaged fiber sequences are exact

The direct `connect_fiberseq` package for a fiber sequence identifies the
shifted adjacent triple

```text
  ΩΩ B →∗ Ω F →∗ Ω E
```

as the loop-boundary segment of the shifted fiber sequence
`Ω E →∗ Ω B →∗ F`. We record that direct shifted exactness theorem here. The
recursive loop-boundary exactness theorem below is still transported through
the canonical fiber of the fibration; the remaining upstream-quality comparison
is to identify the direct shifted boundary with the recursive looped fiber
inclusion by a K-safe inverse computation.

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  pointed-htpy-fiber-fiber-boundary-fiber-sequence :
    ( pointed-map-fiber-fiber-sequence-Pointed-Type S ∘∗
      boundary-pointed-map-fiber-sequence S) ~∗
    boundary-fiber-Pointed-Type
      ( fibration-fiber-sequence-Pointed-Type S)
  pointed-htpy-fiber-fiber-boundary-fiber-sequence =
    concat-pointed-htpy
      ( inv-associative-comp-pointed-map
        ( pointed-map-fiber-fiber-sequence-Pointed-Type S)
        ( pointed-map-inv-pointed-equiv
          ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))
        ( boundary-fiber-Pointed-Type
          ( fibration-fiber-sequence-Pointed-Type S)))
      ( concat-pointed-htpy
        ( right-whisker-comp-pointed-htpy
          ( pointed-map-fiber-fiber-sequence-Pointed-Type S ∘∗
            pointed-map-inv-pointed-equiv
              ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))
          ( id-pointed-map)
          ( is-pointed-section-pointed-map-inv-pointed-equiv
            ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))
          ( boundary-fiber-Pointed-Type
            ( fibration-fiber-sequence-Pointed-Type S)))
        ( left-unit-law-comp-pointed-map
          ( boundary-fiber-Pointed-Type
            ( fibration-fiber-sequence-Pointed-Type S))))

  hom-trunc-loop-boundary-fiber-sequence-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set (Ω (Ω (base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set (Ω (fiber-fiber-sequence-Pointed-Type S)))
  hom-trunc-loop-boundary-fiber-sequence-Pointed-Type =
    hom-trunc-Pointed-Set
      ( pointed-map-Ω (boundary-pointed-map-fiber-sequence S))

  hom-trunc-loop-pointed-map-fiber-fiber-sequence-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set (Ω (fiber-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set
        ( Ω
          ( fiber-Pointed-Type
            ( fibration-fiber-sequence-Pointed-Type S))))
  hom-trunc-loop-pointed-map-fiber-fiber-sequence-Pointed-Type =
    hom-trunc-Pointed-Set
      ( pointed-map-Ω
        ( pointed-map-fiber-fiber-sequence-Pointed-Type S))

  hom-trunc-boundary-boundary-fiber-sequence-direct-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set (Ω (fiber-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (Ω (total-space-fiber-sequence-Pointed-Type S)))
  hom-trunc-boundary-boundary-fiber-sequence-direct-Pointed-Type =
    hom-trunc-boundary-fiber-sequence-Pointed-Type
      ( fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type S)

  is-exact-set-truncation-loop-boundary-boundary-fiber-sequence-direct :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (Ω (Ω (base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set (Ω (fiber-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (Ω (total-space-fiber-sequence-Pointed-Type S)))
      ( hom-trunc-loop-boundary-fiber-sequence-Pointed-Type)
      ( hom-trunc-boundary-boundary-fiber-sequence-direct-Pointed-Type)
  is-exact-set-truncation-loop-boundary-boundary-fiber-sequence-direct =
    is-exact-set-truncation-loop-boundary-fiber-sequence
      ( fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type S)

  eq-map-Ω-fibration-map-Ω-fiber-inclusion-fiber-sequence-Pointed-Type :
    (q : type-Ω (fiber-fiber-sequence-Pointed-Type S)) →
    map-Ω (fibration-fiber-sequence-Pointed-Type S)
      ( map-Ω (fiber-inclusion-fiber-sequence-Pointed-Type S) q) ＝
    refl
  eq-map-Ω-fibration-map-Ω-fiber-inclusion-fiber-sequence-Pointed-Type q =
    ( inv
      ( preserves-comp-map-Ω
        ( fibration-fiber-sequence-Pointed-Type S)
        ( fiber-inclusion-fiber-sequence-Pointed-Type S)
        ( q))) ∙
    ( htpy-map-Ω
      ( fibration-fiber-sequence-Pointed-Type S ∘∗
        fiber-inclusion-fiber-sequence-Pointed-Type S)
      ( constant-pointed-map
        ( fiber-fiber-sequence-Pointed-Type S)
        ( base-fiber-sequence-Pointed-Type S))
      ( null-htpy-comp-fibration-fiber-inclusion-fiber-sequence-Pointed-Type S)
      ( q)) ∙
    ( eq-map-Ω-constant-pointed-map-Pointed-Type q)

  eq-pr1-map-equiv-fiber-boundary-fiber-sequence-direct-loop-fiber-inclusion :
    (q : type-Ω (fiber-fiber-sequence-Pointed-Type S)) →
    pr1
      ( map-equiv (equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type S)
        ( map-Ω (fiber-inclusion-fiber-sequence-Pointed-Type S) q)) ＝
    pr1
      ( map-pointed-map
        ( boundary-fiber-Pointed-Type (boundary-pointed-map-fiber-sequence S))
        ( q))
  eq-pr1-map-equiv-fiber-boundary-fiber-sequence-direct-loop-fiber-inclusion q =
    ( eq-map-Ω-fibration-map-Ω-fiber-inclusion-fiber-sequence-Pointed-Type q) ∙
    ( inv
      ( eq-pr1-boundary-fiber-Pointed-Type
        ( boundary-pointed-map-fiber-sequence S)
        ( q)))

  eq-map-Ω-fiber-inclusion-map-Ω-pointed-map-fiber-fiber-sequence-Pointed-Type :
    (q : type-Ω (fiber-fiber-sequence-Pointed-Type S)) →
    map-Ω (fiber-inclusion-fiber-sequence-Pointed-Type S) q ＝
    map-Ω
      ( inclusion-fiber-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))
      ( map-Ω (pointed-map-fiber-fiber-sequence-Pointed-Type S) q)
  eq-map-Ω-fiber-inclusion-map-Ω-pointed-map-fiber-fiber-sequence-Pointed-Type q =
    ( htpy-map-Ω
      ( fiber-inclusion-fiber-sequence-Pointed-Type S)
      ( inclusion-fiber-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S) ∘∗
        pointed-map-fiber-fiber-sequence-Pointed-Type S)
      ( pointed-htpy-fiber-inclusion-fiber-sequence-Pointed-Type S)
      ( q)) ∙
    ( preserves-comp-map-Ω
      ( inclusion-fiber-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))
      ( pointed-map-fiber-fiber-sequence-Pointed-Type S)
      ( q))

  eq-map-equiv-fiber-boundary-map-Ω-direct-loop-fiber-inclusion-fiber-sequence-Pointed-Type :
    (q : type-Ω (fiber-fiber-sequence-Pointed-Type S)) →
    map-equiv
      ( equiv-fiber-boundary-map-Ω-direct-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))
      ( map-Ω (fiber-inclusion-fiber-sequence-Pointed-Type S) q) ＝
    map-pointed-map
      ( boundary-fiber-Pointed-Type
        ( boundary-fiber-Pointed-Type
          ( fibration-fiber-sequence-Pointed-Type S)))
      ( map-Ω (pointed-map-fiber-fiber-sequence-Pointed-Type S) q)
  eq-map-equiv-fiber-boundary-map-Ω-direct-loop-fiber-inclusion-fiber-sequence-Pointed-Type q =
    ( ap
      ( map-equiv
        ( equiv-fiber-boundary-map-Ω-direct-Pointed-Type
          ( fibration-fiber-sequence-Pointed-Type S)))
      ( eq-map-Ω-fiber-inclusion-map-Ω-pointed-map-fiber-fiber-sequence-Pointed-Type q)) ∙
    ( eq-map-equiv-fiber-boundary-map-Ω-direct-loop-inclusion-fiber-Pointed-Type
      ( fibration-fiber-sequence-Pointed-Type S)
      ( map-Ω (pointed-map-fiber-fiber-sequence-Pointed-Type S) q))

  eq-map-equiv-fiber-boundary-fiber-sequence-direct-loop-fiber-inclusion-canonical-Pointed-Type :
    (q : type-Ω (fiber-fiber-sequence-Pointed-Type S)) →
    map-equiv (equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type S)
      ( map-Ω (fiber-inclusion-fiber-sequence-Pointed-Type S) q) ＝
    map-equiv
      ( equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type S)
      ( map-pointed-map
        ( boundary-fiber-Pointed-Type
          ( boundary-fiber-Pointed-Type
            ( fibration-fiber-sequence-Pointed-Type S)))
        ( map-Ω (pointed-map-fiber-fiber-sequence-Pointed-Type S) q))
  eq-map-equiv-fiber-boundary-fiber-sequence-direct-loop-fiber-inclusion-canonical-Pointed-Type q =
    ap
      ( map-equiv
        ( equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type S))
      ( eq-map-equiv-fiber-boundary-map-Ω-direct-loop-fiber-inclusion-fiber-sequence-Pointed-Type q)

  eq-pr1-map-equiv-fiber-canonical-boundary-boundary-fiber-sequence-boundary-boundary :
    (q : type-Ω (fiber-fiber-sequence-Pointed-Type S)) →
    pr1
      ( map-equiv
        ( equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type S)
        ( map-pointed-map
          ( boundary-fiber-Pointed-Type
            ( boundary-fiber-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S)))
          ( map-Ω (pointed-map-fiber-fiber-sequence-Pointed-Type S) q))) ＝
    pr1
      ( map-pointed-map
        ( boundary-fiber-Pointed-Type (boundary-pointed-map-fiber-sequence S))
        ( q))
  eq-pr1-map-equiv-fiber-canonical-boundary-boundary-fiber-sequence-boundary-boundary q =
    ( ap
      ( pr1)
      ( inv
        ( eq-map-equiv-fiber-boundary-fiber-sequence-direct-loop-fiber-inclusion-canonical-Pointed-Type q))) ∙
    ( eq-pr1-map-equiv-fiber-boundary-fiber-sequence-direct-loop-fiber-inclusion q)

  eq-map-equiv-fiber-canonical-boundary-boundary-fiber-sequence-boundary-boundary :
    (q : type-Ω (fiber-fiber-sequence-Pointed-Type S)) →
    map-equiv
      ( equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type S)
      ( map-pointed-map
        ( boundary-fiber-Pointed-Type
          ( boundary-fiber-Pointed-Type
            ( fibration-fiber-sequence-Pointed-Type S)))
        ( map-Ω (pointed-map-fiber-fiber-sequence-Pointed-Type S) q)) ＝
    map-pointed-map
      ( boundary-fiber-Pointed-Type (boundary-pointed-map-fiber-sequence S))
      ( q)
  eq-map-equiv-fiber-canonical-boundary-boundary-fiber-sequence-boundary-boundary q =
    eq-pair-Σ
      ( refl)
      ( ( eq-ap-concat-loop-preserves-point-Pointed-Type
          ( pointed-map-inv-pointed-equiv
            ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))
          ( preserves-point-pointed-map
            ( boundary-fiber-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S)))
          ( map-Ω (pointed-map-fiber-fiber-sequence-Pointed-Type S) q)) ∙
        ( ap
          ( preserves-point-pointed-map
            ( boundary-pointed-map-fiber-sequence S) ∙_)
          ( is-retraction-map-Ω-pointed-map-inv-pointed-equiv
            ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S)
            ( q))))

  eq-map-boundary-boundary-fiber-sequence-direct-loop-fiber-inclusion :
    (q : type-Ω (fiber-fiber-sequence-Pointed-Type S)) →
    map-pointed-map
      ( boundary-pointed-map-fiber-sequence
        ( fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type S))
      ( q) ＝
    map-Ω (fiber-inclusion-fiber-sequence-Pointed-Type S) q
  eq-map-boundary-boundary-fiber-sequence-direct-loop-fiber-inclusion q =
    ( ap
      ( map-pointed-map
        ( pointed-map-inv-pointed-equiv
          ( pointed-equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type S)))
      ( inv
        ( ( eq-map-equiv-fiber-boundary-fiber-sequence-direct-loop-fiber-inclusion-canonical-Pointed-Type q) ∙
          ( eq-map-equiv-fiber-canonical-boundary-boundary-fiber-sequence-boundary-boundary q)))) ∙
    ( is-retraction-map-inv-equiv
      ( equiv-pointed-equiv
        ( pointed-equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type S))
      ( map-Ω (fiber-inclusion-fiber-sequence-Pointed-Type S) q))

  eq-map-hom-trunc-boundary-boundary-fiber-sequence-direct-loop-fiber-inclusion :
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω (fiber-fiber-sequence-Pointed-Type S)))) →
    map-pointed-map
      ( hom-trunc-boundary-boundary-fiber-sequence-direct-Pointed-Type)
      ( x) ＝
    map-pointed-map
      ( hom-trunc-loop-fiber-inclusion-fiber-sequence-Pointed-Type S)
      ( x)
  eq-map-hom-trunc-boundary-boundary-fiber-sequence-direct-loop-fiber-inclusion =
    apply-dependent-universal-property-trunc-Set'
      ( λ x →
        set-Prop
          ( Id-Prop
            ( set-Pointed-Set
              ( trunc-Pointed-Set
                ( Ω (total-space-fiber-sequence-Pointed-Type S))))
            ( map-pointed-map
              ( hom-trunc-boundary-boundary-fiber-sequence-direct-Pointed-Type)
              ( x))
            ( map-pointed-map
              ( hom-trunc-loop-fiber-inclusion-fiber-sequence-Pointed-Type S)
              ( x))))
      ( λ q →
        ( naturality-unit-trunc-Set
          ( map-pointed-map
            ( boundary-pointed-map-fiber-sequence
              ( fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type S)))
          ( q)) ∙
        ( ap
          ( unit-trunc-Set)
          ( eq-map-boundary-boundary-fiber-sequence-direct-loop-fiber-inclusion q)) ∙
        ( inv
          ( naturality-unit-trunc-Set
            ( map-pointed-map
              ( pointed-map-Ω (fiber-inclusion-fiber-sequence-Pointed-Type S)))
            ( q))))

  eq-map-hom-trunc-loop-boundary-fiber-sequence-Pointed-Type :
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω (Ω (base-fiber-sequence-Pointed-Type S))))) →
    map-pointed-map
      ( hom-trunc-loop-pointed-map-fiber-fiber-sequence-Pointed-Type)
      ( map-pointed-map
        ( hom-trunc-loop-boundary-fiber-sequence-Pointed-Type)
        ( x)) ＝
    map-pointed-map
      ( hom-trunc-loop-boundary-boundary-fiber-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))
      ( x)
  eq-map-hom-trunc-loop-boundary-fiber-sequence-Pointed-Type =
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
              ( hom-trunc-loop-pointed-map-fiber-fiber-sequence-Pointed-Type)
              ( map-pointed-map
                ( hom-trunc-loop-boundary-fiber-sequence-Pointed-Type)
                ( x)))
            ( map-pointed-map
              ( hom-trunc-loop-boundary-boundary-fiber-Pointed-Type
                ( fibration-fiber-sequence-Pointed-Type S))
              ( x))))
      ( λ q →
        ( ap
          ( map-pointed-map
            ( hom-trunc-loop-pointed-map-fiber-fiber-sequence-Pointed-Type))
          ( naturality-unit-trunc-Set
            ( map-pointed-map
              ( pointed-map-Ω (boundary-pointed-map-fiber-sequence S)))
            ( q))) ∙
        ( naturality-unit-trunc-Set
          ( map-pointed-map
            ( pointed-map-Ω
              ( pointed-map-fiber-fiber-sequence-Pointed-Type S)))
          ( map-Ω (boundary-pointed-map-fiber-sequence S) q)) ∙
        ( ap
          ( unit-trunc-Set)
          ( ( inv
              ( preserves-comp-map-Ω
                ( pointed-map-fiber-fiber-sequence-Pointed-Type S)
                ( boundary-pointed-map-fiber-sequence S)
                ( q))) ∙
            ( htpy-map-Ω
              ( pointed-map-fiber-fiber-sequence-Pointed-Type S ∘∗
                boundary-pointed-map-fiber-sequence S)
              ( boundary-fiber-Pointed-Type
                ( fibration-fiber-sequence-Pointed-Type S))
              ( pointed-htpy-fiber-fiber-boundary-fiber-sequence)
              ( q)))) ∙
        ( inv
          ( naturality-unit-trunc-Set
            ( map-pointed-map
              ( pointed-map-Ω
                ( boundary-fiber-Pointed-Type
                  ( fibration-fiber-sequence-Pointed-Type S))))
            ( q))))

  eq-map-hom-trunc-loop-fiber-inclusion-fiber-sequence-Pointed-Type :
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω (fiber-fiber-sequence-Pointed-Type S)))) →
    map-pointed-map
      ( hom-trunc-loop-fiber-inclusion-fiber-sequence-Pointed-Type S)
      ( x) ＝
    map-pointed-map
      ( hom-trunc-loop-inclusion-fiber-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))
      ( map-pointed-map
        ( hom-trunc-loop-pointed-map-fiber-fiber-sequence-Pointed-Type)
        ( x))
  eq-map-hom-trunc-loop-fiber-inclusion-fiber-sequence-Pointed-Type =
    apply-dependent-universal-property-trunc-Set'
      ( λ x →
        set-Prop
          ( Id-Prop
            ( set-Pointed-Set
              ( trunc-Pointed-Set
                ( Ω (total-space-fiber-sequence-Pointed-Type S))))
            ( map-pointed-map
              ( hom-trunc-loop-fiber-inclusion-fiber-sequence-Pointed-Type S)
              ( x))
            ( map-pointed-map
              ( hom-trunc-loop-inclusion-fiber-Pointed-Type
                ( fibration-fiber-sequence-Pointed-Type S))
              ( map-pointed-map
                ( hom-trunc-loop-pointed-map-fiber-fiber-sequence-Pointed-Type)
                ( x)))))
      ( λ q →
        ( naturality-unit-trunc-Set
          ( map-pointed-map
            ( pointed-map-Ω
              ( fiber-inclusion-fiber-sequence-Pointed-Type S)))
          ( q)) ∙
        ( ap
          ( unit-trunc-Set)
          ( ( htpy-map-Ω
              ( fiber-inclusion-fiber-sequence-Pointed-Type S)
              ( inclusion-fiber-Pointed-Type
                ( fibration-fiber-sequence-Pointed-Type S) ∘∗
                pointed-map-fiber-fiber-sequence-Pointed-Type S)
              ( pointed-htpy-fiber-inclusion-fiber-sequence-Pointed-Type S)
              ( q)) ∙
            ( preserves-comp-map-Ω
              ( inclusion-fiber-Pointed-Type
                ( fibration-fiber-sequence-Pointed-Type S))
              ( pointed-map-fiber-fiber-sequence-Pointed-Type S)
              ( q)))) ∙
        ( inv
          ( naturality-unit-trunc-Set
            ( map-pointed-map
              ( pointed-map-Ω
                ( inclusion-fiber-Pointed-Type
                  ( fibration-fiber-sequence-Pointed-Type S))))
            ( map-Ω (pointed-map-fiber-fiber-sequence-Pointed-Type S) q))) ∙
        ( ap
          ( map-pointed-map
            ( hom-trunc-loop-inclusion-fiber-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S)))
          ( inv
            ( naturality-unit-trunc-Set
              ( map-pointed-map
                ( pointed-map-Ω
                  ( pointed-map-fiber-fiber-sequence-Pointed-Type S)))
              ( q)))))

  is-exact-set-truncation-loop-boundary-fiber-inclusion-fiber-sequence :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (Ω (Ω (base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set (Ω (fiber-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (Ω (total-space-fiber-sequence-Pointed-Type S)))
      ( hom-trunc-loop-boundary-fiber-sequence-Pointed-Type)
      ( hom-trunc-loop-fiber-inclusion-fiber-sequence-Pointed-Type S)
  is-exact-set-truncation-loop-boundary-fiber-inclusion-fiber-sequence =
    is-exact-hom-Pointed-Set-injective-middle
      ( trunc-Pointed-Set (Ω (Ω (base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set (Ω (fiber-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set
        ( Ω
          ( fiber-Pointed-Type
            ( fibration-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set (Ω (total-space-fiber-sequence-Pointed-Type S)))
      ( hom-trunc-loop-boundary-fiber-sequence-Pointed-Type)
      ( hom-trunc-loop-fiber-inclusion-fiber-sequence-Pointed-Type S)
      ( hom-trunc-loop-boundary-boundary-fiber-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))
      ( hom-trunc-loop-inclusion-fiber-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))
      ( hom-trunc-loop-pointed-map-fiber-fiber-sequence-Pointed-Type)
      ( is-injective-map-trunc-Set
        ( map-Ω (pointed-map-fiber-fiber-sequence-Pointed-Type S))
        ( is-injective-equiv
          ( equiv-Ω-pointed-equiv
            ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))))
      ( eq-map-hom-trunc-loop-boundary-fiber-sequence-Pointed-Type)
      ( eq-map-hom-trunc-loop-fiber-inclusion-fiber-sequence-Pointed-Type)
      ( is-exact-set-truncation-loop-boundary-boundary-fiber-sequence-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))
```
