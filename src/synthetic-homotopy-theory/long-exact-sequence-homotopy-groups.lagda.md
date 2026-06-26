# Long exact sequences of homotopy groups

```agda
module synthetic-homotopy-theory.long-exact-sequence-homotopy-groups where
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
open import synthetic-homotopy-theory.loop-spaces-fibers-of-pointed-maps
open import synthetic-homotopy-theory.loop-spaces-pointed-equivalences
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.reassociation-iterated-loop-spaces
```

</details>

## Idea

A [fiber sequence](structured-types.fiber-sequences.md)

```text
  F →∗ E →∗ B
```

has induced homomorphisms on homotopy groups. The remaining extra datum needed
to state the long exact sequence is the family of boundary homomorphisms

```text
  π(n+2) B → π(n+1) F.
```

In the indexing convention of
[homotopy groups](synthetic-homotopy-theory.homotopy-groups.md),
`concrete-homotopy-group n` denotes `π(n+1)`.

The public group-level boundary convention is the canonical iterated boundary
homomorphism. The shifted sequence `Ω E →∗ Ω B →∗ F` is provided structurally by
the connecting fiber sequence module; names in this file containing `direct` or
the older boundary-map terminology are compatibility adapters used by the LES
proof.

## Definitions

### The loop space of the fiber of a pointed map

The loop-fiber equivalence and its compatibility with fiber inclusions are
defined in
[`loop-spaces-fibers-of-pointed-maps`](synthetic-homotopy-theory.loop-spaces-fibers-of-pointed-maps.md).

### Boundary maps of pointed maps

The boundary-map terminology, the direct fiber-of-boundary comparison, and
the looped-boundary comparison adapters are defined in
[`fibers-boundary-maps-pointed-maps`](synthetic-homotopy-theory.fibers-boundary-maps-pointed-maps.md).

### Pointed equivalence algebra

The generic loop-space algebra for pointed equivalences is defined in
[`loop-spaces-pointed-equivalences`](synthetic-homotopy-theory.loop-spaces-pointed-equivalences.md).

### Induced maps on the homotopy groups of a fiber sequence

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence :
    (n : ℕ) →
    hom-Concrete-Group
      ( concrete-homotopy-group
        ( n)
        ( fiber-fiber-sequence-Pointed-Type S))
      ( concrete-homotopy-group
        ( n)
        ( total-space-fiber-sequence-Pointed-Type S))
  hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence n =
    hom-concrete-homotopy-group
      ( n)
      ( fiber-inclusion-fiber-sequence-Pointed-Type S)

  hom-fibration-concrete-homotopy-group-fiber-sequence :
    (n : ℕ) →
    hom-Concrete-Group
      ( concrete-homotopy-group
        ( n)
        ( total-space-fiber-sequence-Pointed-Type S))
      ( concrete-homotopy-group
        ( n)
        ( base-fiber-sequence-Pointed-Type S))
  hom-fibration-concrete-homotopy-group-fiber-sequence n =
    hom-concrete-homotopy-group
      ( n)
      ( fibration-fiber-sequence-Pointed-Type S)
```

### Iterated loop fiber sequences of a fiber sequence

```agda
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

### Compatibility name for the connecting map of a fiber sequence

The packaged boundary map is the connecting map of the packaged fiber sequence.
The `boundary` name is retained for the homotopy-group LES API.

```agda
  boundary-pointed-map-fiber-sequence : Ω (base-fiber-sequence-Pointed-Type S) →∗
    fiber-fiber-sequence-Pointed-Type S
  boundary-pointed-map-fiber-sequence =
    connecting-map-fiber-sequence-Pointed-Type S

  pointed-map-iterated-boundary-fiber-sequence :
    (n : ℕ) →
    iterated-loop-space
      ( succ-ℕ n)
      ( base-fiber-sequence-Pointed-Type S) →∗
    iterated-loop-space
      ( n)
      ( fiber-fiber-sequence-Pointed-Type S)
  pointed-map-iterated-boundary-fiber-sequence zero-ℕ =
    boundary-pointed-map-fiber-sequence
  pointed-map-iterated-boundary-fiber-sequence (succ-ℕ n) =
    pointed-map-Ω (pointed-map-iterated-boundary-fiber-sequence n)

  reassociate-pointed-map-iterated-boundary-fiber-sequence :
    (n : ℕ) →
    tr
      (λ X → X →∗ iterated-loop-space n (fiber-fiber-sequence-Pointed-Type S))
      (reassociate-succ-iterated-loop-space n (base-fiber-sequence-Pointed-Type S))
      (pointed-map-iterated-boundary-fiber-sequence n) ＝
    pointed-map-iterated-loop-space n boundary-pointed-map-fiber-sequence
  reassociate-pointed-map-iterated-boundary-fiber-sequence zero-ℕ = refl
  reassociate-pointed-map-iterated-boundary-fiber-sequence (succ-ℕ n) =
    tr-pointed-map-Ω
      (reassociate-succ-iterated-loop-space n (base-fiber-sequence-Pointed-Type S))
      (refl)
      (pointed-map-iterated-boundary-fiber-sequence n) ∙
    ap pointed-map-Ω
      (reassociate-pointed-map-iterated-boundary-fiber-sequence n)

  reassociate-Ω-pointed-map-iterated-boundary-fiber-sequence :
    (n : ℕ) →
    tr
      (λ X → X →∗ Ω (iterated-loop-space n (fiber-fiber-sequence-Pointed-Type S)))
      (reassociate-Ω-succ-iterated-loop-space n (base-fiber-sequence-Pointed-Type S))
      (pointed-map-Ω (pointed-map-iterated-boundary-fiber-sequence n)) ＝
    pointed-map-Ω
      (pointed-map-iterated-loop-space n boundary-pointed-map-fiber-sequence)
  reassociate-Ω-pointed-map-iterated-boundary-fiber-sequence n =
    tr-pointed-map-Ω
      (reassociate-succ-iterated-loop-space n (base-fiber-sequence-Pointed-Type S))
      (refl)
      (pointed-map-iterated-boundary-fiber-sequence n) ∙
    ap pointed-map-Ω
      (reassociate-pointed-map-iterated-boundary-fiber-sequence n)

  canonical-pointed-map-iterated-boundary-fiber-sequence :
    (n : ℕ) →
    iterated-loop-space
      ( succ-ℕ n)
      ( base-fiber-sequence-Pointed-Type S) →∗
    iterated-loop-space
      ( n)
      ( fiber-fiber-sequence-Pointed-Type S)
  canonical-pointed-map-iterated-boundary-fiber-sequence n =
    pointed-map-inv-pointed-equiv
      ( pointed-equiv-iterated-loop-fiber-fiber-sequence n) ∘∗
    boundary-fiber-Pointed-Type
      ( pointed-map-iterated-loop-space
        ( n)
        ( fibration-fiber-sequence-Pointed-Type S))

  canonical-pointed-map-iterated-loop-boundary-fiber-sequence :
    (n : ℕ) →
    Ω
      ( iterated-loop-space
        ( succ-ℕ n)
        ( base-fiber-sequence-Pointed-Type S)) →∗
    Ω
      ( iterated-loop-space
        ( n)
        ( fiber-fiber-sequence-Pointed-Type S))
  canonical-pointed-map-iterated-loop-boundary-fiber-sequence n =
    pointed-map-inv-pointed-equiv
      ( pointed-equiv-fiber-fiber-sequence-Pointed-Type
        ( iterated-loop-fiber-sequence (succ-ℕ n))) ∘∗
    boundary-fiber-Pointed-Type
      ( fibration-fiber-sequence-Pointed-Type
        ( iterated-loop-fiber-sequence (succ-ℕ n)))

  loop-canonical-pointed-map-iterated-boundary-fiber-sequence :
    (n : ℕ) →
    Ω
      ( iterated-loop-space
        ( succ-ℕ n)
        ( base-fiber-sequence-Pointed-Type S)) →∗
    Ω
      ( iterated-loop-space
        ( n)
        ( fiber-fiber-sequence-Pointed-Type S))
  loop-canonical-pointed-map-iterated-boundary-fiber-sequence n =
    pointed-map-Ω
      ( canonical-pointed-map-iterated-boundary-fiber-sequence n)

  equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type :
    type-Pointed-Type
      ( fiber-Pointed-Type
        ( boundary-fiber-Pointed-Type
          ( fibration-fiber-sequence-Pointed-Type S))) ≃
    type-Pointed-Type (fiber-Pointed-Type boundary-pointed-map-fiber-sequence)
  equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type =
    equiv-tot
      ( λ q →
        ( equiv-concat'
          ( map-pointed-map boundary-pointed-map-fiber-sequence q)
          ( preserves-point-map-inv-pointed-equiv
            ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))) ∘e
        ( equiv-ap
          ( equiv-inv-pointed-equiv
            ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))
          ( map-pointed-map
            ( boundary-fiber-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S))
            ( q))
          ( point-Pointed-Type
            ( fiber-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S)))))

  preserves-point-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type :
    map-equiv
      ( equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type)
      ( point-Pointed-Type
        ( fiber-Pointed-Type
          ( boundary-fiber-Pointed-Type
            ( fibration-fiber-sequence-Pointed-Type S)))) ＝
    point-Pointed-Type (fiber-Pointed-Type boundary-pointed-map-fiber-sequence)
  preserves-point-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type =
    refl

  pointed-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type :
    fiber-Pointed-Type
      ( boundary-fiber-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S)) ≃∗
    fiber-Pointed-Type boundary-pointed-map-fiber-sequence
  pr1 pointed-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type =
    equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type
  pr2 pointed-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type =
    preserves-point-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type

  pointed-htpy-inclusion-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type :
    inclusion-fiber-Pointed-Type
      ( boundary-fiber-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S)) ~∗
    ( inclusion-fiber-Pointed-Type boundary-pointed-map-fiber-sequence ∘∗
      pointed-map-pointed-equiv
        pointed-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type)
  pr1 pointed-htpy-inclusion-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type u =
    refl
  pr2 pointed-htpy-inclusion-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type =
    refl

  equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type :
    type-Ω (total-space-fiber-sequence-Pointed-Type S) ≃
    type-Pointed-Type (fiber-Pointed-Type boundary-pointed-map-fiber-sequence)
  equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type =
    equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type ∘e
    equiv-fiber-boundary-map-Ω-direct-Pointed-Type
      ( fibration-fiber-sequence-Pointed-Type S)

  htpy-inclusion-fiber-boundary-fiber-sequence-direct-Pointed-Type :
    (p : type-Ω (total-space-fiber-sequence-Pointed-Type S)) →
    map-Ω (fibration-fiber-sequence-Pointed-Type S) p ＝
    map-pointed-map
      ( inclusion-fiber-Pointed-Type boundary-pointed-map-fiber-sequence)
      ( map-equiv equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type p)
  htpy-inclusion-fiber-boundary-fiber-sequence-direct-Pointed-Type p =
    refl

  preserves-point-equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type :
    map-equiv equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type refl ＝
    point-Pointed-Type (fiber-Pointed-Type boundary-pointed-map-fiber-sequence)
  preserves-point-equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type =
    ( ap
      ( map-equiv
        equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type)
      ( preserves-point-equiv-fiber-boundary-map-Ω-direct-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))) ∙
    preserves-point-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type

  pointed-equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type :
    Ω (total-space-fiber-sequence-Pointed-Type S) ≃∗
    fiber-Pointed-Type boundary-pointed-map-fiber-sequence
  pointed-equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type =
    comp-pointed-equiv
      ( pointed-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type)
      ( pointed-equiv-fiber-boundary-map-Ω-direct-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))

  pointed-htpy-inclusion-fiber-boundary-fiber-sequence-direct-Pointed-Type :
    pointed-map-Ω (fibration-fiber-sequence-Pointed-Type S) ~∗
    ( inclusion-fiber-Pointed-Type boundary-pointed-map-fiber-sequence ∘∗
      pointed-map-pointed-equiv
        pointed-equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type)
  pointed-htpy-inclusion-fiber-boundary-fiber-sequence-direct-Pointed-Type =
    concat-pointed-htpy
      ( pointed-htpy-inclusion-fiber-boundary-map-Ω-direct-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))
      ( concat-pointed-htpy
        ( right-whisker-comp-pointed-htpy
          ( inclusion-fiber-Pointed-Type
            ( boundary-fiber-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S)))
          ( inclusion-fiber-Pointed-Type boundary-pointed-map-fiber-sequence ∘∗
            pointed-map-pointed-equiv
              pointed-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type)
          ( pointed-htpy-inclusion-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type)
          ( pointed-map-pointed-equiv
            ( pointed-equiv-fiber-boundary-map-Ω-direct-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S))))
        ( associative-comp-pointed-map
          ( inclusion-fiber-Pointed-Type boundary-pointed-map-fiber-sequence)
          ( pointed-map-pointed-equiv
            pointed-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type)
          ( pointed-map-pointed-equiv
            ( pointed-equiv-fiber-boundary-map-Ω-direct-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S)))))

  is-fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type :
    is-fiber-sequence-Pointed-Type
      ( pointed-map-Ω (fibration-fiber-sequence-Pointed-Type S))
      ( boundary-pointed-map-fiber-sequence)
  pr1 is-fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type =
    pointed-equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type
  pr2 is-fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type =
    pointed-htpy-inclusion-fiber-boundary-fiber-sequence-direct-Pointed-Type

  fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type :
    fiber-sequence-Pointed-Type l2 l3 l1
  pr1 fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type =
    Ω (total-space-fiber-sequence-Pointed-Type S)
  pr1 (pr2 fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type) =
    Ω (base-fiber-sequence-Pointed-Type S)
  pr1 (pr2 (pr2 fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type)) =
    fiber-fiber-sequence-Pointed-Type S
  pr1 (pr2 (pr2 (pr2 fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type))) =
    pointed-map-Ω (fibration-fiber-sequence-Pointed-Type S)
  pr1 (pr2 (pr2 (pr2 (pr2 fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type)))) =
    boundary-pointed-map-fiber-sequence
  pr2 (pr2 (pr2 (pr2 (pr2 fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type)))) =
    is-fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type

  boundary-hom-concrete-homotopy-group-fiber-sequence :
    (n : ℕ) →
    hom-Concrete-Group
      ( concrete-homotopy-group
        ( succ-ℕ n)
        ( base-fiber-sequence-Pointed-Type S))
      ( concrete-homotopy-group
        ( n)
        ( fiber-fiber-sequence-Pointed-Type S))
  boundary-hom-concrete-homotopy-group-fiber-sequence n =
    hom-concrete-group-Pointed-Type
      ( pointed-map-iterated-boundary-fiber-sequence n)

  canonical-boundary-hom-concrete-homotopy-group-fiber-sequence :
    (n : ℕ) →
    hom-Concrete-Group
      ( concrete-homotopy-group
        ( succ-ℕ n)
        ( base-fiber-sequence-Pointed-Type S))
      ( concrete-homotopy-group
        ( n)
        ( fiber-fiber-sequence-Pointed-Type S))
  canonical-boundary-hom-concrete-homotopy-group-fiber-sequence n =
    hom-concrete-group-Pointed-Type
      ( canonical-pointed-map-iterated-boundary-fiber-sequence n)
```

### The canonical boundary homomorphism of a pointed map

```agda
module _
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B)
  where

  canonical-boundary-hom-concrete-homotopy-group-Pointed-Type :
    (n : ℕ) →
    hom-Concrete-Group
      ( concrete-homotopy-group (succ-ℕ n) B)
      ( concrete-homotopy-group n (fiber-Pointed-Type g))
  canonical-boundary-hom-concrete-homotopy-group-Pointed-Type n =
    boundary-hom-concrete-homotopy-group-fiber-sequence
      ( fiber-sequence-fiber-Pointed-Type g)
      ( n)
```

## Properties

The set-truncated exactness statements for canonical, packaged, boundary, and
looped boundary fiber-sequence segments are defined in
[`set-truncated-exactness-homotopy-groups-fiber-sequences`](synthetic-homotopy-theory.set-truncated-exactness-homotopy-groups-fiber-sequences.md).
