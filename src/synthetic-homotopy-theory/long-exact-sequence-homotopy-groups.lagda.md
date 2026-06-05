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
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.functoriality-homotopy-automorphism-groups
open import group-theory.homomorphisms-concrete-groups

open import structured-types.exact-sequences-pointed-sets
open import structured-types.fiber-sequences
open import structured-types.fibers-of-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-homotopy-groups
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
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

## Definitions

### The boundary pointed map of a pointed map

```agda
module _
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B)
  where

  boundary-fiber-Pointed-Type : Ω B →∗ fiber-Pointed-Type g
  pr1 boundary-fiber-Pointed-Type p =
    ( point-Pointed-Type E , preserves-point-pointed-map g ∙ p)
  pr2 boundary-fiber-Pointed-Type =
    eq-pair-Σ refl right-unit
```

### The fiber sequence after taking the fiber of a pointed map

The first nontrivial step in the iterated fiber sequence construction is the
identification of the fiber of the fiber inclusion with the loop space of the
base. This is the first instance of HoTT Book Lemma 8.4.4.

```agda
  map-fiber-inclusion-path-Pointed-Type :
    map-pointed-map g (point-Pointed-Type E) ＝ point-Pointed-Type B →
    type-Pointed-Type
      ( fiber-Pointed-Type (inclusion-fiber-Pointed-Type g))
  map-fiber-inclusion-path-Pointed-Type p =
    ( ( point-Pointed-Type E , p) , refl)

  map-inv-fiber-inclusion-path-Pointed-Type :
    type-Pointed-Type
      ( fiber-Pointed-Type (inclusion-fiber-Pointed-Type g)) →
    map-pointed-map g (point-Pointed-Type E) ＝ point-Pointed-Type B
  map-inv-fiber-inclusion-path-Pointed-Type ((x , p) , q) =
    inv (ap (map-pointed-map g) q) ∙ p

  is-section-map-inv-fiber-inclusion-path-Pointed-Type :
    (x :
      type-Pointed-Type
        ( fiber-Pointed-Type (inclusion-fiber-Pointed-Type g))) →
    map-fiber-inclusion-path-Pointed-Type
      ( map-inv-fiber-inclusion-path-Pointed-Type x) ＝ x
  is-section-map-inv-fiber-inclusion-path-Pointed-Type
    ((.(point-Pointed-Type E) , p) , refl) =
    refl

  is-retraction-map-inv-fiber-inclusion-path-Pointed-Type :
    (p : map-pointed-map g (point-Pointed-Type E) ＝ point-Pointed-Type B) →
    map-inv-fiber-inclusion-path-Pointed-Type
      ( map-fiber-inclusion-path-Pointed-Type p) ＝ p
  is-retraction-map-inv-fiber-inclusion-path-Pointed-Type p = refl

  is-equiv-map-fiber-inclusion-path-Pointed-Type :
    is-equiv map-fiber-inclusion-path-Pointed-Type
  is-equiv-map-fiber-inclusion-path-Pointed-Type =
    is-equiv-is-invertible
      ( map-inv-fiber-inclusion-path-Pointed-Type)
      ( is-section-map-inv-fiber-inclusion-path-Pointed-Type)
      ( is-retraction-map-inv-fiber-inclusion-path-Pointed-Type)

  equiv-fiber-inclusion-path-Pointed-Type :
    ( map-pointed-map g (point-Pointed-Type E) ＝ point-Pointed-Type B) ≃
    type-Pointed-Type
      ( fiber-Pointed-Type (inclusion-fiber-Pointed-Type g))
  pr1 equiv-fiber-inclusion-path-Pointed-Type =
    map-fiber-inclusion-path-Pointed-Type
  pr2 equiv-fiber-inclusion-path-Pointed-Type =
    is-equiv-map-fiber-inclusion-path-Pointed-Type

  equiv-fiber-inclusion-boundary-fiber-Pointed-Type :
    type-Ω B ≃
    type-Pointed-Type
      ( fiber-Pointed-Type (inclusion-fiber-Pointed-Type g))
  equiv-fiber-inclusion-boundary-fiber-Pointed-Type =
    equiv-fiber-inclusion-path-Pointed-Type ∘e
    equiv-concat (preserves-point-pointed-map g) (point-Pointed-Type B)

  dependent-identification-eq-pair-fiber-inclusion-Pointed-Type :
    {p q : map-pointed-map g (point-Pointed-Type E) ＝ point-Pointed-Type B}
    (α : p ＝ q) →
    dependent-identification
      ( λ x → pr1 x ＝ point-Pointed-Type E)
      ( eq-pair-Σ
        { A = type-Pointed-Type E}
        { B = λ x → map-pointed-map g x ＝ point-Pointed-Type B}
        { s = point-Pointed-Type E , p}
        { t = point-Pointed-Type E , q}
        ( refl)
        ( α))
      ( refl)
      ( refl)
  dependent-identification-eq-pair-fiber-inclusion-Pointed-Type refl =
    refl

  preserves-point-equiv-fiber-inclusion-boundary-fiber-Pointed-Type :
    map-equiv equiv-fiber-inclusion-boundary-fiber-Pointed-Type refl ＝
    point-Pointed-Type
      ( fiber-Pointed-Type (inclusion-fiber-Pointed-Type g))
  preserves-point-equiv-fiber-inclusion-boundary-fiber-Pointed-Type =
    eq-pair-Σ
      ( eq-pair-Σ
        { A = type-Pointed-Type E}
        { B = λ x → map-pointed-map g x ＝ point-Pointed-Type B}
        { s =
          point-Pointed-Type E ,
          preserves-point-pointed-map g ∙ refl}
        { t = point-Pointed-Type E , preserves-point-pointed-map g}
        ( refl)
        ( right-unit))
      ( dependent-identification-eq-pair-fiber-inclusion-Pointed-Type
        ( right-unit))

  pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type :
    Ω B ≃∗ fiber-Pointed-Type (inclusion-fiber-Pointed-Type g)
  pr1 pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type =
    equiv-fiber-inclusion-boundary-fiber-Pointed-Type
  pr2 pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type =
    preserves-point-equiv-fiber-inclusion-boundary-fiber-Pointed-Type

  pointed-htpy-boundary-fiber-inclusion-boundary-fiber-Pointed-Type :
    boundary-fiber-Pointed-Type ~∗
    ( inclusion-fiber-Pointed-Type (inclusion-fiber-Pointed-Type g) ∘∗
      pointed-map-pointed-equiv
        pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type)
  pr1 pointed-htpy-boundary-fiber-inclusion-boundary-fiber-Pointed-Type p =
    refl
  pr2 pointed-htpy-boundary-fiber-inclusion-boundary-fiber-Pointed-Type =
    ( inv
      ( ap-pr1-eq-pair-Σ
        ( eq-pair-Σ
          { A = type-Pointed-Type E}
          { B = λ x → map-pointed-map g x ＝ point-Pointed-Type B}
          { s =
            point-Pointed-Type E ,
            preserves-point-pointed-map g ∙ refl}
          { t = point-Pointed-Type E , preserves-point-pointed-map g}
          ( refl)
          ( right-unit))
        ( dependent-identification-eq-pair-fiber-inclusion-Pointed-Type
          ( right-unit)))) ∙
    ( inv right-unit)

  is-fiber-sequence-boundary-fiber-Pointed-Type :
    is-fiber-sequence-Pointed-Type
      ( boundary-fiber-Pointed-Type)
      ( inclusion-fiber-Pointed-Type g)
  pr1 is-fiber-sequence-boundary-fiber-Pointed-Type =
    pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type
  pr2 is-fiber-sequence-boundary-fiber-Pointed-Type =
    pointed-htpy-boundary-fiber-inclusion-boundary-fiber-Pointed-Type

  fiber-sequence-boundary-fiber-Pointed-Type :
    fiber-sequence-Pointed-Type l2 (l1 ⊔ l2) l1
  pr1 fiber-sequence-boundary-fiber-Pointed-Type =
    Ω B
  pr1 (pr2 fiber-sequence-boundary-fiber-Pointed-Type) =
    fiber-Pointed-Type g
  pr1 (pr2 (pr2 fiber-sequence-boundary-fiber-Pointed-Type)) =
    E
  pr1 (pr2 (pr2 (pr2 fiber-sequence-boundary-fiber-Pointed-Type))) =
    boundary-fiber-Pointed-Type
  pr1 (pr2 (pr2 (pr2 (pr2 fiber-sequence-boundary-fiber-Pointed-Type)))) =
    inclusion-fiber-Pointed-Type g
  pr2 (pr2 (pr2 (pr2 (pr2 fiber-sequence-boundary-fiber-Pointed-Type)))) =
    is-fiber-sequence-boundary-fiber-Pointed-Type
```

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

### The boundary map of a fiber sequence

```agda
  boundary-pointed-map-fiber-sequence : Ω (base-fiber-sequence-Pointed-Type S) →∗
    fiber-fiber-sequence-Pointed-Type S
  boundary-pointed-map-fiber-sequence =
    pointed-map-inv-pointed-equiv
      ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S) ∘∗
    boundary-fiber-Pointed-Type
      ( fibration-fiber-sequence-Pointed-Type S)

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
