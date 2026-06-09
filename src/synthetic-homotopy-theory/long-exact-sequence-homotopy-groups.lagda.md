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
open import foundation.functoriality-set-truncation
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
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

  eq-ap-map-Ω-Pointed-Type :
    (p : type-Ω E) →
    ap (map-pointed-map g) p ＝
    ( preserves-point-pointed-map g ∙ map-Ω g p) ∙
    inv (preserves-point-pointed-map g)
  eq-ap-map-Ω-Pointed-Type p =
    inv
      ( equational-reasoning
        ( preserves-point-pointed-map g ∙ map-Ω g p) ∙
          inv (preserves-point-pointed-map g)
        ＝ ( preserves-point-pointed-map g ∙
            ( inv (preserves-point-pointed-map g) ∙
              ( ap (map-pointed-map g) p ∙
                preserves-point-pointed-map g))) ∙
          inv (preserves-point-pointed-map g)
          by
          ap
            ( λ u →
              ( preserves-point-pointed-map g ∙ u) ∙
              inv (preserves-point-pointed-map g))
            ( eq-conjugation-tr-type-Ω
              ( preserves-point-pointed-map g)
              ( ap (map-pointed-map g) p))
        ＝ ( ( preserves-point-pointed-map g ∙
              inv (preserves-point-pointed-map g)) ∙
            ( ap (map-pointed-map g) p ∙
              preserves-point-pointed-map g)) ∙
          inv (preserves-point-pointed-map g)
          by
          ap
            ( _∙ inv (preserves-point-pointed-map g))
            ( inv
              ( assoc
                ( preserves-point-pointed-map g)
                ( inv (preserves-point-pointed-map g))
                ( ap (map-pointed-map g) p ∙
                  preserves-point-pointed-map g)))
        ＝ ( refl ∙
            ( ap (map-pointed-map g) p ∙
              preserves-point-pointed-map g)) ∙
          inv (preserves-point-pointed-map g)
          by
          ap
            ( λ u →
              ( u ∙
                ( ap (map-pointed-map g) p ∙
                  preserves-point-pointed-map g)) ∙
              inv (preserves-point-pointed-map g))
            ( right-inv (preserves-point-pointed-map g))
        ＝ ( ap (map-pointed-map g) p ∙ preserves-point-pointed-map g) ∙
          inv (preserves-point-pointed-map g)
          by ap (_∙ inv (preserves-point-pointed-map g)) left-unit
        ＝ ap (map-pointed-map g) p ∙
          ( preserves-point-pointed-map g ∙
            inv (preserves-point-pointed-map g))
          by
          assoc
            ( ap (map-pointed-map g) p)
            ( preserves-point-pointed-map g)
            ( inv (preserves-point-pointed-map g))
        ＝ ap (map-pointed-map g) p ∙ refl
          by
          ap
            ( ap (map-pointed-map g) p ∙_)
            ( right-inv (preserves-point-pointed-map g))
        ＝ ap (map-pointed-map g) p by right-unit)

  eq-boundary-map-Ω-Pointed-Type :
    (p : type-Ω E) →
    map-pointed-map boundary-fiber-Pointed-Type (map-Ω g p) ＝
    point-Pointed-Type (fiber-Pointed-Type g)
  eq-boundary-map-Ω-Pointed-Type p =
    map-inv-fiber-ap-eq-fiber
      ( map-pointed-map g)
      ( map-pointed-map boundary-fiber-Pointed-Type (map-Ω g p))
      ( point-Pointed-Type (fiber-Pointed-Type g))
      ( p , eq-ap-map-Ω-Pointed-Type p)

  map-fiber-boundary-map-Ω-Pointed-Type :
    type-Ω E →
    type-Pointed-Type (fiber-Pointed-Type boundary-fiber-Pointed-Type)
  pr1 (map-fiber-boundary-map-Ω-Pointed-Type p) = map-Ω g p
  pr2 (map-fiber-boundary-map-Ω-Pointed-Type p) =
    eq-boundary-map-Ω-Pointed-Type p

  map-inv-fiber-boundary-map-Ω-Pointed-Type :
    type-Pointed-Type (fiber-Pointed-Type boundary-fiber-Pointed-Type) →
    type-Ω E
  map-inv-fiber-boundary-map-Ω-Pointed-Type (q , α) = ap pr1 α

  is-retraction-map-inv-fiber-boundary-map-Ω-Pointed-Type :
    (p : type-Ω E) →
    map-inv-fiber-boundary-map-Ω-Pointed-Type
      ( map-fiber-boundary-map-Ω-Pointed-Type p) ＝ p
  is-retraction-map-inv-fiber-boundary-map-Ω-Pointed-Type p =
    ap-pr1-map-inv-fiber-ap-eq-fiber
      ( map-pointed-map g)
      ( map-pointed-map boundary-fiber-Pointed-Type (map-Ω g p))
      ( point-Pointed-Type (fiber-Pointed-Type g))
      ( p , eq-ap-map-Ω-Pointed-Type p)

  eq-tr-type-Ω-concat-inv-Pointed-Type :
    {x y : type-Pointed-Type B} (p : x ＝ y) (q : y ＝ y) →
    tr-type-Ω p ((p ∙ q) ∙ inv p) ＝ q
  eq-tr-type-Ω-concat-inv-Pointed-Type refl q = right-unit

  eq-pr1-fiber-ap-eq-boundary-fiber-Pointed-Type :
    (q : type-Ω B)
    (α :
      map-pointed-map boundary-fiber-Pointed-Type q ＝
      point-Pointed-Type (fiber-Pointed-Type g)) →
    pr1
      ( fiber-ap-eq-fiber
        ( map-pointed-map g)
        ( map-pointed-map boundary-fiber-Pointed-Type q)
        ( point-Pointed-Type (fiber-Pointed-Type g))
        ( α)) ＝
    ap pr1 α
  eq-pr1-fiber-ap-eq-boundary-fiber-Pointed-Type q α =
    ap pr1
      ( triangle-fiber-ap-eq-fiber
        ( map-pointed-map g)
        ( map-pointed-map boundary-fiber-Pointed-Type q)
        ( point-Pointed-Type (fiber-Pointed-Type g))
        ( α))

  eq-map-Ω-map-inv-fiber-boundary-map-Ω-Pointed-Type :
    (u : type-Pointed-Type (fiber-Pointed-Type boundary-fiber-Pointed-Type)) →
    map-Ω g (map-inv-fiber-boundary-map-Ω-Pointed-Type u) ＝ pr1 u
  eq-map-Ω-map-inv-fiber-boundary-map-Ω-Pointed-Type (q , α) =
    ( ap
      ( λ r →
        tr-type-Ω
          ( preserves-point-pointed-map g)
          ( ap (map-pointed-map g) r))
      ( inv (eq-pr1-fiber-ap-eq-boundary-fiber-Pointed-Type q α))) ∙
    ( ap
      ( tr-type-Ω (preserves-point-pointed-map g))
      ( pr2
        ( fiber-ap-eq-fiber
          ( map-pointed-map g)
          ( map-pointed-map boundary-fiber-Pointed-Type q)
          ( point-Pointed-Type (fiber-Pointed-Type g))
          ( α)))) ∙
    ( eq-tr-type-Ω-concat-inv-Pointed-Type
      ( preserves-point-pointed-map g)
      ( q))
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

  hom-trunc-inclusion-fiber-boundary-fiber-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set
        ( fiber-Pointed-Type (boundary-fiber-Pointed-Type g)))
      ( trunc-Pointed-Set (Ω B))
  hom-trunc-inclusion-fiber-boundary-fiber-Pointed-Type =
    hom-trunc-Pointed-Set
      ( inclusion-fiber-Pointed-Type (boundary-fiber-Pointed-Type g))

  is-in-image-trunc-inclusion-fiber-boundary-fiber-is-in-image-trunc-loop-map-Pointed-Type :
    (x : type-Pointed-Set (trunc-Pointed-Set (Ω B))) →
    is-in-image-hom-Pointed-Set
      {A = trunc-Pointed-Set (Ω E)}
      {B = trunc-Pointed-Set (Ω B)}
      hom-trunc-loop-map-Pointed-Type
      x →
    is-in-image-hom-Pointed-Set
      {A =
        trunc-Pointed-Set
          ( fiber-Pointed-Type (boundary-fiber-Pointed-Type g))}
      {B = trunc-Pointed-Set (Ω B)}
      hom-trunc-inclusion-fiber-boundary-fiber-Pointed-Type
      x
  is-in-image-trunc-inclusion-fiber-boundary-fiber-is-in-image-trunc-loop-map-Pointed-Type
    x H =
    apply-universal-property-trunc-Prop H
      ( subtype-image-hom-Pointed-Set
        {A =
          trunc-Pointed-Set
            ( fiber-Pointed-Type (boundary-fiber-Pointed-Type g))}
        {B = trunc-Pointed-Set (Ω B)}
        ( hom-trunc-inclusion-fiber-boundary-fiber-Pointed-Type)
        ( x))
      ( λ (t , p) →
        apply-dependent-universal-property-trunc-Set'
          ( λ t' →
            function-Set
              ( map-pointed-map hom-trunc-loop-map-Pointed-Type t' ＝ x)
              ( set-Prop
                ( subtype-image-hom-Pointed-Set
                  {A =
                    trunc-Pointed-Set
                      ( fiber-Pointed-Type (boundary-fiber-Pointed-Type g))}
                  {B = trunc-Pointed-Set (Ω B)}
                  ( hom-trunc-inclusion-fiber-boundary-fiber-Pointed-Type)
                  ( x))))
          ( λ q p' →
            unit-trunc-Prop
              ( unit-trunc-Set
                ( map-fiber-boundary-map-Ω-Pointed-Type g q) ,
                ( naturality-unit-trunc-Set
                  ( map-pointed-map
                    ( inclusion-fiber-Pointed-Type
                      ( boundary-fiber-Pointed-Type g)))
                  ( map-fiber-boundary-map-Ω-Pointed-Type g q)) ∙
                ( inv
                  ( naturality-unit-trunc-Set
                    ( map-pointed-map (pointed-map-Ω g))
                    ( q))) ∙
                ( p')))
          ( t)
          ( p))

  is-in-image-trunc-loop-map-is-in-image-trunc-inclusion-fiber-boundary-fiber-Pointed-Type :
    (x : type-Pointed-Set (trunc-Pointed-Set (Ω B))) →
    is-in-image-hom-Pointed-Set
      {A =
        trunc-Pointed-Set
          ( fiber-Pointed-Type (boundary-fiber-Pointed-Type g))}
      {B = trunc-Pointed-Set (Ω B)}
      hom-trunc-inclusion-fiber-boundary-fiber-Pointed-Type
      x →
    is-in-image-hom-Pointed-Set
      {A = trunc-Pointed-Set (Ω E)}
      {B = trunc-Pointed-Set (Ω B)}
      hom-trunc-loop-map-Pointed-Type
      x
  is-in-image-trunc-loop-map-is-in-image-trunc-inclusion-fiber-boundary-fiber-Pointed-Type
    x H =
    apply-universal-property-trunc-Prop H
      ( subtype-image-hom-Pointed-Set
        {A = trunc-Pointed-Set (Ω E)}
        {B = trunc-Pointed-Set (Ω B)}
        ( hom-trunc-loop-map-Pointed-Type)
        ( x))
      ( λ (t , p) →
        apply-dependent-universal-property-trunc-Set'
          ( λ t' →
            function-Set
              ( map-pointed-map
                hom-trunc-inclusion-fiber-boundary-fiber-Pointed-Type
                t' ＝ x)
              ( set-Prop
                ( subtype-image-hom-Pointed-Set
                  {A = trunc-Pointed-Set (Ω E)}
                  {B = trunc-Pointed-Set (Ω B)}
                  ( hom-trunc-loop-map-Pointed-Type)
                  ( x))))
          ( λ q p' →
            unit-trunc-Prop
              ( unit-trunc-Set
                ( map-inv-fiber-boundary-map-Ω-Pointed-Type g q) ,
                ( naturality-unit-trunc-Set
                  ( map-pointed-map (pointed-map-Ω g))
                  ( map-inv-fiber-boundary-map-Ω-Pointed-Type g q)) ∙
                ( ap
                  ( unit-trunc-Set)
                  ( eq-map-Ω-map-inv-fiber-boundary-map-Ω-Pointed-Type g q)) ∙
                ( inv
                  ( naturality-unit-trunc-Set
                    ( map-pointed-map
                      ( inclusion-fiber-Pointed-Type
                        ( boundary-fiber-Pointed-Type g)))
                    ( q))) ∙
                ( p')))
          ( t)
          ( p))

  is-exact-set-truncation-loop-boundary-fiber-sequence-Pointed-Type :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (Ω E))
      ( trunc-Pointed-Set (Ω B))
      ( trunc-Pointed-Set (fiber-Pointed-Type g))
      ( hom-trunc-loop-map-Pointed-Type)
      ( hom-trunc-boundary-fiber-Pointed-Type)
  pr1 (is-exact-set-truncation-loop-boundary-fiber-sequence-Pointed-Type x) H =
    pr1
      ( is-exact-set-truncation-fiber-sequence-Pointed-Type
        ( boundary-fiber-Pointed-Type g)
        ( x))
      ( is-in-image-trunc-inclusion-fiber-boundary-fiber-is-in-image-trunc-loop-map-Pointed-Type
        ( x)
        ( H))
  pr2 (is-exact-set-truncation-loop-boundary-fiber-sequence-Pointed-Type x) H =
    is-in-image-trunc-loop-map-is-in-image-trunc-inclusion-fiber-boundary-fiber-Pointed-Type
      ( x)
      ( pr2
        ( is-exact-set-truncation-fiber-sequence-Pointed-Type
          ( boundary-fiber-Pointed-Type g)
          ( x))
        ( H))
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

The preceding packaged boundary theorem gives exactness at the chosen fiber
term. The adjacent segment one step to the left has middle term `Ω B`; its
kernel comparison is transported across the same pointed equivalence from the
chosen fiber to the canonical fiber of the fibration.

```agda
  hom-trunc-loop-fibration-fiber-sequence-Pointed-Type :
    hom-Pointed-Set
      ( trunc-Pointed-Set (Ω (total-space-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S)))
  hom-trunc-loop-fibration-fiber-sequence-Pointed-Type =
    hom-trunc-Pointed-Set
      ( pointed-map-Ω (fibration-fiber-sequence-Pointed-Type S))

  is-in-kernel-trunc-boundary-is-in-kernel-trunc-canonical-boundary-fiber-sequence-Pointed-Type :
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S)))) →
    is-in-kernel-hom-Pointed-Set
      {A = trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S))}
      {B =
        trunc-Pointed-Set
          ( fiber-Pointed-Type (fibration-fiber-sequence-Pointed-Type S))}
      ( hom-trunc-boundary-fiber-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))
      ( x) →
    is-in-kernel-hom-Pointed-Set
      {A = trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S))}
      {B = trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S)}
      ( hom-trunc-boundary-fiber-sequence-Pointed-Type)
      ( x)
  is-in-kernel-trunc-boundary-is-in-kernel-trunc-canonical-boundary-fiber-sequence-Pointed-Type
    x H =
    ( inv
      ( is-retraction-hom-trunc-inv-pointed-map-fiber-fiber-sequence-Pointed-Type
        ( map-pointed-map hom-trunc-boundary-fiber-sequence-Pointed-Type x))) ∙
    ( ap
      ( map-pointed-map
        hom-trunc-inv-pointed-map-fiber-fiber-sequence-Pointed-Type)
      ( eq-map-hom-trunc-pointed-map-boundary-fiber-sequence-Pointed-Type
        ( x) ∙ H)) ∙
    ( preserves-point-pointed-map
      hom-trunc-inv-pointed-map-fiber-fiber-sequence-Pointed-Type)

  is-in-kernel-trunc-canonical-boundary-is-in-kernel-trunc-boundary-fiber-sequence-Pointed-Type :
    (x :
      type-Pointed-Set
        ( trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S)))) →
    is-in-kernel-hom-Pointed-Set
      {A = trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S))}
      {B = trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S)}
      ( hom-trunc-boundary-fiber-sequence-Pointed-Type)
      ( x) →
    is-in-kernel-hom-Pointed-Set
      {A = trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S))}
      {B =
        trunc-Pointed-Set
          ( fiber-Pointed-Type (fibration-fiber-sequence-Pointed-Type S))}
      ( hom-trunc-boundary-fiber-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))
      ( x)
  is-in-kernel-trunc-canonical-boundary-is-in-kernel-trunc-boundary-fiber-sequence-Pointed-Type
    x H =
    ( inv
      ( eq-map-hom-trunc-pointed-map-boundary-fiber-sequence-Pointed-Type
        ( x))) ∙
    ( ap
      ( map-pointed-map
        hom-trunc-pointed-map-fiber-fiber-sequence-Pointed-Type)
      ( H)) ∙
    ( preserves-point-pointed-map
      hom-trunc-pointed-map-fiber-fiber-sequence-Pointed-Type)

  is-exact-set-truncation-loop-boundary-fiber-sequence :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (Ω (total-space-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (Ω (base-fiber-sequence-Pointed-Type S)))
      ( trunc-Pointed-Set (fiber-fiber-sequence-Pointed-Type S))
      ( hom-trunc-loop-fibration-fiber-sequence-Pointed-Type)
      ( hom-trunc-boundary-fiber-sequence-Pointed-Type)
  pr1 (is-exact-set-truncation-loop-boundary-fiber-sequence x) H =
    is-in-kernel-trunc-boundary-is-in-kernel-trunc-canonical-boundary-fiber-sequence-Pointed-Type
      ( x)
      ( pr1
        ( is-exact-set-truncation-loop-boundary-fiber-sequence-Pointed-Type
          ( fibration-fiber-sequence-Pointed-Type S)
          ( x))
        ( H))
  pr2 (is-exact-set-truncation-loop-boundary-fiber-sequence x) H =
    pr2
      ( is-exact-set-truncation-loop-boundary-fiber-sequence-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S)
        ( x))
      ( is-in-kernel-trunc-canonical-boundary-is-in-kernel-trunc-boundary-fiber-sequence-Pointed-Type
        ( x)
        ( H))
```
