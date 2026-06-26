# Connecting fiber sequences

```agda
module synthetic-homotopy-theory.connecting-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equality-fibers-of-maps
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import structured-types.fiber-sequences
open import structured-types.fibers-of-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.whiskering-pointed-homotopies-composition

open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

The **connecting fiber sequence** of a pointed map `g : E →∗ B` is the
fiber sequence

```text
  Ω E →∗ Ω B →∗ fiber g
```

whose second map sends a loop in the base to the corresponding point of the
fiber over the base point. This is the `connect_fiberseq` construction used in
long exact sequence proofs.

For a packaged fiber sequence `F →∗ E →∗ B`, the same construction is transported
across the chosen pointed equivalence `F ≃∗ fiber g`, giving the connecting
fiber sequence

```text
  Ω E →∗ Ω B →∗ F.
```

This module is the structural home for those two fiber sequences. Older names
using "boundary" or "direct" in the long-exact-sequence development are
compatibility names for this construction.

## Lemmas

### Inverting the fiber equality equivalence

```agda
private
  module _
    {l1 l2 : Level} {A : UU l1} {B : UU l2}
    (f : A → B) {b : B}
    where

    is-section-map-inv-fiber-ap-eq-fiber :
      (s t : fiber f b) (α : s ＝ t) →
      map-inv-fiber-ap-eq-fiber f s t (fiber-ap-eq-fiber f s t α) ＝ α
    is-section-map-inv-fiber-ap-eq-fiber (x , refl) .(x , refl) refl =
      refl

    htpy-map-inv-fiber-ap-eq-fiber-map-inv-equiv :
      (s t : fiber f b)
      (v : fiber (ap f {x = pr1 s} {y = pr1 t}) (pr2 s ∙ inv (pr2 t))) →
      map-inv-fiber-ap-eq-fiber f s t v ＝
      map-inv-equiv (equiv-fiber-ap-eq-fiber f s t) v
    htpy-map-inv-fiber-ap-eq-fiber-map-inv-equiv s t v =
      ( ap
        ( map-inv-fiber-ap-eq-fiber f s t)
        ( inv (is-section-map-inv-equiv (equiv-fiber-ap-eq-fiber f s t) v))) ∙
      ( is-section-map-inv-fiber-ap-eq-fiber
        ( s)
        ( t)
        ( map-inv-equiv (equiv-fiber-ap-eq-fiber f s t) v))

    is-equiv-map-inv-fiber-ap-eq-fiber :
      (s t : fiber f b) → is-equiv (map-inv-fiber-ap-eq-fiber f s t)
    is-equiv-map-inv-fiber-ap-eq-fiber s t =
      is-equiv-htpy-equiv'
        ( inv-equiv (equiv-fiber-ap-eq-fiber f s t))
        ( λ v → inv (htpy-map-inv-fiber-ap-eq-fiber-map-inv-equiv s t v))

    equiv-map-inv-fiber-ap-eq-fiber :
      (s t : fiber f b) →
      fiber (ap f {x = pr1 s} {y = pr1 t}) (pr2 s ∙ inv (pr2 t)) ≃
      (s ＝ t)
    pr1 (equiv-map-inv-fiber-ap-eq-fiber s t) =
      map-inv-fiber-ap-eq-fiber f s t
    pr2 (equiv-map-inv-fiber-ap-eq-fiber s t) =
      is-equiv-map-inv-fiber-ap-eq-fiber s t
```

## Definitions

### The connecting map of a pointed map

```agda
module _
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B)
  where

  connecting-map-Pointed-Type : Ω B →∗ fiber-Pointed-Type g
  pr1 connecting-map-Pointed-Type p =
    ( point-Pointed-Type E , preserves-point-pointed-map g ∙ p)
  pr2 connecting-map-Pointed-Type =
    eq-pair-Σ refl right-unit
```

### The fiber of the connecting map of a pointed map

The fiber of the connecting map is equivalent, over `Ω B`, to `Ω E`. This
packages the shifted triple `Ω E →∗ Ω B →∗ fiber g` as a pointed fiber
sequence.

```agda
private
  module connecting-map-fiber-data
    {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
    (g : E →∗ B)
    where
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

    eq-tr-type-Ω-concat-inv-Pointed-Type :
      {x y : type-Pointed-Type B} (p : x ＝ y) (q : y ＝ y) →
      tr-type-Ω p ((p ∙ q) ∙ inv p) ＝ q
    eq-tr-type-Ω-concat-inv-Pointed-Type refl q = right-unit

    map-inv-tr-type-Ω-concat-inv-Pointed-Type :
      {x y : type-Pointed-Type B} (p : x ＝ y) →
      type-Ω (type-Pointed-Type B , y) →
      type-Ω (type-Pointed-Type B , x)
    map-inv-tr-type-Ω-concat-inv-Pointed-Type p q =
      (p ∙ q) ∙ inv p

    is-section-map-inv-tr-type-Ω-concat-inv-Pointed-Type :
      {x y : type-Pointed-Type B} (p : x ＝ y)
      (q : type-Ω (type-Pointed-Type B , x)) →
      map-inv-tr-type-Ω-concat-inv-Pointed-Type p
        ( tr-type-Ω p q) ＝ q
    is-section-map-inv-tr-type-Ω-concat-inv-Pointed-Type refl q =
      right-unit

    is-retraction-map-inv-tr-type-Ω-concat-inv-Pointed-Type :
      {x y : type-Pointed-Type B} (p : x ＝ y)
      (q : type-Ω (type-Pointed-Type B , y)) →
      tr-type-Ω p
        ( map-inv-tr-type-Ω-concat-inv-Pointed-Type p q) ＝ q
    is-retraction-map-inv-tr-type-Ω-concat-inv-Pointed-Type =
      eq-tr-type-Ω-concat-inv-Pointed-Type

    is-equiv-map-inv-tr-type-Ω-concat-inv-Pointed-Type :
      {x y : type-Pointed-Type B} (p : x ＝ y) →
      is-equiv (map-inv-tr-type-Ω-concat-inv-Pointed-Type p)
    is-equiv-map-inv-tr-type-Ω-concat-inv-Pointed-Type p =
      is-equiv-is-invertible
        ( tr-type-Ω p)
        ( is-section-map-inv-tr-type-Ω-concat-inv-Pointed-Type p)
        ( is-retraction-map-inv-tr-type-Ω-concat-inv-Pointed-Type p)

    equiv-map-inv-tr-type-Ω-concat-inv-Pointed-Type :
      {x y : type-Pointed-Type B} (p : x ＝ y) →
      type-Ω (type-Pointed-Type B , y) ≃
      type-Ω (type-Pointed-Type B , x)
    pr1 (equiv-map-inv-tr-type-Ω-concat-inv-Pointed-Type p) =
      map-inv-tr-type-Ω-concat-inv-Pointed-Type p
    pr2 (equiv-map-inv-tr-type-Ω-concat-inv-Pointed-Type p) =
      is-equiv-map-inv-tr-type-Ω-concat-inv-Pointed-Type p

    equiv-eq-map-Ω-eq-ap-Pointed-Type :
      (p : type-Ω E) (q : type-Ω B) →
      ( map-Ω g p ＝ q) ≃
      ( ap (map-pointed-map g) p ＝
        ( preserves-point-pointed-map g ∙ q) ∙
        inv (preserves-point-pointed-map g))
    equiv-eq-map-Ω-eq-ap-Pointed-Type p q =
      equiv-concat
        ( eq-ap-map-Ω-Pointed-Type p)
        ( (preserves-point-pointed-map g ∙ q) ∙
          inv (preserves-point-pointed-map g)) ∘e
      equiv-ap
        ( equiv-map-inv-tr-type-Ω-concat-inv-Pointed-Type
          ( preserves-point-pointed-map g))
        ( map-Ω g p)
        ( q)

    equiv-fiber-map-Ω-fiber-ap-Pointed-Type :
      (q : type-Ω B) →
      fiber (map-Ω g) q ≃
      fiber
        ( ap (map-pointed-map g))
        ( (preserves-point-pointed-map g ∙ q) ∙
          inv (preserves-point-pointed-map g))
    equiv-fiber-map-Ω-fiber-ap-Pointed-Type q =
      equiv-tot (λ p → equiv-eq-map-Ω-eq-ap-Pointed-Type p q)

    equiv-fiber-map-Ω-connecting-map-Pointed-Type :
      (q : type-Ω B) →
      fiber (map-Ω g) q ≃
      ( map-pointed-map (connecting-map-Pointed-Type g) q ＝
        point-Pointed-Type (fiber-Pointed-Type g))
    equiv-fiber-map-Ω-connecting-map-Pointed-Type q =
      equiv-map-inv-fiber-ap-eq-fiber
        ( map-pointed-map g)
        ( map-pointed-map (connecting-map-Pointed-Type g) q)
        ( point-Pointed-Type (fiber-Pointed-Type g)) ∘e
      equiv-fiber-map-Ω-fiber-ap-Pointed-Type q

    equiv-fiber-connecting-map-Pointed-Type :
      type-Ω E ≃
      type-Pointed-Type (fiber-Pointed-Type (connecting-map-Pointed-Type g))
    equiv-fiber-connecting-map-Pointed-Type =
      equiv-tot equiv-fiber-map-Ω-connecting-map-Pointed-Type ∘e
      inv-equiv-total-fiber (map-Ω g)

    htpy-inclusion-fiber-connecting-map-Pointed-Type :
      (p : type-Ω E) →
      map-Ω g p ＝
      map-pointed-map
        ( inclusion-fiber-Pointed-Type (connecting-map-Pointed-Type g))
        ( map-equiv equiv-fiber-connecting-map-Pointed-Type p)
    htpy-inclusion-fiber-connecting-map-Pointed-Type p =
      refl

preserves-point-equiv-fiber-connecting-map-Pointed-Type :
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B) →
  map-equiv
    ( connecting-map-fiber-data.equiv-fiber-connecting-map-Pointed-Type g)
    ( refl) ＝
  point-Pointed-Type
    ( fiber-Pointed-Type (connecting-map-Pointed-Type g))
preserves-point-equiv-fiber-connecting-map-Pointed-Type (h , refl) =
  refl

pointed-equiv-fiber-connecting-map-Pointed-Type :
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B) →
  Ω E ≃∗ fiber-Pointed-Type (connecting-map-Pointed-Type g)
pr1 (pointed-equiv-fiber-connecting-map-Pointed-Type g) =
  connecting-map-fiber-data.equiv-fiber-connecting-map-Pointed-Type g
pr2 (pointed-equiv-fiber-connecting-map-Pointed-Type g) =
  preserves-point-equiv-fiber-connecting-map-Pointed-Type g

pointed-htpy-inclusion-fiber-connecting-map-Pointed-Type :
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B) →
  pointed-map-Ω g ~∗
  ( inclusion-fiber-Pointed-Type (connecting-map-Pointed-Type g) ∘∗
    pointed-map-pointed-equiv
      ( pointed-equiv-fiber-connecting-map-Pointed-Type g))
pr1 (pointed-htpy-inclusion-fiber-connecting-map-Pointed-Type g) =
  connecting-map-fiber-data.htpy-inclusion-fiber-connecting-map-Pointed-Type g
pr2 (pointed-htpy-inclusion-fiber-connecting-map-Pointed-Type (h , refl)) =
  refl

is-fiber-sequence-connecting-map-Pointed-Type :
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B) →
  is-fiber-sequence-Pointed-Type
    ( pointed-map-Ω g)
    ( connecting-map-Pointed-Type g)
pr1 (is-fiber-sequence-connecting-map-Pointed-Type g) =
  pointed-equiv-fiber-connecting-map-Pointed-Type g
pr2 (is-fiber-sequence-connecting-map-Pointed-Type g) =
  pointed-htpy-inclusion-fiber-connecting-map-Pointed-Type g

fiber-sequence-connecting-map-Pointed-Type :
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B) →
  fiber-sequence-Pointed-Type l1 l2 (l1 ⊔ l2)
pr1 (fiber-sequence-connecting-map-Pointed-Type {E = E} g) =
  Ω E
pr1 (pr2 (fiber-sequence-connecting-map-Pointed-Type {B = B} g)) =
  Ω B
pr1 (pr2 (pr2 (fiber-sequence-connecting-map-Pointed-Type g))) =
  fiber-Pointed-Type g
pr1 (pr2 (pr2 (pr2 (fiber-sequence-connecting-map-Pointed-Type g)))) =
  pointed-map-Ω g
pr1 (pr2 (pr2 (pr2 (pr2 (fiber-sequence-connecting-map-Pointed-Type g))))) =
  connecting-map-Pointed-Type g
pr2 (pr2 (pr2 (pr2 (pr2 (fiber-sequence-connecting-map-Pointed-Type g))))) =
  is-fiber-sequence-connecting-map-Pointed-Type g
```

### The connecting map of a packaged fiber sequence

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  connecting-map-fiber-sequence-Pointed-Type :
    Ω (base-fiber-sequence-Pointed-Type S) →∗
    fiber-fiber-sequence-Pointed-Type S
  connecting-map-fiber-sequence-Pointed-Type =
    pointed-map-inv-pointed-equiv
      ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S) ∘∗
    connecting-map-Pointed-Type
      ( fibration-fiber-sequence-Pointed-Type S)
```

### Comparing fibers after replacing the canonical fiber by the chosen fiber

```agda
  equiv-fiber-canonical-connecting-map-fiber-sequence-Pointed-Type :
    type-Pointed-Type
      ( fiber-Pointed-Type
        ( connecting-map-Pointed-Type
          ( fibration-fiber-sequence-Pointed-Type S))) ≃
    type-Pointed-Type
      ( fiber-Pointed-Type connecting-map-fiber-sequence-Pointed-Type)
  equiv-fiber-canonical-connecting-map-fiber-sequence-Pointed-Type =
    equiv-tot
      ( λ q →
        ( equiv-concat'
          ( map-pointed-map connecting-map-fiber-sequence-Pointed-Type q)
          ( preserves-point-map-inv-pointed-equiv
            ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))) ∘e
        ( equiv-ap
          ( equiv-inv-pointed-equiv
            ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))
          ( map-pointed-map
            ( connecting-map-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S))
            ( q))
          ( point-Pointed-Type
            ( fiber-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S)))))

  preserves-point-equiv-fiber-canonical-connecting-map-fiber-sequence-Pointed-Type :
    map-equiv
      ( equiv-fiber-canonical-connecting-map-fiber-sequence-Pointed-Type)
      ( point-Pointed-Type
        ( fiber-Pointed-Type
          ( connecting-map-Pointed-Type
            ( fibration-fiber-sequence-Pointed-Type S)))) ＝
    point-Pointed-Type
      ( fiber-Pointed-Type connecting-map-fiber-sequence-Pointed-Type)
  preserves-point-equiv-fiber-canonical-connecting-map-fiber-sequence-Pointed-Type =
    refl

  pointed-equiv-fiber-canonical-connecting-map-fiber-sequence-Pointed-Type :
    fiber-Pointed-Type
      ( connecting-map-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S)) ≃∗
    fiber-Pointed-Type connecting-map-fiber-sequence-Pointed-Type
  pr1 pointed-equiv-fiber-canonical-connecting-map-fiber-sequence-Pointed-Type =
    equiv-fiber-canonical-connecting-map-fiber-sequence-Pointed-Type
  pr2 pointed-equiv-fiber-canonical-connecting-map-fiber-sequence-Pointed-Type =
    preserves-point-equiv-fiber-canonical-connecting-map-fiber-sequence-Pointed-Type

  pointed-htpy-inclusion-fiber-canonical-connecting-map-fiber-sequence-Pointed-Type :
    inclusion-fiber-Pointed-Type
      ( connecting-map-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S)) ~∗
    ( inclusion-fiber-Pointed-Type connecting-map-fiber-sequence-Pointed-Type ∘∗
      pointed-map-pointed-equiv
        pointed-equiv-fiber-canonical-connecting-map-fiber-sequence-Pointed-Type)
  pr1
    pointed-htpy-inclusion-fiber-canonical-connecting-map-fiber-sequence-Pointed-Type
    u =
    refl
  pr2
    pointed-htpy-inclusion-fiber-canonical-connecting-map-fiber-sequence-Pointed-Type =
    refl
```

### Connecting fiber sequence of a packaged fiber sequence

```agda
  pointed-equiv-fiber-connecting-map-fiber-sequence-Pointed-Type :
    Ω (total-space-fiber-sequence-Pointed-Type S) ≃∗
    fiber-Pointed-Type connecting-map-fiber-sequence-Pointed-Type
  pointed-equiv-fiber-connecting-map-fiber-sequence-Pointed-Type =
    comp-pointed-equiv
      ( pointed-equiv-fiber-canonical-connecting-map-fiber-sequence-Pointed-Type)
      ( pointed-equiv-fiber-connecting-map-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))

  pointed-htpy-inclusion-fiber-connecting-map-fiber-sequence-Pointed-Type :
    pointed-map-Ω (fibration-fiber-sequence-Pointed-Type S) ~∗
    ( inclusion-fiber-Pointed-Type
      ( connecting-map-fiber-sequence-Pointed-Type) ∘∗
      pointed-map-pointed-equiv
        pointed-equiv-fiber-connecting-map-fiber-sequence-Pointed-Type)
  pointed-htpy-inclusion-fiber-connecting-map-fiber-sequence-Pointed-Type =
    concat-pointed-htpy
      ( pointed-htpy-inclusion-fiber-connecting-map-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))
      ( concat-pointed-htpy
        ( right-whisker-comp-pointed-htpy
          ( inclusion-fiber-Pointed-Type
            ( connecting-map-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S)))
          ( inclusion-fiber-Pointed-Type connecting-map-fiber-sequence-Pointed-Type ∘∗
            pointed-map-pointed-equiv
              pointed-equiv-fiber-canonical-connecting-map-fiber-sequence-Pointed-Type)
          ( pointed-htpy-inclusion-fiber-canonical-connecting-map-fiber-sequence-Pointed-Type)
          ( pointed-map-pointed-equiv
            ( pointed-equiv-fiber-connecting-map-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S))))
        ( associative-comp-pointed-map
          ( inclusion-fiber-Pointed-Type connecting-map-fiber-sequence-Pointed-Type)
          ( pointed-map-pointed-equiv
            pointed-equiv-fiber-canonical-connecting-map-fiber-sequence-Pointed-Type)
          ( pointed-map-pointed-equiv
            ( pointed-equiv-fiber-connecting-map-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S)))))

  is-fiber-sequence-connecting-map-fiber-sequence-Pointed-Type :
    is-fiber-sequence-Pointed-Type
      ( pointed-map-Ω (fibration-fiber-sequence-Pointed-Type S))
      ( connecting-map-fiber-sequence-Pointed-Type)
  pr1 is-fiber-sequence-connecting-map-fiber-sequence-Pointed-Type =
    pointed-equiv-fiber-connecting-map-fiber-sequence-Pointed-Type
  pr2 is-fiber-sequence-connecting-map-fiber-sequence-Pointed-Type =
    pointed-htpy-inclusion-fiber-connecting-map-fiber-sequence-Pointed-Type

  fiber-sequence-connecting-map-fiber-sequence-Pointed-Type :
    fiber-sequence-Pointed-Type l2 l3 l1
  pr1 fiber-sequence-connecting-map-fiber-sequence-Pointed-Type =
    Ω (total-space-fiber-sequence-Pointed-Type S)
  pr1 (pr2 fiber-sequence-connecting-map-fiber-sequence-Pointed-Type) =
    Ω (base-fiber-sequence-Pointed-Type S)
  pr1 (pr2 (pr2 fiber-sequence-connecting-map-fiber-sequence-Pointed-Type)) =
    fiber-fiber-sequence-Pointed-Type S
  pr1
    ( pr2 (pr2 (pr2 fiber-sequence-connecting-map-fiber-sequence-Pointed-Type))) =
    pointed-map-Ω (fibration-fiber-sequence-Pointed-Type S)
  pr1
    ( pr2
      ( pr2
        ( pr2
          ( pr2 fiber-sequence-connecting-map-fiber-sequence-Pointed-Type)))) =
    connecting-map-fiber-sequence-Pointed-Type
  pr2
    ( pr2
      ( pr2
        ( pr2
          ( pr2 fiber-sequence-connecting-map-fiber-sequence-Pointed-Type)))) =
    is-fiber-sequence-connecting-map-fiber-sequence-Pointed-Type
```
