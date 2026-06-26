# Fibers of boundary maps of pointed maps

```agda
module synthetic-homotopy-theory.fibers-boundary-maps-pointed-maps where
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

open import structured-types.constant-pointed-maps
open import structured-types.fiber-sequences
open import structured-types.fibers-of-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.connecting-fiber-sequences
open import synthetic-homotopy-theory.fiber-sequences-fiber-inclusions
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces-fibers-of-pointed-maps
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

The **boundary map** of a pointed map is the connecting map

```text
  Ω B →∗ fiber g.
```

This file records the boundary-map terminology and comparison adapters used in
the long exact sequence development. The structural fiber sequence itself lives
in
[`connecting-fiber-sequences`](synthetic-homotopy-theory.connecting-fiber-sequences.md);
this module gives the LES-facing names for the fiber of the boundary map and
the looped-boundary comparison.

## Lemmas

### Loop maps of constant pointed maps

The loop map of a constant pointed map is constant at the reflexivity loop.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  compute-map-equiv-equiv-ap-refl :
    (e : A ≃ B) (x : A) → map-equiv (equiv-ap e x x) refl ＝ refl
  compute-map-equiv-equiv-ap-refl e x =
    refl

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  eq-map-Ω-constant-pointed-map-Pointed-Type :
    (x : type-Ω A) →
    map-Ω (constant-pointed-map A B) x ＝ refl
  eq-map-Ω-constant-pointed-map-Pointed-Type x =
    ap-const (point-Pointed-Type B) x
```

### Computing `fiber-ap-eq-fiber` on fiberwise paths

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) {b : B}
  where

  compute-fiber-ap-eq-fiber-ap-pair :
    (x : A) (p r : f x ＝ b) (q : p ＝ r) →
    fiber-ap-eq-fiber f (x , p) (x , r) (ap (pair x) q) ＝
    ( refl ,
      tr
        ( λ u → refl ＝ p ∙ inv u)
        ( q)
        ( inv (right-inv p)))
  compute-fiber-ap-eq-fiber-ap-pair x p .p refl =
    refl

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

### The boundary map of a pointed map

The boundary-map name is retained for long exact sequence terminology.

```agda
module _
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B)
  where

  boundary-fiber-Pointed-Type : Ω B →∗ fiber-Pointed-Type g
  boundary-fiber-Pointed-Type =
    connecting-map-Pointed-Type g
```

### The fiber of the boundary map

```agda
module _
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

  eq-ap-concat-loop-preserves-point-Pointed-Type :
    {x : type-Pointed-Type E} (p : x ＝ point-Pointed-Type E)
    (q : type-Ω E) →
    ap (map-pointed-map g) (p ∙ q) ∙ preserves-point-pointed-map g ＝
    ( ap (map-pointed-map g) p ∙ preserves-point-pointed-map g) ∙
    map-Ω g q
  eq-ap-concat-loop-preserves-point-Pointed-Type p q =
    ( ap
      ( _∙ preserves-point-pointed-map g)
      ( ap-concat (map-pointed-map g) p q)) ∙
    ( assoc
      ( ap (map-pointed-map g) p)
      ( ap (map-pointed-map g) q)
      ( preserves-point-pointed-map g)) ∙
    ( ap
      ( ap (map-pointed-map g) p ∙_)
      ( ( ap
          ( _∙ preserves-point-pointed-map g)
          ( eq-ap-map-Ω-Pointed-Type q)) ∙
        ( assoc
          ( preserves-point-pointed-map g ∙ map-Ω g q)
          ( inv (preserves-point-pointed-map g))
          ( preserves-point-pointed-map g)) ∙
        ( ap
          ( (preserves-point-pointed-map g ∙ map-Ω g q) ∙_)
          ( left-inv (preserves-point-pointed-map g))) ∙
        ( right-unit))) ∙
    ( inv
      ( assoc
        ( ap (map-pointed-map g) p)
        ( preserves-point-pointed-map g)
        ( map-Ω g q)))

  eq-boundary-map-Ω-Pointed-Type :
    (p : type-Ω E) →
    map-pointed-map (boundary-fiber-Pointed-Type g) (map-Ω g p) ＝
    point-Pointed-Type (fiber-Pointed-Type g)
  eq-boundary-map-Ω-Pointed-Type p =
    map-inv-fiber-ap-eq-fiber
      ( map-pointed-map g)
      ( map-pointed-map (boundary-fiber-Pointed-Type g) (map-Ω g p))
      ( point-Pointed-Type (fiber-Pointed-Type g))
      ( p , eq-ap-map-Ω-Pointed-Type p)

  map-fiber-boundary-map-Ω-Pointed-Type :
    type-Ω E →
    type-Pointed-Type (fiber-Pointed-Type (boundary-fiber-Pointed-Type g))
  pr1 (map-fiber-boundary-map-Ω-Pointed-Type p) = map-Ω g p
  pr2 (map-fiber-boundary-map-Ω-Pointed-Type p) =
    eq-boundary-map-Ω-Pointed-Type p

  map-inv-fiber-boundary-map-Ω-Pointed-Type :
    type-Pointed-Type (fiber-Pointed-Type (boundary-fiber-Pointed-Type g)) →
    type-Ω E
  map-inv-fiber-boundary-map-Ω-Pointed-Type (q , α) = ap pr1 α

  is-retraction-map-inv-fiber-boundary-map-Ω-Pointed-Type :
    (p : type-Ω E) →
    map-inv-fiber-boundary-map-Ω-Pointed-Type
      ( map-fiber-boundary-map-Ω-Pointed-Type p) ＝ p
  is-retraction-map-inv-fiber-boundary-map-Ω-Pointed-Type p =
    ap-pr1-map-inv-fiber-ap-eq-fiber
      ( map-pointed-map g)
      ( map-pointed-map (boundary-fiber-Pointed-Type g) (map-Ω g p))
      ( point-Pointed-Type (fiber-Pointed-Type g))
      ( p , eq-ap-map-Ω-Pointed-Type p)

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

  eq-pr1-fiber-ap-eq-boundary-fiber-Pointed-Type :
    (q : type-Ω B)
    (α :
      map-pointed-map (boundary-fiber-Pointed-Type g) q ＝
      point-Pointed-Type (fiber-Pointed-Type g)) →
    pr1
      ( fiber-ap-eq-fiber
        ( map-pointed-map g)
        ( map-pointed-map (boundary-fiber-Pointed-Type g) q)
        ( point-Pointed-Type (fiber-Pointed-Type g))
        ( α)) ＝
    ap pr1 α
  eq-pr1-fiber-ap-eq-boundary-fiber-Pointed-Type q α =
    ap pr1
      ( triangle-fiber-ap-eq-fiber
        ( map-pointed-map g)
        ( map-pointed-map (boundary-fiber-Pointed-Type g) q)
        ( point-Pointed-Type (fiber-Pointed-Type g))
        ( α))

  eq-map-Ω-map-inv-fiber-boundary-map-Ω-Pointed-Type :
    (u :
      type-Pointed-Type (fiber-Pointed-Type (boundary-fiber-Pointed-Type g))) →
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
          ( map-pointed-map (boundary-fiber-Pointed-Type g) q)
          ( point-Pointed-Type (fiber-Pointed-Type g))
          ( α)))) ∙
    ( eq-tr-type-Ω-concat-inv-Pointed-Type
      ( preserves-point-pointed-map g)
      ( q))

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

  equiv-fiber-map-Ω-boundary-map-Ω-Pointed-Type :
    (q : type-Ω B) →
    fiber (map-Ω g) q ≃
    ( map-pointed-map (boundary-fiber-Pointed-Type g) q ＝
      point-Pointed-Type (fiber-Pointed-Type g))
  equiv-fiber-map-Ω-boundary-map-Ω-Pointed-Type q =
    equiv-map-inv-fiber-ap-eq-fiber
      ( map-pointed-map g)
      ( map-pointed-map (boundary-fiber-Pointed-Type g) q)
      ( point-Pointed-Type (fiber-Pointed-Type g)) ∘e
    equiv-fiber-map-Ω-fiber-ap-Pointed-Type q

  equiv-fiber-boundary-map-Ω-direct-Pointed-Type :
    type-Ω E ≃
    type-Pointed-Type (fiber-Pointed-Type (boundary-fiber-Pointed-Type g))
  equiv-fiber-boundary-map-Ω-direct-Pointed-Type =
    equiv-tot equiv-fiber-map-Ω-boundary-map-Ω-Pointed-Type ∘e
    inv-equiv-total-fiber (map-Ω g)

  htpy-inclusion-fiber-boundary-map-Ω-direct-Pointed-Type :
    (p : type-Ω E) →
    map-Ω g p ＝
    map-pointed-map
      ( inclusion-fiber-Pointed-Type (boundary-fiber-Pointed-Type g))
      ( map-equiv equiv-fiber-boundary-map-Ω-direct-Pointed-Type p)
  htpy-inclusion-fiber-boundary-map-Ω-direct-Pointed-Type p =
    refl

  compute-equiv-eq-map-Ω-eq-ap-refl-Pointed-Type :
    (p : type-Ω E) →
    map-equiv
      ( equiv-eq-map-Ω-eq-ap-Pointed-Type p (map-Ω g p))
      ( refl) ＝
    eq-ap-map-Ω-Pointed-Type p
  compute-equiv-eq-map-Ω-eq-ap-refl-Pointed-Type p =
    ( ap
      ( eq-ap-map-Ω-Pointed-Type p ∙_)
      ( compute-map-equiv-equiv-ap-refl
        ( equiv-map-inv-tr-type-Ω-concat-inv-Pointed-Type
          ( preserves-point-pointed-map g))
        ( map-Ω g p))) ∙
    ( right-unit)

  compute-equiv-fiber-map-Ω-boundary-map-Ω-map-fiber-boundary-Pointed-Type :
    (p : type-Ω E) →
    map-equiv
      ( equiv-fiber-map-Ω-boundary-map-Ω-Pointed-Type (map-Ω g p))
      ( p , refl) ＝
    eq-boundary-map-Ω-Pointed-Type p
  compute-equiv-fiber-map-Ω-boundary-map-Ω-map-fiber-boundary-Pointed-Type p =
    ap
      ( map-inv-fiber-ap-eq-fiber
        ( map-pointed-map g)
        ( map-pointed-map (boundary-fiber-Pointed-Type g) (map-Ω g p))
        ( point-Pointed-Type (fiber-Pointed-Type g)))
      ( eq-pair-Σ
        ( refl)
        ( compute-equiv-eq-map-Ω-eq-ap-refl-Pointed-Type p))

  eq-map-equiv-fiber-boundary-map-Ω-direct-map-fiber-boundary-Pointed-Type :
    (p : type-Ω E) →
    map-equiv equiv-fiber-boundary-map-Ω-direct-Pointed-Type p ＝
    map-fiber-boundary-map-Ω-Pointed-Type p
  eq-map-equiv-fiber-boundary-map-Ω-direct-map-fiber-boundary-Pointed-Type p =
    eq-pair-Σ
      ( refl)
      ( compute-equiv-fiber-map-Ω-boundary-map-Ω-map-fiber-boundary-Pointed-Type
        ( p))

  is-equiv-map-fiber-boundary-map-Ω-Pointed-Type :
    is-equiv map-fiber-boundary-map-Ω-Pointed-Type
  is-equiv-map-fiber-boundary-map-Ω-Pointed-Type =
    is-equiv-htpy-equiv
      ( equiv-fiber-boundary-map-Ω-direct-Pointed-Type)
      ( λ p →
        inv
          ( eq-map-equiv-fiber-boundary-map-Ω-direct-map-fiber-boundary-Pointed-Type
            ( p)))

  equiv-map-fiber-boundary-map-Ω-Pointed-Type :
    type-Ω E ≃
    type-Pointed-Type (fiber-Pointed-Type (boundary-fiber-Pointed-Type g))
  pr1 equiv-map-fiber-boundary-map-Ω-Pointed-Type =
    map-fiber-boundary-map-Ω-Pointed-Type
  pr2 equiv-map-fiber-boundary-map-Ω-Pointed-Type =
    is-equiv-map-fiber-boundary-map-Ω-Pointed-Type

  is-equiv-map-inv-fiber-boundary-map-Ω-Pointed-Type :
    is-equiv map-inv-fiber-boundary-map-Ω-Pointed-Type
  is-equiv-map-inv-fiber-boundary-map-Ω-Pointed-Type =
    is-equiv-is-retraction
      ( is-equiv-map-fiber-boundary-map-Ω-Pointed-Type)
      ( is-retraction-map-inv-fiber-boundary-map-Ω-Pointed-Type)

  equiv-map-inv-fiber-boundary-map-Ω-Pointed-Type :
    type-Pointed-Type (fiber-Pointed-Type (boundary-fiber-Pointed-Type g)) ≃
    type-Ω E
  pr1 equiv-map-inv-fiber-boundary-map-Ω-Pointed-Type =
    map-inv-fiber-boundary-map-Ω-Pointed-Type
  pr2 equiv-map-inv-fiber-boundary-map-Ω-Pointed-Type =
    is-equiv-map-inv-fiber-boundary-map-Ω-Pointed-Type

  is-section-map-inv-fiber-boundary-map-Ω-Pointed-Type :
    (u :
      type-Pointed-Type (fiber-Pointed-Type (boundary-fiber-Pointed-Type g))) →
    map-fiber-boundary-map-Ω-Pointed-Type
      ( map-inv-fiber-boundary-map-Ω-Pointed-Type u) ＝
    u
  is-section-map-inv-fiber-boundary-map-Ω-Pointed-Type u =
    inv
      ( htpy-map-inv-equiv-section
        ( equiv-map-inv-fiber-boundary-map-Ω-Pointed-Type)
        ( map-fiber-boundary-map-Ω-Pointed-Type ,
          is-retraction-map-inv-fiber-boundary-map-Ω-Pointed-Type)
        ( map-inv-fiber-boundary-map-Ω-Pointed-Type u)) ∙
    ( is-retraction-map-inv-equiv
      ( equiv-map-inv-fiber-boundary-map-Ω-Pointed-Type)
      ( u))

  eq-map-Ω-inclusion-fiber-Pointed-Type :
    (q : type-Ω (fiber-Pointed-Type g)) →
    map-Ω g (map-Ω (inclusion-fiber-Pointed-Type g) q) ＝ refl
  eq-map-Ω-inclusion-fiber-Pointed-Type q =
    ( inv
      ( preserves-comp-map-Ω
        ( g)
        ( inclusion-fiber-Pointed-Type g)
        ( q))) ∙
    ( htpy-map-Ω
      ( g ∘∗ inclusion-fiber-Pointed-Type g)
      ( constant-pointed-map (fiber-Pointed-Type g) B)
      ( null-htpy-comp-fibration-inclusion-fiber-Pointed-Type g)
      ( q)) ∙
    ( eq-map-Ω-constant-pointed-map-Pointed-Type q)
```

### Comparing with the fiber inclusion of the fiber inclusion

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h : A → B)
  (H : (x : A) → f x ＝ g (h x))
  where

  compute-fiber-triangle :
    (x : X) (u : fiber f x) →
    fiber-triangle f g h H x u ＝
    ( h (pr1 u) , inv (H (pr1 u)) ∙ pr2 u)
  compute-fiber-triangle .(f a) (a , refl) =
    eq-Eq-fiber g (f a) refl right-unit

module _
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B)
  where

  equiv-fiber-boundary-fiber-inclusion-boundary-fiber-Pointed-Type :
    type-Pointed-Type
      ( fiber-Pointed-Type (boundary-fiber-Pointed-Type g)) ≃
    type-Pointed-Type
      ( fiber-Pointed-Type
        ( inclusion-fiber-Pointed-Type (inclusion-fiber-Pointed-Type g)))
  pr1 equiv-fiber-boundary-fiber-inclusion-boundary-fiber-Pointed-Type =
    fiber-triangle
      ( map-pointed-map (boundary-fiber-Pointed-Type g))
      ( map-pointed-map
        ( inclusion-fiber-Pointed-Type (inclusion-fiber-Pointed-Type g)))
      ( map-pointed-equiv
        ( pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type g))
      ( pr1
        ( pointed-htpy-boundary-fiber-inclusion-boundary-fiber-Pointed-Type g))
      ( point-Pointed-Type (fiber-Pointed-Type g))
  pr2 equiv-fiber-boundary-fiber-inclusion-boundary-fiber-Pointed-Type =
    is-fiberwise-equiv-is-equiv-triangle
      ( map-pointed-map (boundary-fiber-Pointed-Type g))
      ( map-pointed-map
        ( inclusion-fiber-Pointed-Type (inclusion-fiber-Pointed-Type g)))
      ( map-pointed-equiv
        ( pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type g))
      ( pr1
        ( pointed-htpy-boundary-fiber-inclusion-boundary-fiber-Pointed-Type g))
      ( is-equiv-map-pointed-equiv
        ( pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type g))
      ( point-Pointed-Type (fiber-Pointed-Type g))

  preserves-point-equiv-fiber-boundary-fiber-inclusion-boundary-fiber-Pointed-Type :
    map-equiv
      ( equiv-fiber-boundary-fiber-inclusion-boundary-fiber-Pointed-Type)
      ( point-Pointed-Type
        ( fiber-Pointed-Type (boundary-fiber-Pointed-Type g))) ＝
    point-Pointed-Type
      ( fiber-Pointed-Type
        ( inclusion-fiber-Pointed-Type (inclusion-fiber-Pointed-Type g)))
  preserves-point-equiv-fiber-boundary-fiber-inclusion-boundary-fiber-Pointed-Type =
    compute-fiber-triangle
      ( map-pointed-map (boundary-fiber-Pointed-Type g))
      ( map-pointed-map
        ( inclusion-fiber-Pointed-Type (inclusion-fiber-Pointed-Type g)))
      ( map-pointed-equiv
        ( pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type g))
      ( pr1
        ( pointed-htpy-boundary-fiber-inclusion-boundary-fiber-Pointed-Type g))
      ( point-Pointed-Type (fiber-Pointed-Type g))
      ( point-Pointed-Type
        ( fiber-Pointed-Type (boundary-fiber-Pointed-Type g))) ∙
    eq-Eq-fiber
      ( map-pointed-map
        ( inclusion-fiber-Pointed-Type (inclusion-fiber-Pointed-Type g)))
      ( point-Pointed-Type (fiber-Pointed-Type g))
      ( preserves-point-pointed-equiv
        ( pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type g))
      ( inv
        ( pr2
          ( pointed-htpy-boundary-fiber-inclusion-boundary-fiber-Pointed-Type
            ( g))))

  pointed-equiv-fiber-boundary-fiber-inclusion-boundary-fiber-Pointed-Type :
    fiber-Pointed-Type (boundary-fiber-Pointed-Type g) ≃∗
    fiber-Pointed-Type
      ( inclusion-fiber-Pointed-Type (inclusion-fiber-Pointed-Type g))
  pr1 pointed-equiv-fiber-boundary-fiber-inclusion-boundary-fiber-Pointed-Type =
    equiv-fiber-boundary-fiber-inclusion-boundary-fiber-Pointed-Type
  pr2 pointed-equiv-fiber-boundary-fiber-inclusion-boundary-fiber-Pointed-Type =
    preserves-point-equiv-fiber-boundary-fiber-inclusion-boundary-fiber-Pointed-Type

  pointed-equiv-fiber-boundary-map-Ω-Pointed-Type :
    Ω E ≃∗
    fiber-Pointed-Type (boundary-fiber-Pointed-Type g)
  pointed-equiv-fiber-boundary-map-Ω-Pointed-Type =
    comp-pointed-equiv
      ( inv-pointed-equiv
        pointed-equiv-fiber-boundary-fiber-inclusion-boundary-fiber-Pointed-Type)
      ( pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type
        ( inclusion-fiber-Pointed-Type g))

  equiv-fiber-boundary-map-Ω-Pointed-Type :
    type-Ω E ≃
    type-Pointed-Type
      ( fiber-Pointed-Type (boundary-fiber-Pointed-Type g))
  equiv-fiber-boundary-map-Ω-Pointed-Type =
    equiv-pointed-equiv pointed-equiv-fiber-boundary-map-Ω-Pointed-Type
```

### The direct boundary-fiber equivalence preserves base points

```agda
module _
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  where

  eq-pr1-boundary-fiber-Pointed-Type :
    (g : E →∗ B) (q : type-Ω B) →
    pr1 (map-pointed-map (boundary-fiber-Pointed-Type g) q) ＝
    point-Pointed-Type E
  eq-pr1-boundary-fiber-Pointed-Type g q =
    refl

module _
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  where

  preserves-point-map-fiber-boundary-map-Ω-Pointed-Type :
    (g : E →∗ B) →
    map-fiber-boundary-map-Ω-Pointed-Type g refl ＝
    point-Pointed-Type
      ( fiber-Pointed-Type (boundary-fiber-Pointed-Type g))
  preserves-point-map-fiber-boundary-map-Ω-Pointed-Type (h , refl) =
    refl

  preserves-point-equiv-fiber-boundary-map-Ω-direct-Pointed-Type :
    (g : E →∗ B) →
    map-equiv (equiv-fiber-boundary-map-Ω-direct-Pointed-Type g) refl ＝
    point-Pointed-Type
      ( fiber-Pointed-Type (boundary-fiber-Pointed-Type g))
  preserves-point-equiv-fiber-boundary-map-Ω-direct-Pointed-Type (h , refl) =
    refl

  pointed-equiv-fiber-boundary-map-Ω-direct-Pointed-Type :
    (g : E →∗ B) →
    Ω E ≃∗ fiber-Pointed-Type (boundary-fiber-Pointed-Type g)
  pr1 (pointed-equiv-fiber-boundary-map-Ω-direct-Pointed-Type g) =
    equiv-fiber-boundary-map-Ω-direct-Pointed-Type g
  pr2 (pointed-equiv-fiber-boundary-map-Ω-direct-Pointed-Type g) =
    preserves-point-equiv-fiber-boundary-map-Ω-direct-Pointed-Type g

  pointed-htpy-inclusion-fiber-boundary-map-Ω-direct-Pointed-Type :
    (g : E →∗ B) →
    pointed-map-Ω g ~∗
    ( inclusion-fiber-Pointed-Type (boundary-fiber-Pointed-Type g) ∘∗
      pointed-map-pointed-equiv
        ( pointed-equiv-fiber-boundary-map-Ω-direct-Pointed-Type g))
  pr1 (pointed-htpy-inclusion-fiber-boundary-map-Ω-direct-Pointed-Type g) =
    htpy-inclusion-fiber-boundary-map-Ω-direct-Pointed-Type g
  pr2
    ( pointed-htpy-inclusion-fiber-boundary-map-Ω-direct-Pointed-Type
      ( h , refl)) =
    refl

  eq-pr1-map-equiv-fiber-boundary-map-Ω-direct-loop-inclusion-fiber-Pointed-Type :
    (g : E →∗ B) (q : type-Ω (fiber-Pointed-Type g)) →
    pr1
      ( map-equiv (equiv-fiber-boundary-map-Ω-direct-Pointed-Type g)
        ( map-Ω (inclusion-fiber-Pointed-Type g) q)) ＝
    pr1
      ( map-pointed-map
        ( boundary-fiber-Pointed-Type (boundary-fiber-Pointed-Type g))
        ( q))
  eq-pr1-map-equiv-fiber-boundary-map-Ω-direct-loop-inclusion-fiber-Pointed-Type
    g q =
    ( eq-map-Ω-inclusion-fiber-Pointed-Type g q) ∙
    ( inv
      ( eq-pr1-boundary-fiber-Pointed-Type
        ( boundary-fiber-Pointed-Type g)
        ( q)))

  eq-inv-preserves-point-boundary-fiber-concat-loop-Pointed-Type :
    (g : E →∗ B) (q : type-Ω (fiber-Pointed-Type g)) →
    inv (preserves-point-pointed-map (boundary-fiber-Pointed-Type g)) ∙
      ( preserves-point-pointed-map (boundary-fiber-Pointed-Type g) ∙ q) ＝
    q
  eq-inv-preserves-point-boundary-fiber-concat-loop-Pointed-Type g q =
    is-retraction-inv-concat
      ( preserves-point-pointed-map (boundary-fiber-Pointed-Type g))
      ( q)

  eq-ap-pr1-preserves-point-boundary-fiber-Pointed-Type :
    (g : E →∗ B) →
    ap pr1 (preserves-point-pointed-map (boundary-fiber-Pointed-Type g)) ＝ refl
  eq-ap-pr1-preserves-point-boundary-fiber-Pointed-Type g =
    ap-pr1-eq-pair-Σ refl right-unit

  eq-ap-pr1-preserves-point-boundary-fiber-concat-loop-Pointed-Type :
    (g : E →∗ B) (q : type-Ω (fiber-Pointed-Type g)) →
    ap pr1
      ( preserves-point-pointed-map (boundary-fiber-Pointed-Type g) ∙ q) ＝
    map-Ω (inclusion-fiber-Pointed-Type g) q
  eq-ap-pr1-preserves-point-boundary-fiber-concat-loop-Pointed-Type g q =
    ( ap-concat
      ( pr1)
      ( preserves-point-pointed-map (boundary-fiber-Pointed-Type g))
      ( q)) ∙
    ( ap
      ( _∙ ap pr1 q)
      ( eq-ap-pr1-preserves-point-boundary-fiber-Pointed-Type g)) ∙
    ( left-unit)

  eq-map-inv-fiber-boundary-map-Ω-boundary-boundary-Pointed-Type :
    (g : E →∗ B) (q : type-Ω (fiber-Pointed-Type g)) →
    map-inv-fiber-boundary-map-Ω-Pointed-Type g
      ( map-pointed-map
        ( boundary-fiber-Pointed-Type (boundary-fiber-Pointed-Type g))
        ( q)) ＝
    map-Ω (inclusion-fiber-Pointed-Type g) q
  eq-map-inv-fiber-boundary-map-Ω-boundary-boundary-Pointed-Type g q =
    eq-ap-pr1-preserves-point-boundary-fiber-concat-loop-Pointed-Type g q

  eq-map-equiv-fiber-boundary-map-Ω-direct-loop-inclusion-fiber-Pointed-Type :
    (g : E →∗ B) (q : type-Ω (fiber-Pointed-Type g)) →
    map-equiv (equiv-fiber-boundary-map-Ω-direct-Pointed-Type g)
      ( map-Ω (inclusion-fiber-Pointed-Type g) q) ＝
    map-pointed-map
      ( boundary-fiber-Pointed-Type (boundary-fiber-Pointed-Type g))
      ( q)
  eq-map-equiv-fiber-boundary-map-Ω-direct-loop-inclusion-fiber-Pointed-Type
    g q =
    ( eq-map-equiv-fiber-boundary-map-Ω-direct-map-fiber-boundary-Pointed-Type
      ( g)
      ( map-Ω (inclusion-fiber-Pointed-Type g) q)) ∙
    ( ap
      ( map-fiber-boundary-map-Ω-Pointed-Type g)
      ( inv
        ( eq-map-inv-fiber-boundary-map-Ω-boundary-boundary-Pointed-Type
          ( g)
          ( q)))) ∙
    ( is-section-map-inv-fiber-boundary-map-Ω-Pointed-Type
      ( g)
      ( map-pointed-map
        ( boundary-fiber-Pointed-Type (boundary-fiber-Pointed-Type g))
        ( q)))

  is-fiber-sequence-boundary-map-Ω-direct-Pointed-Type :
    (g : E →∗ B) →
    is-fiber-sequence-Pointed-Type
      ( pointed-map-Ω g)
      ( boundary-fiber-Pointed-Type g)
  is-fiber-sequence-boundary-map-Ω-direct-Pointed-Type =
    is-fiber-sequence-connecting-map-Pointed-Type

  fiber-sequence-boundary-map-Ω-direct-Pointed-Type :
    (g : E →∗ B) → fiber-sequence-Pointed-Type l1 l2 (l1 ⊔ l2)
  fiber-sequence-boundary-map-Ω-direct-Pointed-Type =
    fiber-sequence-connecting-map-Pointed-Type
```

### First projection of the looped boundary comparison

The loop of the canonical boundary of a pointed map has the expected first
projection after applying the loop-fiber equivalence. The full pointed
comparison is orientation-sensitive and is kept separate from this diagnostic
calculation.

```agda
eq-pr1-map-loop-fiber-map-Ω-boundary-fiber-Pointed-Type :
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B) (q : type-Ω (Ω B)) →
  pr1
    ( map-loop-fiber-Pointed-Type g
      ( map-Ω (boundary-fiber-Pointed-Type g) q)) ＝
  refl
eq-pr1-map-loop-fiber-map-Ω-boundary-fiber-Pointed-Type (h , refl) q =
  ( inv
    ( pr1
      ( pointed-htpy-loop-fiber-inclusion-Pointed-Type
        ( h , refl))
      ( map-Ω (boundary-fiber-Pointed-Type (h , refl)) q))) ∙
  ( inv
    ( preserves-comp-map-Ω
      ( inclusion-fiber-Pointed-Type (h , refl))
      ( boundary-fiber-Pointed-Type (h , refl))
      ( q))) ∙
  ( eq-map-Ω-constant-pointed-map-Pointed-Type q)

eq-map-inv-loop-fiber-boundary-Ω-Pointed-Type :
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B) (q : type-Ω (Ω B)) →
  map-inv-loop-fiber-Pointed-Type g
    ( map-pointed-map
      ( boundary-fiber-Pointed-Type (pointed-map-Ω g))
      ( q)) ＝
  map-Ω (boundary-fiber-Pointed-Type g) (ap inv q)
eq-map-inv-loop-fiber-boundary-Ω-Pointed-Type {E = E} {B = B} (h , refl) q =
  ( inv
    ( htpy-map-inv-fiber-ap-eq-fiber-map-inv-equiv
      ( h)
      ( point-Pointed-Type (fiber-Pointed-Type (h , refl)))
      ( point-Pointed-Type (fiber-Pointed-Type (h , refl)))
      ( map-pointed-map
        ( boundary-fiber-Pointed-Type (pointed-map-Ω (h , refl)))
        ( q)))) ∙
  ( ap
    ( eq-pair-eq-fiber
      { A = type-Pointed-Type E}
      { B = λ x → h x ＝ point-Pointed-Type B}
      { x = point-Pointed-Type E})
    ( ( ap concat-ap-inv-q eq-inv-inv-point) ∙
      right-unit))
  where
    eq-inv-inv-point :
      inv-inv
        ( pr2 (point-Pointed-Type (fiber-Pointed-Type (h , refl)))) ＝
      refl
    eq-inv-inv-point = refl

    concat-ap-inv-q :
      ( inv
        ( inv (pr2 (point-Pointed-Type (fiber-Pointed-Type (h , refl))))) ＝
        pr2 (point-Pointed-Type (fiber-Pointed-Type (h , refl)))) →
      inv (ap h refl) ＝
      pr2 (point-Pointed-Type (fiber-Pointed-Type (h , refl)))
    concat-ap-inv-q u = ap inv q ∙ u

eq-map-loop-fiber-map-Ω-boundary-fiber-Pointed-Type :
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B) (q : type-Ω (Ω B)) →
  map-loop-fiber-Pointed-Type g
    ( map-Ω (boundary-fiber-Pointed-Type g) (ap inv q)) ＝
  map-pointed-map
    ( boundary-fiber-Pointed-Type (pointed-map-Ω g))
    ( q)
eq-map-loop-fiber-map-Ω-boundary-fiber-Pointed-Type g q =
  ( inv
    ( ap
      ( map-loop-fiber-Pointed-Type g)
      ( eq-map-inv-loop-fiber-boundary-Ω-Pointed-Type g q))) ∙
  ( is-section-map-inv-loop-fiber-Pointed-Type g
    ( map-pointed-map
      ( boundary-fiber-Pointed-Type (pointed-map-Ω g))
      ( q)))
```
