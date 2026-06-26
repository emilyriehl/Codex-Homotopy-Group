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

open import synthetic-homotopy-theory.functoriality-homotopy-groups
open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.iterated-loop-spaces
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

## Definitions

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

### The loop space of the fiber of a pointed map

```agda
module _
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  where

  map-loop-fiber-Pointed-Type :
    (g : E →∗ B) →
    type-Ω (fiber-Pointed-Type g) →
    type-Pointed-Type (fiber-Pointed-Type (pointed-map-Ω g))
  map-loop-fiber-Pointed-Type (g , refl) x =
    fiber-ap-eq-fiber
      ( g)
      ( point-Pointed-Type (fiber-Pointed-Type (g , refl)))
      ( point-Pointed-Type (fiber-Pointed-Type (g , refl)))
      ( x)

  map-inv-loop-fiber-Pointed-Type :
    (g : E →∗ B) →
    type-Pointed-Type (fiber-Pointed-Type (pointed-map-Ω g)) →
    type-Ω (fiber-Pointed-Type g)
  map-inv-loop-fiber-Pointed-Type (g , refl) =
    map-inv-equiv
      ( equiv-fiber-ap-eq-fiber
        ( g)
        ( point-Pointed-Type (fiber-Pointed-Type (g , refl)))
        ( point-Pointed-Type (fiber-Pointed-Type (g , refl))))

  is-section-map-inv-loop-fiber-Pointed-Type :
    (g : E →∗ B) →
    (x : type-Pointed-Type (fiber-Pointed-Type (pointed-map-Ω g))) →
    map-loop-fiber-Pointed-Type g (map-inv-loop-fiber-Pointed-Type g x) ＝ x
  is-section-map-inv-loop-fiber-Pointed-Type (g , refl) =
    is-section-map-inv-equiv
      ( equiv-fiber-ap-eq-fiber
        ( g)
        ( point-Pointed-Type (fiber-Pointed-Type (g , refl)))
        ( point-Pointed-Type (fiber-Pointed-Type (g , refl))))

  is-retraction-map-inv-loop-fiber-Pointed-Type :
    (g : E →∗ B) →
    (x : type-Ω (fiber-Pointed-Type g)) →
    map-inv-loop-fiber-Pointed-Type g (map-loop-fiber-Pointed-Type g x) ＝ x
  is-retraction-map-inv-loop-fiber-Pointed-Type (g , refl) =
    is-retraction-map-inv-equiv
      ( equiv-fiber-ap-eq-fiber
        ( g)
        ( point-Pointed-Type (fiber-Pointed-Type (g , refl)))
        ( point-Pointed-Type (fiber-Pointed-Type (g , refl))))

  is-equiv-map-loop-fiber-Pointed-Type :
    (g : E →∗ B) → is-equiv (map-loop-fiber-Pointed-Type g)
  is-equiv-map-loop-fiber-Pointed-Type g =
    is-equiv-is-invertible
      ( map-inv-loop-fiber-Pointed-Type g)
      ( is-section-map-inv-loop-fiber-Pointed-Type g)
      ( is-retraction-map-inv-loop-fiber-Pointed-Type g)

  equiv-loop-fiber-Pointed-Type :
    (g : E →∗ B) →
    type-Ω (fiber-Pointed-Type g) ≃
    type-Pointed-Type (fiber-Pointed-Type (pointed-map-Ω g))
  pr1 (equiv-loop-fiber-Pointed-Type g) = map-loop-fiber-Pointed-Type g
  pr2 (equiv-loop-fiber-Pointed-Type g) = is-equiv-map-loop-fiber-Pointed-Type g

  preserves-point-map-loop-fiber-Pointed-Type :
    (g : E →∗ B) →
    map-equiv (equiv-loop-fiber-Pointed-Type g) refl ＝
    point-Pointed-Type (fiber-Pointed-Type (pointed-map-Ω g))
  preserves-point-map-loop-fiber-Pointed-Type (g , refl) =
    refl

  pointed-equiv-loop-fiber-Pointed-Type :
    (g : E →∗ B) →
    Ω (fiber-Pointed-Type g) ≃∗ fiber-Pointed-Type (pointed-map-Ω g)
  pr1 (pointed-equiv-loop-fiber-Pointed-Type g) = equiv-loop-fiber-Pointed-Type g
  pr2 (pointed-equiv-loop-fiber-Pointed-Type g) =
    preserves-point-map-loop-fiber-Pointed-Type g

  pointed-htpy-loop-fiber-inclusion-Pointed-Type :
    (g : E →∗ B) →
    pointed-map-Ω (inclusion-fiber-Pointed-Type g) ~∗
    ( inclusion-fiber-Pointed-Type (pointed-map-Ω g) ∘∗
      pointed-map-pointed-equiv (pointed-equiv-loop-fiber-Pointed-Type g))
  pr1 (pointed-htpy-loop-fiber-inclusion-Pointed-Type (g , refl)) x =
    inv
      ( ap pr1
        ( triangle-fiber-ap-eq-fiber
          ( g)
          ( point-Pointed-Type (fiber-Pointed-Type (g , refl)))
          ( point-Pointed-Type (fiber-Pointed-Type (g , refl)))
          ( x)))
  pr2 (pointed-htpy-loop-fiber-inclusion-Pointed-Type (g , refl)) =
    refl

```

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
    ( map-pointed-map boundary-fiber-Pointed-Type q ＝
      point-Pointed-Type (fiber-Pointed-Type g))
  equiv-fiber-map-Ω-boundary-map-Ω-Pointed-Type q =
    equiv-map-inv-fiber-ap-eq-fiber
      ( map-pointed-map g)
      ( map-pointed-map boundary-fiber-Pointed-Type q)
      ( point-Pointed-Type (fiber-Pointed-Type g)) ∘e
    equiv-fiber-map-Ω-fiber-ap-Pointed-Type q

  equiv-fiber-boundary-map-Ω-direct-Pointed-Type :
    type-Ω E ≃
    type-Pointed-Type (fiber-Pointed-Type boundary-fiber-Pointed-Type)
  equiv-fiber-boundary-map-Ω-direct-Pointed-Type =
    equiv-tot equiv-fiber-map-Ω-boundary-map-Ω-Pointed-Type ∘e
    inv-equiv-total-fiber (map-Ω g)

  htpy-inclusion-fiber-boundary-map-Ω-direct-Pointed-Type :
    (p : type-Ω E) →
    map-Ω g p ＝
    map-pointed-map
      ( inclusion-fiber-Pointed-Type boundary-fiber-Pointed-Type)
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
        ( map-pointed-map boundary-fiber-Pointed-Type (map-Ω g p))
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
      ( compute-equiv-fiber-map-Ω-boundary-map-Ω-map-fiber-boundary-Pointed-Type p)

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
    type-Pointed-Type (fiber-Pointed-Type boundary-fiber-Pointed-Type)
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
    type-Pointed-Type (fiber-Pointed-Type boundary-fiber-Pointed-Type) ≃
    type-Ω E
  pr1 equiv-map-inv-fiber-boundary-map-Ω-Pointed-Type =
    map-inv-fiber-boundary-map-Ω-Pointed-Type
  pr2 equiv-map-inv-fiber-boundary-map-Ω-Pointed-Type =
    is-equiv-map-inv-fiber-boundary-map-Ω-Pointed-Type

  is-section-map-inv-fiber-boundary-map-Ω-Pointed-Type :
    (u : type-Pointed-Type (fiber-Pointed-Type boundary-fiber-Pointed-Type)) →
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

### The fiber of the boundary map

The fiber of the boundary map is identified structurally, by comparing the
boundary map with the fiber inclusion of the fiber inclusion.

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
      ( pr1 (pointed-htpy-boundary-fiber-inclusion-boundary-fiber-Pointed-Type g))
      ( point-Pointed-Type (fiber-Pointed-Type g))
  pr2 equiv-fiber-boundary-fiber-inclusion-boundary-fiber-Pointed-Type =
    is-fiberwise-equiv-is-equiv-triangle
      ( map-pointed-map (boundary-fiber-Pointed-Type g))
      ( map-pointed-map
        ( inclusion-fiber-Pointed-Type (inclusion-fiber-Pointed-Type g)))
      ( map-pointed-equiv
        ( pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type g))
      ( pr1 (pointed-htpy-boundary-fiber-inclusion-boundary-fiber-Pointed-Type g))
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
      ( pr1 (pointed-htpy-boundary-fiber-inclusion-boundary-fiber-Pointed-Type g))
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
          ( pointed-htpy-boundary-fiber-inclusion-boundary-fiber-Pointed-Type g)))

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
  pr1 (is-fiber-sequence-boundary-map-Ω-direct-Pointed-Type g) =
    pointed-equiv-fiber-boundary-map-Ω-direct-Pointed-Type g
  pr2 (is-fiber-sequence-boundary-map-Ω-direct-Pointed-Type g) =
    pointed-htpy-inclusion-fiber-boundary-map-Ω-direct-Pointed-Type g

  fiber-sequence-boundary-map-Ω-direct-Pointed-Type :
    (g : E →∗ B) → fiber-sequence-Pointed-Type l1 l2 (l1 ⊔ l2)
  pr1 (fiber-sequence-boundary-map-Ω-direct-Pointed-Type g) =
    Ω E
  pr1 (pr2 (fiber-sequence-boundary-map-Ω-direct-Pointed-Type g)) =
    Ω B
  pr1 (pr2 (pr2 (fiber-sequence-boundary-map-Ω-direct-Pointed-Type g))) =
    fiber-Pointed-Type g
  pr1 (pr2 (pr2 (pr2 (fiber-sequence-boundary-map-Ω-direct-Pointed-Type g)))) =
    pointed-map-Ω g
  pr1 (pr2 (pr2 (pr2 (pr2 (fiber-sequence-boundary-map-Ω-direct-Pointed-Type g))))) =
    boundary-fiber-Pointed-Type g
  pr2 (pr2 (pr2 (pr2 (pr2 (fiber-sequence-boundary-map-Ω-direct-Pointed-Type g))))) =
    is-fiber-sequence-boundary-map-Ω-direct-Pointed-Type g

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

```

### Pointed equivalence algebra

```agda
pointed-htpy-Ω-inv-pointed-equiv :
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (e : A ≃∗ B) →
  pointed-map-Ω (pointed-map-inv-pointed-equiv e) ~∗
  pointed-map-inv-pointed-equiv (pointed-equiv-Ω-pointed-equiv e)
pointed-htpy-Ω-inv-pointed-equiv e =
  concat-pointed-htpy
    ( inv-left-unit-law-comp-pointed-map
      ( pointed-map-Ω (pointed-map-inv-pointed-equiv e)))
    ( concat-pointed-htpy
      ( right-whisker-comp-pointed-htpy
        ( id-pointed-map)
        ( pointed-map-inv-pointed-equiv (pointed-equiv-Ω-pointed-equiv e) ∘∗
          pointed-map-pointed-equiv (pointed-equiv-Ω-pointed-equiv e))
        ( inv-pointed-htpy
          ( is-pointed-retraction-pointed-map-inv-pointed-equiv
            ( pointed-equiv-Ω-pointed-equiv e)))
        ( pointed-map-Ω (pointed-map-inv-pointed-equiv e)))
      ( concat-pointed-htpy
        ( associative-comp-pointed-map
          ( pointed-map-inv-pointed-equiv (pointed-equiv-Ω-pointed-equiv e))
          ( pointed-map-pointed-equiv (pointed-equiv-Ω-pointed-equiv e))
          ( pointed-map-Ω (pointed-map-inv-pointed-equiv e)))
        ( concat-pointed-htpy
          ( left-whisker-comp-pointed-htpy
            ( pointed-map-inv-pointed-equiv (pointed-equiv-Ω-pointed-equiv e))
            ( pointed-map-pointed-equiv (pointed-equiv-Ω-pointed-equiv e) ∘∗
              pointed-map-Ω (pointed-map-inv-pointed-equiv e))
            ( id-pointed-map)
            ( concat-pointed-htpy
              ( inv-pointed-htpy
                ( preserves-comp-pointed-map-Ω
                  ( pointed-map-pointed-equiv e)
                  ( pointed-map-inv-pointed-equiv e)))
              ( concat-pointed-htpy
                ( pointed-htpy-Ω
                  ( pointed-map-pointed-equiv e ∘∗
                    pointed-map-inv-pointed-equiv e)
                  ( id-pointed-map)
                  ( is-pointed-section-pointed-map-inv-pointed-equiv e))
                ( preserves-id-pointed-map-Ω))))
          ( right-unit-law-comp-pointed-map
            ( pointed-map-inv-pointed-equiv
              ( pointed-equiv-Ω-pointed-equiv e))))))

is-retraction-map-Ω-pointed-map-inv-pointed-equiv :
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (e : A ≃∗ B) (q : type-Ω A) →
  map-Ω (pointed-map-inv-pointed-equiv e)
    ( map-Ω (pointed-map-pointed-equiv e) q) ＝
  q
is-retraction-map-Ω-pointed-map-inv-pointed-equiv e q =
  ( pr1 (pointed-htpy-Ω-inv-pointed-equiv e)
    ( map-Ω (pointed-map-pointed-equiv e) q)) ∙
  ( is-retraction-map-inv-equiv (equiv-Ω-pointed-equiv e) q)

pointed-htpy-section-explicit-inv-comp-pointed-equiv :
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  (e : A ≃∗ B) (f : B ≃∗ C) →
  ( pointed-map-pointed-equiv (comp-pointed-equiv f e) ∘∗
    ( pointed-map-inv-pointed-equiv e ∘∗
      pointed-map-inv-pointed-equiv f)) ~∗
  id-pointed-map
pointed-htpy-section-explicit-inv-comp-pointed-equiv e f =
  concat-pointed-htpy
    ( associative-comp-pointed-map
      ( pointed-map-pointed-equiv f)
      ( pointed-map-pointed-equiv e)
      ( pointed-map-inv-pointed-equiv e ∘∗
        pointed-map-inv-pointed-equiv f))
    ( concat-pointed-htpy
      ( left-whisker-comp-pointed-htpy
        ( pointed-map-pointed-equiv f)
        ( pointed-map-pointed-equiv e ∘∗
          ( pointed-map-inv-pointed-equiv e ∘∗
            pointed-map-inv-pointed-equiv f))
        ( ( pointed-map-pointed-equiv e ∘∗
            pointed-map-inv-pointed-equiv e) ∘∗
          pointed-map-inv-pointed-equiv f)
        ( inv-associative-comp-pointed-map
          ( pointed-map-pointed-equiv e)
          ( pointed-map-inv-pointed-equiv e)
          ( pointed-map-inv-pointed-equiv f)))
      ( concat-pointed-htpy
        ( left-whisker-comp-pointed-htpy
          ( pointed-map-pointed-equiv f)
          ( ( pointed-map-pointed-equiv e ∘∗
              pointed-map-inv-pointed-equiv e) ∘∗
            pointed-map-inv-pointed-equiv f)
          ( pointed-map-inv-pointed-equiv f)
          ( concat-pointed-htpy
            ( right-whisker-comp-pointed-htpy
              ( pointed-map-pointed-equiv e ∘∗
                pointed-map-inv-pointed-equiv e)
              ( id-pointed-map)
              ( is-pointed-section-pointed-map-inv-pointed-equiv e)
              ( pointed-map-inv-pointed-equiv f))
            ( left-unit-law-comp-pointed-map
              ( pointed-map-inv-pointed-equiv f))))
        ( is-pointed-section-pointed-map-inv-pointed-equiv f)))

pointed-htpy-inv-comp-pointed-equiv :
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  (e : A ≃∗ B) (f : B ≃∗ C) →
  ( pointed-map-inv-pointed-equiv e ∘∗
    pointed-map-inv-pointed-equiv f) ~∗
  pointed-map-inv-pointed-equiv (comp-pointed-equiv f e)
pointed-htpy-inv-comp-pointed-equiv e f =
  concat-pointed-htpy
    ( inv-left-unit-law-comp-pointed-map
      ( pointed-map-inv-pointed-equiv e ∘∗
        pointed-map-inv-pointed-equiv f))
    ( concat-pointed-htpy
      ( right-whisker-comp-pointed-htpy
        ( id-pointed-map)
        ( pointed-map-inv-pointed-equiv (comp-pointed-equiv f e) ∘∗
          pointed-map-pointed-equiv (comp-pointed-equiv f e))
        ( inv-pointed-htpy
          ( is-pointed-retraction-pointed-map-inv-pointed-equiv
            ( comp-pointed-equiv f e)))
        ( pointed-map-inv-pointed-equiv e ∘∗
          pointed-map-inv-pointed-equiv f))
      ( concat-pointed-htpy
        ( associative-comp-pointed-map
          ( pointed-map-inv-pointed-equiv (comp-pointed-equiv f e))
          ( pointed-map-pointed-equiv (comp-pointed-equiv f e))
          ( pointed-map-inv-pointed-equiv e ∘∗
            pointed-map-inv-pointed-equiv f))
        ( concat-pointed-htpy
          ( left-whisker-comp-pointed-htpy
            ( pointed-map-inv-pointed-equiv (comp-pointed-equiv f e))
            ( pointed-map-pointed-equiv (comp-pointed-equiv f e) ∘∗
              ( pointed-map-inv-pointed-equiv e ∘∗
                pointed-map-inv-pointed-equiv f))
            ( id-pointed-map)
            ( pointed-htpy-section-explicit-inv-comp-pointed-equiv e f))
          ( right-unit-law-comp-pointed-map
            ( pointed-map-inv-pointed-equiv
              ( comp-pointed-equiv f e))))))

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
