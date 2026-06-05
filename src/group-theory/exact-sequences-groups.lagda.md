# Exact sequences of groups

```agda
module group-theory.exact-sequences-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.action-on-identifications-functions
open import foundation.equality-fibers-of-maps
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.groups
open import group-theory.homomorphisms-concrete-groups
open import group-theory.homomorphisms-groups
open import group-theory.images-of-group-homomorphisms
open import group-theory.kernels-homomorphisms-groups
open import group-theory.subgroups

open import structured-types.constant-pointed-maps
open import structured-types.fibers-of-pointed-maps
open import structured-types.fiber-sequences
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

A pair of composable group homomorphisms is exact when the image of the first
homomorphism is the kernel of the second.

For [concrete groups](group-theory.concrete-groups.md), we use the native
homotopical condition directly: the two classifying pointed maps form a
[fiber sequence](structured-types.fiber-sequences.md). The corresponding
ordinary group condition is `is-exact-hom-Group` applied to the underlying
group homomorphisms.

## Definitions

### Exactness of a pair of group homomorphisms

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (K : Group l3)
  (f : hom-Group G H) (g : hom-Group H K)
  where

  is-exact-hom-Group : UU (l1 ⊔ l2 ⊔ l3)
  is-exact-hom-Group =
    has-same-elements-Subgroup
      ( H)
      ( image-hom-Group G H f)
      ( subgroup-kernel-hom-Group H K g)
```

## Properties

### Null pointed maps induce trivial maps on underlying groups

```agda
module _
  {l1 l2 : Level} (A : Concrete-Group l1) (B : Concrete-Group l2)
  where

  map-Ω-constant-pointed-map :
    (x : type-Concrete-Group A) →
    map-Ω
      ( constant-pointed-map
        ( classifying-pointed-type-Concrete-Group A)
        ( classifying-pointed-type-Concrete-Group B))
      ( x) ＝ unit-Concrete-Group B
  map-Ω-constant-pointed-map x =
    ap-const (shape-Concrete-Group B) x

  is-in-kernel-hom-group-null-htpy-hom-Concrete-Group :
    (f : hom-Concrete-Group A B) →
    f ~∗
    constant-pointed-map
      ( classifying-pointed-type-Concrete-Group A)
      ( classifying-pointed-type-Concrete-Group B) →
    (x : type-Concrete-Group A) →
    is-in-kernel-hom-Group
      ( group-Concrete-Group A)
      ( group-Concrete-Group B)
      ( hom-group-hom-Concrete-Group A B f)
      ( x)
  is-in-kernel-hom-group-null-htpy-hom-Concrete-Group f H x =
    inv
      ( htpy-map-Ω
        ( f)
        ( constant-pointed-map
          ( classifying-pointed-type-Concrete-Group A)
          ( classifying-pointed-type-Concrete-Group B))
        ( H)
        ( x) ∙
        map-Ω-constant-pointed-map x)
```

### From fiber sequences to exactness

The forward implication should follow from applying loops to the fiber sequence
and identifying loops in the fiber of the classifying map of `g` with the
kernel subgroup of `g`.

```agda
eq-ap-is-in-kernel-tr-type-Ω :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {a : A} {b : B}
  (g : A → B) (p : g a ＝ b) (x : a ＝ a) →
  refl ＝ tr-type-Ω p (ap g x) → ap g x ＝ p ∙ inv p
eq-ap-is-in-kernel-tr-type-Ω g refl x H = inv H

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (g : A →∗ B)
  where

  eq-ap-is-in-kernel-map-Ω :
    (x : type-Ω A) →
    refl ＝ map-Ω g x →
    ap (map-pointed-map g) x ＝
    ( preserves-point-pointed-map g) ∙ inv (preserves-point-pointed-map g)
  eq-ap-is-in-kernel-map-Ω x =
    eq-ap-is-in-kernel-tr-type-Ω
      ( map-pointed-map g)
      ( preserves-point-pointed-map g)
      ( x)

  loop-fiber-is-in-kernel-map-Ω :
    (x : type-Ω A) →
    refl ＝ map-Ω g x →
    type-Ω (fiber-Pointed-Type g)
  loop-fiber-is-in-kernel-map-Ω x H =
    map-inv-fiber-ap-eq-fiber
      ( map-pointed-map g)
      ( point-Pointed-Type (fiber-Pointed-Type g))
      ( point-Pointed-Type (fiber-Pointed-Type g))
      ( x , eq-ap-is-in-kernel-map-Ω x H)

  map-Ω-inclusion-loop-fiber-is-in-kernel-map-Ω :
    (x : type-Ω A) (H : refl ＝ map-Ω g x) →
    map-Ω
      ( inclusion-fiber-Pointed-Type g)
      ( loop-fiber-is-in-kernel-map-Ω x H) ＝
    x
  map-Ω-inclusion-loop-fiber-is-in-kernel-map-Ω x H =
    ap-pr1-map-inv-fiber-ap-eq-fiber
      ( map-pointed-map g)
      ( point-Pointed-Type (fiber-Pointed-Type g))
      ( point-Pointed-Type (fiber-Pointed-Type g))
      ( x , eq-ap-is-in-kernel-map-Ω x H)

module _
  {l1 l2 l3 : Level}
  (G : Concrete-Group l1) (H : Concrete-Group l2) (K : Concrete-Group l3)
  (f : hom-Concrete-Group G H) (g : hom-Concrete-Group H K)
  where

  fiber-sequence-is-fiber-sequence-hom-Concrete-Group :
    is-fiber-sequence-Pointed-Type f g →
    fiber-sequence-Pointed-Type l1 l2 l3
  fiber-sequence-is-fiber-sequence-hom-Concrete-Group S =
    pair
      ( classifying-pointed-type-Concrete-Group G)
      ( pair
        ( classifying-pointed-type-Concrete-Group H)
        ( pair
          ( classifying-pointed-type-Concrete-Group K)
          ( pair f (pair g S))))

  null-htpy-comp-is-fiber-sequence-hom-Concrete-Group :
    (S : is-fiber-sequence-Pointed-Type f g) →
    (g ∘∗ f) ~∗
    constant-pointed-map
      ( classifying-pointed-type-Concrete-Group G)
      ( classifying-pointed-type-Concrete-Group K)
  null-htpy-comp-is-fiber-sequence-hom-Concrete-Group S =
    null-htpy-comp-fibration-fiber-inclusion-fiber-sequence-Pointed-Type
      ( fiber-sequence-is-fiber-sequence-hom-Concrete-Group S)

  leq-kernel-image-is-fiber-sequence-hom-Concrete-Group :
    is-fiber-sequence-Pointed-Type f g →
    leq-Subgroup
      ( group-Concrete-Group H)
      ( image-hom-Group
        ( group-Concrete-Group G)
        ( group-Concrete-Group H)
        ( hom-group-hom-Concrete-Group G H f))
      ( subgroup-kernel-hom-Group
        ( group-Concrete-Group H)
        ( group-Concrete-Group K)
        ( hom-group-hom-Concrete-Group H K g))
  leq-kernel-image-is-fiber-sequence-hom-Concrete-Group S y u =
    apply-universal-property-trunc-Prop u
      ( subset-kernel-hom-Group
        ( group-Concrete-Group H)
        ( group-Concrete-Group K)
        ( hom-group-hom-Concrete-Group H K g)
        ( y))
      ( λ where
        (x , refl) →
          ( is-in-kernel-hom-group-null-htpy-hom-Concrete-Group G K
            ( comp-hom-Concrete-Group G H K g f)
            ( null-htpy-comp-is-fiber-sequence-hom-Concrete-Group S)
            ( x)) ∙
          ( preserves-comp-map-Ω g f x))

  leq-image-kernel-is-fiber-sequence-hom-Concrete-Group :
    is-fiber-sequence-Pointed-Type f g →
    leq-Subgroup
      ( group-Concrete-Group H)
      ( subgroup-kernel-hom-Group
        ( group-Concrete-Group H)
        ( group-Concrete-Group K)
        ( hom-group-hom-Concrete-Group H K g))
      ( image-hom-Group
        ( group-Concrete-Group G)
        ( group-Concrete-Group H)
        ( hom-group-hom-Concrete-Group G H f))
  leq-image-kernel-is-fiber-sequence-hom-Concrete-Group S y H =
    unit-trunc-Prop
      ( map-inv-equiv
        ( equiv-Ω-pointed-equiv
          ( pointed-equiv-fiber-fiber-sequence-Pointed-Type
            ( fiber-sequence-is-fiber-sequence-hom-Concrete-Group S)))
        ( loop-fiber-is-in-kernel-map-Ω g y H) ,
        ( htpy-map-Ω
          ( f)
          ( inclusion-fiber-Pointed-Type g ∘∗
            pointed-map-fiber-fiber-sequence-Pointed-Type
              ( fiber-sequence-is-fiber-sequence-hom-Concrete-Group S))
          ( pointed-htpy-fiber-inclusion-fiber-sequence-Pointed-Type
            ( fiber-sequence-is-fiber-sequence-hom-Concrete-Group S))
          ( map-inv-equiv
            ( equiv-Ω-pointed-equiv
              ( pointed-equiv-fiber-fiber-sequence-Pointed-Type
                ( fiber-sequence-is-fiber-sequence-hom-Concrete-Group S)))
            ( loop-fiber-is-in-kernel-map-Ω g y H))) ∙
        ( preserves-comp-map-Ω
          ( inclusion-fiber-Pointed-Type g)
          ( pointed-map-fiber-fiber-sequence-Pointed-Type
            ( fiber-sequence-is-fiber-sequence-hom-Concrete-Group S))
          ( map-inv-equiv
            ( equiv-Ω-pointed-equiv
              ( pointed-equiv-fiber-fiber-sequence-Pointed-Type
                ( fiber-sequence-is-fiber-sequence-hom-Concrete-Group S)))
            ( loop-fiber-is-in-kernel-map-Ω g y H))) ∙
        ( ap
          ( map-Ω (inclusion-fiber-Pointed-Type g))
          ( is-section-map-inv-equiv
            ( equiv-Ω-pointed-equiv
              ( pointed-equiv-fiber-fiber-sequence-Pointed-Type
                ( fiber-sequence-is-fiber-sequence-hom-Concrete-Group S)))
            ( loop-fiber-is-in-kernel-map-Ω g y H))) ∙
        ( map-Ω-inclusion-loop-fiber-is-in-kernel-map-Ω g y H))

  is-exact-is-fiber-sequence-hom-Concrete-Group :
    is-fiber-sequence-Pointed-Type f g →
    is-exact-hom-Group
      ( group-Concrete-Group G)
      ( group-Concrete-Group H)
      ( group-Concrete-Group K)
      ( hom-group-hom-Concrete-Group G H f)
      ( hom-group-hom-Concrete-Group H K g)
  pr1 (is-exact-is-fiber-sequence-hom-Concrete-Group S y) =
    leq-kernel-image-is-fiber-sequence-hom-Concrete-Group S y
  pr2 (is-exact-is-fiber-sequence-hom-Concrete-Group S y) =
    leq-image-kernel-is-fiber-sequence-hom-Concrete-Group S y
```
