# Exact sequences of pointed sets

```agda
module structured-types.exact-sequences-pointed-sets where

open import structured-types.pointed-sets public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.functoriality-set-truncation
open import foundation.images
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.set-truncations
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import structured-types.fiber-sequences
open import structured-types.fibers-of-pointed-maps
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

An **exact sequence of pointed sets** is a sequence of pointed sets and pointed
maps whose image at each middle term is equal to the kernel of the following
map. This uses [pointed sets](structured-types.pointed-sets.md) as the
ambient structure. It is the pointed-set version used in the proof of the
[long exact sequence of homotopy groups](synthetic-homotopy-theory.long-exact-sequence-homotopy-groups.md):
first apply set truncation to the fiber sequence of a pointed map, then prove
that each adjacent triple is exact.

## Definitions

### Images and kernels of pointed maps of pointed sets

```agda
module _
  {l1 l2 : Level} {A : Pointed-Set l1} {B : Pointed-Set l2}
  (f : hom-Pointed-Set A B)
  where

  subtype-image-hom-Pointed-Set : subtype (l1 ⊔ l2) (type-Pointed-Set B)
  subtype-image-hom-Pointed-Set = subtype-im (map-pointed-map f)

  is-in-image-hom-Pointed-Set : type-Pointed-Set B → UU (l1 ⊔ l2)
  is-in-image-hom-Pointed-Set =
    is-in-subtype subtype-image-hom-Pointed-Set

module _
  {l1 l2 : Level} {A : Pointed-Set l1} {B : Pointed-Set l2}
  (f : hom-Pointed-Set A B)
  where

  subtype-kernel-hom-Pointed-Set : subtype l2 (type-Pointed-Set A)
  subtype-kernel-hom-Pointed-Set x =
    Id-Prop
      ( set-Pointed-Set B)
      ( map-pointed-map f x)
      ( point-Pointed-Set B)

  is-in-kernel-hom-Pointed-Set : type-Pointed-Set A → UU l2
  is-in-kernel-hom-Pointed-Set =
    is-in-subtype subtype-kernel-hom-Pointed-Set
```

### Exactness of a pair of pointed maps of pointed sets

```agda
module _
  {l1 l2 l3 : Level}
  (A : Pointed-Set l1) (B : Pointed-Set l2) (C : Pointed-Set l3)
  (f : hom-Pointed-Set A B) (g : hom-Pointed-Set B C)
  where

  is-exact-hom-Pointed-Set : UU (l1 ⊔ l2 ⊔ l3)
  is-exact-hom-Pointed-Set =
    (x : type-Pointed-Set B) →
    is-in-image-hom-Pointed-Set {A = A} {B = B} f x ↔
    is-in-kernel-hom-Pointed-Set {A = B} {B = C} g x
```

## Properties

### Exactness transports along identifications of pointed-set triples

```agda
module _
  {l1 l2 l3 : Level}
  {A A' : Pointed-Set l1} {B B' : Pointed-Set l2} {C C' : Pointed-Set l3}
  where

  is-exact-hom-Pointed-Set-tr :
    (pA : A' ＝ A) (pB : B' ＝ B) (pC : C' ＝ C)
    (f : hom-Pointed-Set A B) (g : hom-Pointed-Set B C)
    (f' : hom-Pointed-Set A' B') (g' : hom-Pointed-Set B' C') →
    tr
      (λ X → hom-Pointed-Set X B)
      (pA)
      ( tr
        (λ Y → hom-Pointed-Set A' Y)
        (pB)
        (f')) ＝ f →
    tr
      (λ X → hom-Pointed-Set X C)
      (pB)
      ( tr
        (λ Y → hom-Pointed-Set B' Y)
        (pC)
        (g')) ＝ g →
    is-exact-hom-Pointed-Set A B C f g →
    is-exact-hom-Pointed-Set A' B' C' f' g'
  is-exact-hom-Pointed-Set-tr refl refl refl f g .f .g refl refl E = E
```

### Homotopies of set-truncated pointed maps

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {f g : A →∗ B}
  where

  htpy-hom-trunc-Pointed-Set :
    ((x : type-Pointed-Type A) →
      map-pointed-map f x ＝ map-pointed-map g x) →
    (t : type-Pointed-Set (trunc-Pointed-Set A)) →
    map-pointed-map (hom-trunc-Pointed-Set f) t ＝
    map-pointed-map (hom-trunc-Pointed-Set g) t
  htpy-hom-trunc-Pointed-Set H = htpy-trunc-Set H
```

### Exactness is invariant under homotopy of the second map

```agda
module _
  {l1 l2 l3 : Level}
  (A : Pointed-Set l1) (B : Pointed-Set l2) (C : Pointed-Set l3)
  (f : hom-Pointed-Set A B) (g h : hom-Pointed-Set B C)
  where

  is-exact-hom-Pointed-Set-htpy-right :
    ((x : type-Pointed-Set B) →
      map-pointed-map h x ＝ map-pointed-map g x) →
    is-exact-hom-Pointed-Set A B C f g →
    is-exact-hom-Pointed-Set A B C f h
  pr1 (is-exact-hom-Pointed-Set-htpy-right K E x) I =
    ( K x) ∙ (pr1 (E x) I)
  pr2 (is-exact-hom-Pointed-Set-htpy-right K E x) H =
    pr2 (E x) ((inv (K x)) ∙ H)
```

### Exactness is invariant under kernel equivalence of the second map

```agda
module _
  {l1 l2 l3 : Level}
  (A : Pointed-Set l1) (B : Pointed-Set l2) (C : Pointed-Set l3)
  (f : hom-Pointed-Set A B) (g h : hom-Pointed-Set B C)
  where

  is-exact-hom-Pointed-Set-iff-kernel-right :
    ((x : type-Pointed-Set B) →
      is-in-kernel-hom-Pointed-Set {A = B} {B = C} h x ↔
      is-in-kernel-hom-Pointed-Set {A = B} {B = C} g x) →
    is-exact-hom-Pointed-Set A B C f g →
    is-exact-hom-Pointed-Set A B C f h
  pr1 (is-exact-hom-Pointed-Set-iff-kernel-right K E x) I =
    backward-implication (K x) (pr1 (E x) I)
  pr2 (is-exact-hom-Pointed-Set-iff-kernel-right K E x) H =
    pr2 (E x) (forward-implication (K x) H)
```

### Exactness is invariant under image equivalence of the first map

```agda
module _
  {l1 l1' l2 l3 : Level}
  (A : Pointed-Set l1) (A' : Pointed-Set l1')
  (B : Pointed-Set l2) (C : Pointed-Set l3)
  (f : hom-Pointed-Set A B) (f' : hom-Pointed-Set A' B)
  (g : hom-Pointed-Set B C)
  where

  is-exact-hom-Pointed-Set-iff-image-left :
    ((x : type-Pointed-Set B) →
      is-in-image-hom-Pointed-Set {A = A} {B = B} f x ↔
      is-in-image-hom-Pointed-Set {A = A'} {B = B} f' x) →
    is-exact-hom-Pointed-Set A' B C f' g →
    is-exact-hom-Pointed-Set A B C f g
  pr1 (is-exact-hom-Pointed-Set-iff-image-left I E x) H =
    pr1 (E x) (forward-implication (I x) H)
  pr2 (is-exact-hom-Pointed-Set-iff-image-left I E x) H =
    backward-implication (I x) (pr2 (E x) H)
```

### Images are invariant under compatible middle self-maps

```agda
module _
  {l1 l2 : Level} {A : Pointed-Set l1} {B : Pointed-Set l2}
  (f : hom-Pointed-Set A B) (e d : hom-Pointed-Set B B)
  where

  iff-image-hom-Pointed-Set-middle-self-map :
    (a dA : type-Pointed-Set A → type-Pointed-Set A) →
    ((x : type-Pointed-Set A) →
      map-pointed-map e (map-pointed-map f x) ＝
      map-pointed-map f (a x)) →
    ((x : type-Pointed-Set A) →
      map-pointed-map d (map-pointed-map f x) ＝
      map-pointed-map f (dA x)) →
    ((y : type-Pointed-Set B) →
      map-pointed-map d (map-pointed-map e y) ＝ y) →
    (y : type-Pointed-Set B) →
    is-in-image-hom-Pointed-Set {A = A} {B = B} f
      ( map-pointed-map e y) ↔
    is-in-image-hom-Pointed-Set {A = A} {B = B} f y
  pr1 (iff-image-hom-Pointed-Set-middle-self-map a dA He Hd I y) H =
    apply-universal-property-trunc-Prop H
      ( subtype-image-hom-Pointed-Set {A = A} {B = B} f y)
      ( λ (x , p) →
        unit-trunc-Prop
          ( dA x ,
            ( inv (Hd x)) ∙
            ( ap (map-pointed-map d) p) ∙
            ( I y)))
  pr2 (iff-image-hom-Pointed-Set-middle-self-map a dA He Hd I y) H =
    apply-universal-property-trunc-Prop H
      ( subtype-image-hom-Pointed-Set
        {A = A}
        {B = B}
        ( f)
        ( map-pointed-map e y))
      ( λ (x , p) →
        unit-trunc-Prop
          ( a x ,
            ( inv (He x)) ∙
            ( ap (map-pointed-map e) p)))
```

### Exactness is invariant under compatible middle shifts of the second map

```agda
module _
  {l1 l2 l3 : Level}
  (A : Pointed-Set l1) (B : Pointed-Set l2) (C : Pointed-Set l3)
  (f : hom-Pointed-Set A B) (g h : hom-Pointed-Set B C)
  (e : hom-Pointed-Set B B)
  where

  is-exact-hom-Pointed-Set-image-kernel-shift-right :
    ((x : type-Pointed-Set B) →
      is-in-image-hom-Pointed-Set {A = A} {B = B} f
        ( map-pointed-map e x) ↔
      is-in-image-hom-Pointed-Set {A = A} {B = B} f x) →
    ((x : type-Pointed-Set B) →
      map-pointed-map h x ＝
      map-pointed-map g (map-pointed-map e x)) →
    is-exact-hom-Pointed-Set A B C f g →
    is-exact-hom-Pointed-Set A B C f h
  pr1
    ( is-exact-hom-Pointed-Set-image-kernel-shift-right I H E x)
    K =
    ( H x) ∙
    ( pr1
      ( E (map-pointed-map e x))
      ( backward-implication (I x) K))
  pr2
    ( is-exact-hom-Pointed-Set-image-kernel-shift-right I H E x)
    K =
    forward-implication
      ( I x)
      ( pr2
        ( E (map-pointed-map e x))
        ( ( inv (H x)) ∙ K))
```

### Exactness is invariant under injective comparison of the middle pointed set

```agda
module _
  {l1 l2 l2' l3 : Level}
  (A : Pointed-Set l1) (B : Pointed-Set l2) (B' : Pointed-Set l2')
  (C : Pointed-Set l3)
  (f : hom-Pointed-Set A B) (g : hom-Pointed-Set B C)
  (f' : hom-Pointed-Set A B') (g' : hom-Pointed-Set B' C)
  (h : hom-Pointed-Set B B')
  where

  is-exact-hom-Pointed-Set-injective-middle :
    is-injective (map-pointed-map h) →
    ((x : type-Pointed-Set A) →
      map-pointed-map h (map-pointed-map f x) ＝ map-pointed-map f' x) →
    ((y : type-Pointed-Set B) →
      map-pointed-map g y ＝ map-pointed-map g' (map-pointed-map h y)) →
    is-exact-hom-Pointed-Set A B' C f' g' →
    is-exact-hom-Pointed-Set A B C f g
  pr1
    ( is-exact-hom-Pointed-Set-injective-middle I Hf Hg E y)
    Hy =
    apply-universal-property-trunc-Prop Hy
      ( subtype-kernel-hom-Pointed-Set {A = B} {B = C} g y)
      ( λ (x , p) →
        ( Hg y) ∙
        ( pr1
          ( E (map-pointed-map h y))
          ( unit-trunc-Prop
            ( x ,
              ( inv (Hf x)) ∙
              ( ap (map-pointed-map h) p)))))
  pr2
    ( is-exact-hom-Pointed-Set-injective-middle I Hf Hg E y)
    Ky =
    apply-universal-property-trunc-Prop
      ( pr2
        ( E (map-pointed-map h y))
        ( ( inv (Hg y)) ∙ Ky))
      ( subtype-image-hom-Pointed-Set {A = A} {B = B} f y)
      ( λ (x , p) →
        unit-trunc-Prop
          ( x ,
            I ((Hf x) ∙ p)))
```

### The image of a pointed map as a mere preimage

```agda
module _
  {l1 l2 : Level} {A : Pointed-Set l1} {B : Pointed-Set l2}
  (f : hom-Pointed-Set A B)
  where

  preimage-hom-Pointed-Set : type-Pointed-Set B → UU (l1 ⊔ l2)
  preimage-hom-Pointed-Set x = fiber (map-pointed-map f) x

  mere-preimage-hom-Pointed-Set : type-Pointed-Set B → UU (l1 ⊔ l2)
  mere-preimage-hom-Pointed-Set x =
    type-trunc-Prop (preimage-hom-Pointed-Set x)

  mere-preimage-is-in-image-hom-Pointed-Set :
    (x : type-Pointed-Set B) →
    is-in-image-hom-Pointed-Set {A = A} {B = B} f x →
    mere-preimage-hom-Pointed-Set x
  mere-preimage-is-in-image-hom-Pointed-Set x H = H

  is-in-image-mere-preimage-hom-Pointed-Set :
    (x : type-Pointed-Set B) →
    mere-preimage-hom-Pointed-Set x →
    is-in-image-hom-Pointed-Set {A = A} {B = B} f x
  is-in-image-mere-preimage-hom-Pointed-Set x H = H
```

### Exactness of pointed sets in mere-preimage form

```agda
module _
  {l1 l2 l3 : Level}
  (A : Pointed-Set l1) (B : Pointed-Set l2) (C : Pointed-Set l3)
  (f : hom-Pointed-Set A B) (g : hom-Pointed-Set B C)
  where

  is-in-kernel-mere-preimage-is-exact-hom-Pointed-Set :
    is-exact-hom-Pointed-Set A B C f g →
    (x : type-Pointed-Set B) →
    mere-preimage-hom-Pointed-Set {A = A} {B = B} f x →
    is-in-kernel-hom-Pointed-Set {A = B} {B = C} g x
  is-in-kernel-mere-preimage-is-exact-hom-Pointed-Set H x K =
    forward-implication (H x)
      ( is-in-image-mere-preimage-hom-Pointed-Set {A = A} {B = B} f x K)

  mere-preimage-is-in-kernel-is-exact-hom-Pointed-Set :
    is-exact-hom-Pointed-Set A B C f g →
    (x : type-Pointed-Set B) →
    is-in-kernel-hom-Pointed-Set {A = B} {B = C} g x →
    mere-preimage-hom-Pointed-Set {A = A} {B = B} f x
  mere-preimage-is-in-kernel-is-exact-hom-Pointed-Set H x K =
    mere-preimage-is-in-image-hom-Pointed-Set {A = A} {B = B} f x
      ( backward-implication (H x) K)
```

### The set truncation of a canonical fiber sequence is exact

```agda
module _
  {l1 l2 : Level} {W : Pointed-Type l1} {Z : Pointed-Type l2}
  (f : W →∗ Z)
  where

  trunc-fiber-inclusion-hom-Pointed-Set :
    hom-Pointed-Set
      ( trunc-Pointed-Set (fiber-Pointed-Type f))
      ( trunc-Pointed-Set W)
  trunc-fiber-inclusion-hom-Pointed-Set =
    hom-trunc-Pointed-Set (inclusion-fiber-Pointed-Type f)

  trunc-map-hom-Pointed-Set :
    hom-Pointed-Set (trunc-Pointed-Set W) (trunc-Pointed-Set Z)
  trunc-map-hom-Pointed-Set =
    hom-trunc-Pointed-Set f

  eq-base-map-trunc-inclusion-fiber-Pointed-Type :
    (t : type-trunc-Set (type-Pointed-Type (fiber-Pointed-Type f))) →
    map-pointed-map trunc-map-hom-Pointed-Set
      ( map-pointed-map trunc-fiber-inclusion-hom-Pointed-Set t) ＝
    point-Pointed-Set (trunc-Pointed-Set Z)
  eq-base-map-trunc-inclusion-fiber-Pointed-Type =
    apply-dependent-universal-property-trunc-Set'
      ( λ t →
        set-Prop
          ( Id-Prop
            ( trunc-Set (type-Pointed-Type Z))
            ( map-pointed-map trunc-map-hom-Pointed-Set
              ( map-pointed-map trunc-fiber-inclusion-hom-Pointed-Set t))
            ( point-Pointed-Set (trunc-Pointed-Set Z))))
      ( λ (w , p) →
        ( ap
          ( map-pointed-map trunc-map-hom-Pointed-Set)
          ( naturality-unit-trunc-Set
            ( map-pointed-map (inclusion-fiber-Pointed-Type f))
            ( w , p))) ∙
        ( naturality-unit-trunc-Set (map-pointed-map f) w) ∙
        ( ap unit-trunc-Set p))

  is-in-kernel-is-in-image-trunc-fiber-inclusion-Pointed-Type :
    (w : type-Pointed-Set (trunc-Pointed-Set W)) →
    is-in-image-hom-Pointed-Set
      {A = trunc-Pointed-Set (fiber-Pointed-Type f)}
      {B = trunc-Pointed-Set W}
      ( trunc-fiber-inclusion-hom-Pointed-Set)
      ( w) →
    is-in-kernel-hom-Pointed-Set
      {A = trunc-Pointed-Set W}
      {B = trunc-Pointed-Set Z}
      ( trunc-map-hom-Pointed-Set)
      ( w)
  is-in-kernel-is-in-image-trunc-fiber-inclusion-Pointed-Type w H =
    apply-universal-property-trunc-Prop H
      ( subtype-kernel-hom-Pointed-Set
        {A = trunc-Pointed-Set W}
        {B = trunc-Pointed-Set Z}
        ( trunc-map-hom-Pointed-Set)
        ( w))
      ( λ where
        (t , refl) →
          eq-base-map-trunc-inclusion-fiber-Pointed-Type t)

  is-in-image-is-in-kernel-trunc-fiber-inclusion-Pointed-Type :
    (w : type-Pointed-Set (trunc-Pointed-Set W)) →
    is-in-kernel-hom-Pointed-Set
      {A = trunc-Pointed-Set W}
      {B = trunc-Pointed-Set Z}
      ( trunc-map-hom-Pointed-Set)
      ( w) →
    is-in-image-hom-Pointed-Set
      {A = trunc-Pointed-Set (fiber-Pointed-Type f)}
      {B = trunc-Pointed-Set W}
      ( trunc-fiber-inclusion-hom-Pointed-Set)
      ( w)
  is-in-image-is-in-kernel-trunc-fiber-inclusion-Pointed-Type =
    apply-dependent-universal-property-trunc-Set'
      ( λ w →
        function-Set
          ( is-in-kernel-hom-Pointed-Set
            {A = trunc-Pointed-Set W}
            {B = trunc-Pointed-Set Z}
            ( trunc-map-hom-Pointed-Set)
            ( w))
          ( set-trunc-Prop
            ( fiber
              ( map-pointed-map trunc-fiber-inclusion-hom-Pointed-Set)
              ( w))))
      ( λ w p →
        apply-universal-property-trunc-Prop
          ( apply-effectiveness-unit-trunc-Set
            ( ( inv (naturality-unit-trunc-Set (map-pointed-map f) w)) ∙
              ( p)))
          ( trunc-Prop
            ( fiber
              ( map-pointed-map trunc-fiber-inclusion-hom-Pointed-Set)
              ( unit-trunc-Set w)))
          ( λ q →
            unit-trunc-Prop
              ( unit-trunc-Set (w , q) ,
                naturality-unit-trunc-Set
                  ( map-pointed-map (inclusion-fiber-Pointed-Type f))
                  ( w , q))))

  is-exact-trunc-fiber-inclusion-Pointed-Type :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (fiber-Pointed-Type f))
      ( trunc-Pointed-Set W)
      ( trunc-Pointed-Set Z)
      ( trunc-fiber-inclusion-hom-Pointed-Set)
      ( trunc-map-hom-Pointed-Set)
  pr1 (is-exact-trunc-fiber-inclusion-Pointed-Type w) =
    is-in-kernel-is-in-image-trunc-fiber-inclusion-Pointed-Type w
  pr2 (is-exact-trunc-fiber-inclusion-Pointed-Type w) =
    is-in-image-is-in-kernel-trunc-fiber-inclusion-Pointed-Type w
```
