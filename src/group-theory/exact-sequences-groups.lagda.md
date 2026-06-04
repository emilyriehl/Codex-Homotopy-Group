# Exact sequences of groups

```agda
module group-theory.exact-sequences-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.groups
open import group-theory.homomorphisms-concrete-groups
open import group-theory.homomorphisms-groups
open import group-theory.images-of-group-homomorphisms
open import group-theory.kernels-homomorphisms-groups
open import group-theory.subgroups

open import structured-types.fiber-sequences
```

</details>

## Idea

A pair of composable group homomorphisms is exact when the image of the first
homomorphism is the kernel of the second.

For [concrete groups](group-theory.concrete-groups.md), exactness is a native
homotopical condition: the two classifying pointed maps form a
[fiber sequence](structured-types.fiber-sequences.md). The corresponding
ordinary group condition is kept as a separate algebraic comparison definition.

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

### Algebraic exactness of a pair of concrete group homomorphisms

```agda
module _
  {l1 l2 l3 : Level}
  (G : Concrete-Group l1) (H : Concrete-Group l2) (K : Concrete-Group l3)
  (f : hom-Concrete-Group G H) (g : hom-Concrete-Group H K)
  where

  is-algebraically-exact-hom-Concrete-Group : UU (l1 ⊔ l2 ⊔ l3)
  is-algebraically-exact-hom-Concrete-Group =
    is-exact-hom-Group
      ( group-Concrete-Group G)
      ( group-Concrete-Group H)
      ( group-Concrete-Group K)
      ( hom-group-hom-Concrete-Group G H f)
      ( hom-group-hom-Concrete-Group H K g)
```

### Exactness of a pair of concrete group homomorphisms

```agda
module _
  {l1 l2 l3 : Level}
  (G : Concrete-Group l1) (H : Concrete-Group l2) (K : Concrete-Group l3)
  (f : hom-Concrete-Group G H) (g : hom-Concrete-Group H K)
  where

  is-exact-hom-Concrete-Group : UU (l1 ⊔ l2 ⊔ l3)
  is-exact-hom-Concrete-Group =
    is-fiber-sequence-Pointed-Type f g
```

### From concrete exactness to algebraic exactness

The forward implication should follow from applying loops to the fiber sequence
and identifying loops in the fiber of the classifying map of `g` with the
kernel subgroup of `g`.

```agda
module _
  {l1 l2 l3 : Level}
  (G : Concrete-Group l1) (H : Concrete-Group l2) (K : Concrete-Group l3)
  (f : hom-Concrete-Group G H) (g : hom-Concrete-Group H K)
  where

  is-algebraically-exact-is-exact-hom-Concrete-Group :
    is-exact-hom-Concrete-Group G H K f g →
    is-algebraically-exact-hom-Concrete-Group G H K f g
  is-algebraically-exact-is-exact-hom-Concrete-Group H =
    {!!}
```

### From algebraic exactness to concrete exactness

The converse direction appears to require more data than ordinary exactness at
`H`: the fiber-sequence condition identifies `G` with the kernel concrete group
of `g`, while ordinary exactness only identifies the image of `f` with the
kernel of `g`.

```agda
module _
  {l1 l2 l3 : Level}
  (G : Concrete-Group l1) (H : Concrete-Group l2) (K : Concrete-Group l3)
  (f : hom-Concrete-Group G H) (g : hom-Concrete-Group H K)
  where

  is-exact-is-algebraically-exact-hom-Concrete-Group :
    is-algebraically-exact-hom-Concrete-Group G H K f g →
    is-exact-hom-Concrete-Group G H K f g
  is-exact-is-algebraically-exact-hom-Concrete-Group H =
    {!!}
```

### The logical equivalence of concrete and algebraic exactness

To prove this logical equivalence, one combines the two separately named
implications.

```agda
module _
  {l1 l2 l3 : Level}
  (G : Concrete-Group l1) (H : Concrete-Group l2) (K : Concrete-Group l3)
  (f : hom-Concrete-Group G H) (g : hom-Concrete-Group H K)
  where

  logical-equivalence-is-exact-is-algebraically-exact-hom-Concrete-Group :
    is-exact-hom-Concrete-Group G H K f g ↔
    is-algebraically-exact-hom-Concrete-Group G H K f g
  logical-equivalence-is-exact-is-algebraically-exact-hom-Concrete-Group =
    pair
      ( is-algebraically-exact-is-exact-hom-Concrete-Group G H K f g)
      ( is-exact-is-algebraically-exact-hom-Concrete-Group G H K f g)
```
