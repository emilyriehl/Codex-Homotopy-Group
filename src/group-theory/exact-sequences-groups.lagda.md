# Exact sequences of groups

```agda
module group-theory.exact-sequences-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.groups
open import group-theory.homomorphisms-concrete-groups
open import group-theory.homomorphisms-groups
open import group-theory.images-of-group-homomorphisms
open import group-theory.kernels-homomorphisms-groups
open import group-theory.subgroups
```

</details>

## Idea

A pair of composable group homomorphisms is exact when the image of the first
homomorphism is the kernel of the second.

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

### Exactness of a pair of concrete group homomorphisms

```agda
module _
  {l1 l2 l3 : Level}
  (G : Concrete-Group l1) (H : Concrete-Group l2) (K : Concrete-Group l3)
  (f : hom-Concrete-Group G H) (g : hom-Concrete-Group H K)
  where

  is-exact-hom-Concrete-Group : UU (l1 ⊔ l2 ⊔ l3)
  is-exact-hom-Concrete-Group =
    is-exact-hom-Group
      ( group-Concrete-Group G)
      ( group-Concrete-Group H)
      ( group-Concrete-Group K)
      ( hom-group-hom-Concrete-Group G H f)
      ( hom-group-hom-Concrete-Group H K g)
```
