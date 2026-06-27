# Exact sequences of abelian groups

```agda
module group-theory.exact-sequences-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.exact-sequences-groups
open import group-theory.homomorphisms-abelian-groups
```

</details>

## Idea

Exactness of a pair of homomorphisms of abelian groups is exactness of the
underlying pair of group homomorphisms. This file provides the abelian-group
surface API without duplicating the group-level image/kernel definition.

## Definitions

```agda
module _
  {l1 l2 l3 : Level} (A : Ab l1) (B : Ab l2) (C : Ab l3)
  (f : hom-Ab A B) (g : hom-Ab B C)
  where

  is-exact-hom-Ab : UU (l1 ⊔ l2 ⊔ l3)
  is-exact-hom-Ab =
    is-exact-hom-Group
      ( group-Ab A)
      ( group-Ab B)
      ( group-Ab C)
      ( f)
      ( g)
```
