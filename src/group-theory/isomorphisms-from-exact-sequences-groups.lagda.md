# Isomorphisms from exact sequences of groups

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module group-theory.isomorphisms-from-exact-sequences-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.exact-sequences-groups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.isomorphisms-groups
open import group-theory.trivial-groups
```

</details>

## Idea

An exact segment

```text
A → B → C → D
```

whose outer groups `A` and `D` are trivial identifies the middle homomorphism
`B → C` as a group isomorphism.

This file records the algebraic extraction needed to turn the Hopf long exact
sequence into the comparison `π₃(S³) ≅ π₃(S²)`.

## Theorem

### Exactness with trivial outer groups gives an isomorphism

```agda
is-iso-is-exact-is-trivial-outer-groups :
  {l1 l2 l3 l4 : Level}
  (A : Group l1) (B : Group l2) (C : Group l3) (D : Group l4)
  (f : hom-Group A B) (g : hom-Group B C) (h : hom-Group C D) →
  is-trivial-Group A →
  is-trivial-Group D →
  is-exact-hom-Group A B C f g →
  is-exact-hom-Group B C D g h →
  is-iso-Group B C g
is-iso-is-exact-is-trivial-outer-groups = {!!}
```
