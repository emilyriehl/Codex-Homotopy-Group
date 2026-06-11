# Trivial underlying groups of trivial concrete groups

```agda
module group-theory.trivial-underlying-groups-concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.trivial-concrete-groups
open import group-theory.trivial-groups
```

</details>

## Idea

A [trivial concrete group](group-theory.trivial-concrete-groups.md) should have
a trivial underlying [ordinary group](group-theory.groups.md).

This bridge is needed because the circle vanishing results are currently stated
for concrete homotopy groups, while the exactness-to-isomorphism extraction is
stated for ordinary groups.

## Theorem

### Trivial concrete groups have trivial underlying groups

```agda
is-trivial-group-is-trivial-Concrete-Group :
  {l : Level} (G : Concrete-Group l) →
  is-trivial-Concrete-Group G →
  is-trivial-Group (group-Concrete-Group G)
is-trivial-group-is-trivial-Concrete-Group G H = H
```
