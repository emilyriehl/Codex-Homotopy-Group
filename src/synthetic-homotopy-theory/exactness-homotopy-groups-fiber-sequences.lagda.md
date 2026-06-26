# Group exactness of homotopy groups of fiber sequences

```agda
module synthetic-homotopy-theory.exactness-homotopy-groups-fiber-sequences where

open import synthetic-homotopy-theory.canonical-exactness-homotopy-groups-fiber-sequences public
open import synthetic-homotopy-theory.direct-exactness-homotopy-groups-fiber-sequences public
open import synthetic-homotopy-theory.recursive-exactness-homotopy-groups-fiber-sequences public
```

## Idea

This module is the compatibility re-export surface for group-level exactness of
homotopy groups of a fiber sequence.

The canonical all-index exactness statements used by the public long exact
sequence package live in
[`canonical-exactness-homotopy-groups-fiber-sequences`](synthetic-homotopy-theory.canonical-exactness-homotopy-groups-fiber-sequences.md).
The direct shifted connecting-map route lives in
[`direct-exactness-homotopy-groups-fiber-sequences`](synthetic-homotopy-theory.direct-exactness-homotopy-groups-fiber-sequences.md).
The older recursive, pointed-homotopy, low-dimensional, and trivial-codomain
compatibility statements live in
[`recursive-exactness-homotopy-groups-fiber-sequences`](synthetic-homotopy-theory.recursive-exactness-homotopy-groups-fiber-sequences.md).

Keeping this file as a thin public facade preserves downstream imports while
making the proof routes explicit for future library extraction.
