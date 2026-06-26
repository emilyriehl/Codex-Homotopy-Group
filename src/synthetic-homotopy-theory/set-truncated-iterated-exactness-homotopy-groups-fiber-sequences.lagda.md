# Set-truncated iterated exactness of homotopy groups of fiber sequences

```agda
module synthetic-homotopy-theory.set-truncated-iterated-exactness-homotopy-groups-fiber-sequences where

open import synthetic-homotopy-theory.set-truncated-canonical-iterated-exactness-homotopy-groups-fiber-sequences public
open import synthetic-homotopy-theory.set-truncated-direct-iterated-exactness-homotopy-groups-fiber-sequences public
open import synthetic-homotopy-theory.set-truncated-iterated-maps-homotopy-groups-fiber-sequences public
open import synthetic-homotopy-theory.set-truncated-recursive-iterated-exactness-homotopy-groups-fiber-sequences public
open import synthetic-homotopy-theory.signed-boundary-comparisons-fiber-sequences public
```

## Idea

This module is the compatibility re-export surface for set-truncated iterated
exactness of homotopy groups of a fiber sequence.

The set-truncated iterated maps live in
[`set-truncated-iterated-maps-homotopy-groups-fiber-sequences`](synthetic-homotopy-theory.set-truncated-iterated-maps-homotopy-groups-fiber-sequences.md).
The canonical all-index exactness statements live in
[`set-truncated-canonical-iterated-exactness-homotopy-groups-fiber-sequences`](synthetic-homotopy-theory.set-truncated-canonical-iterated-exactness-homotopy-groups-fiber-sequences.md).
The direct connecting-map route and reassociation transports live in
[`set-truncated-direct-iterated-exactness-homotopy-groups-fiber-sequences`](synthetic-homotopy-theory.set-truncated-direct-iterated-exactness-homotopy-groups-fiber-sequences.md).
The recursive-boundary compatibility transports live in
[`set-truncated-recursive-iterated-exactness-homotopy-groups-fiber-sequences`](synthetic-homotopy-theory.set-truncated-recursive-iterated-exactness-homotopy-groups-fiber-sequences.md).
The signed boundary comparison machinery lives in
[`signed-boundary-comparisons-fiber-sequences`](synthetic-homotopy-theory.signed-boundary-comparisons-fiber-sequences.md).

Keeping this file as a thin public facade preserves existing downstream imports
while making the proof-route ownership explicit for future library extraction.
