# The classifying fiber-sequence route for homotopy groups

```agda
module synthetic-homotopy-theory.classifying-fiber-sequences-homotopy-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import structured-types.fiber-sequences

open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.long-exact-sequences-homotopy-groups
```

</details>

## Idea

The concrete homotopy group `π(n+1) X` is represented as the concrete group of
the pointed type `Ωⁿ X`. It is tempting to try to prove adjacent exactness in
the homotopy long exact sequence by showing that the corresponding classifying
pointed maps of concrete groups form fiber sequences.

This route is too strong in general. A fiber sequence of classifying spaces of
groups imposes short-exact-style information: the third group is controlled as
the quotient of the middle group by the image of the first. In the homotopy long
exact sequence, an adjacent triple only gives exactness at the middle term; the
next boundary homomorphism measures the cokernel.

Consequently, the correct next target is not a classifying-map fiber sequence.
The group-level LES proof should instead compare the already-proved
set-truncated exactness statements with the ordinary groups underlying concrete
homotopy groups.

This module deliberately contains no theorem statements.
