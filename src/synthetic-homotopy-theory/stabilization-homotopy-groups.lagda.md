# Stabilization maps on homotopy groups

```agda
module synthetic-homotopy-theory.stabilization-homotopy-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.groups
open import group-theory.homomorphisms-concrete-groups
open import group-theory.homomorphisms-groups

open import structured-types.pointed-types

open import synthetic-homotopy-theory.freudenthal-suspension-theorem
open import synthetic-homotopy-theory.functoriality-homotopy-groups
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.suspensions-of-pointed-types
```

</details>

## Idea

The unit of the suspension-loop adjunction induces, functorially, stabilization
homomorphisms on the concrete homotopy groups

```text
  πₖ A → πₖ ΩΣA.
```

These are the group-level maps whose low-dimensional isomorphism consequences
are supplied by the Freudenthal suspension theorem.

## Definitions

### The concrete homotopy-group stabilization homomorphism

```agda
hom-stabilization-concrete-homotopy-group :
  {l : Level} (n : ℕ) (A : Pointed-Type l) →
  hom-Concrete-Group
    ( concrete-homotopy-group n A)
    ( concrete-homotopy-group n (Ω (suspension-Pointed-Type A)))
hom-stabilization-concrete-homotopy-group n A =
  hom-concrete-homotopy-group n (pointed-map-Freudenthal-suspension A)

hom-group-stabilization-concrete-homotopy-group :
  {l : Level} (n : ℕ) (A : Pointed-Type l) →
  hom-Group
    ( group-Concrete-Group (concrete-homotopy-group n A))
    ( group-Concrete-Group
      ( concrete-homotopy-group n (Ω (suspension-Pointed-Type A))))
hom-group-stabilization-concrete-homotopy-group n A =
  hom-group-hom-Concrete-Group
    ( concrete-homotopy-group n A)
    ( concrete-homotopy-group n (Ω (suspension-Pointed-Type A)))
    ( hom-stabilization-concrete-homotopy-group n A)
```
