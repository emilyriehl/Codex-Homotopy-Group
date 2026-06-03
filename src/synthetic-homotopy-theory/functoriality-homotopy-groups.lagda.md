# Functoriality of homotopy groups

```agda
module synthetic-homotopy-theory.functoriality-homotopy-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import group-theory.homomorphisms-concrete-groups
open import group-theory.functoriality-homotopy-automorphism-groups

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.homotopy-groups
```

</details>

## Idea

Every [pointed map](structured-types.pointed-maps.md) `f : A →∗ B` induces a
homomorphism on each concrete
[homotopy group](synthetic-homotopy-theory.homotopy-groups.md) by applying
`f` to the corresponding iterated loop spaces and then using functoriality of
homotopy automorphism groups.

## Definitions

### The homomorphism induced on concrete homotopy groups

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  hom-concrete-homotopy-group :
    (n : ℕ) → A →∗ B →
    hom-Concrete-Group
      ( concrete-homotopy-group n A)
      ( concrete-homotopy-group n B)
  hom-concrete-homotopy-group n f =
    hom-concrete-group-Pointed-Type (pointed-map-iterated-loop-space n f)
```
