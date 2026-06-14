# Computing identity types of subtypes

```agda
module foundation.computing-identity-types-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import foundation-core.subtypes
```

</details>

## Idea

The inverse direction of subtype extensionality constructs an equality in a
subtype from an equality of first components. Applying the subtype inclusion to
that constructed equality recovers the original equality.

## Theorem

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A)
  where

  compute-map-extensionality-eq-type-subtype :
    {x y : type-subtype P} (p : pr1 x ＝ pr1 y) →
    map-extensionality-type-subtype
      ( P)
      ( pr2 x)
      ( refl)
      ( λ x → id-equiv)
      ( y)
      ( eq-type-subtype P p) ＝
    p
  compute-map-extensionality-eq-type-subtype {x} {y} p =
    is-section-map-inv-equiv (extensionality-type-subtype' P x y) p
```
