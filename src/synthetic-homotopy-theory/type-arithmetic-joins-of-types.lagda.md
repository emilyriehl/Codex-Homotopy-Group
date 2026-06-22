# Type arithmetic for joins of types

```agda
module synthetic-homotopy-theory.type-arithmetic-joins-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

This file records arithmetic laws for the **join of types**. The first such law
is commutativity:

```text
  A * B ≃ B * A.
```

The proof is a pushout argument. The standard cocone on `B * A` is first
swapped, and then extended along the commutativity equivalence
`A × B ≃ B × A`.

## Laws

### Commutativity of joins

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  cocone-commutative-join : cocone pr1 pr2 (B * A)
  cocone-commutative-join =
    comp-cocone-hom-span
      ( pr2)
      ( pr1)
      ( pr1)
      ( pr2)
      ( id)
      ( id)
      ( map-commutative-product)
      ( swap-cocone pr1 pr2 (B * A) cocone-join)
      ( refl-htpy)
      ( refl-htpy)

  map-commutative-join : A * B → B * A
  map-commutative-join =
    cogap-join (B * A) cocone-commutative-join

  compute-inl-map-commutative-join :
    map-commutative-join ∘ inl-join ~ inr-join
  compute-inl-map-commutative-join =
    compute-inl-cogap-join cocone-commutative-join

  compute-inr-map-commutative-join :
    map-commutative-join ∘ inr-join ~ inl-join
  compute-inr-map-commutative-join =
    compute-inr-cogap-join cocone-commutative-join

  compute-glue-map-commutative-join :
    statement-coherence-htpy-cocone pr1 pr2
      ( cocone-map pr1 pr2 cocone-join map-commutative-join)
      ( cocone-commutative-join)
      ( compute-inl-map-commutative-join)
      ( compute-inr-map-commutative-join)
  compute-glue-map-commutative-join =
    compute-glue-cogap-join cocone-commutative-join

  universal-property-pushout-cocone-commutative-join :
    universal-property-pushout pr1 pr2 cocone-commutative-join
  universal-property-pushout-cocone-commutative-join =
    universal-property-pushout-extended-by-equivalences
      ( pr2)
      ( pr1)
      ( pr1)
      ( pr2)
      ( id)
      ( id)
      ( map-commutative-product)
      ( swap-cocone pr1 pr2 (B * A) cocone-join)
      ( universal-property-pushout-swap-cocone-universal-property-pushout
        ( pr1)
        ( pr2)
        ( B * A)
        ( cocone-join)
        ( up-join))
      ( refl-htpy)
      ( refl-htpy)
      ( is-equiv-id)
      ( is-equiv-id)
      ( is-equiv-map-commutative-product)

  is-equiv-map-commutative-join : is-equiv map-commutative-join
  is-equiv-map-commutative-join =
    is-equiv-up-pushout-up-pushout
      ( pr1)
      ( pr2)
      ( cocone-join)
      ( cocone-commutative-join)
      ( map-commutative-join)
      ( ( compute-inl-map-commutative-join) ,
        ( ( compute-inr-map-commutative-join) ,
          ( compute-glue-map-commutative-join)))
      ( up-join)
      ( universal-property-pushout-cocone-commutative-join)

  commutative-join : A * B ≃ B * A
  pr1 commutative-join = map-commutative-join
  pr2 commutative-join = is-equiv-map-commutative-join
```
