# Functoriality of joins of types

```agda
module synthetic-homotopy-theory.functoriality-joins-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.homotopies
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The **join of types** is functorial in both variables. Given maps
`f : A → C` and `g : B → D`, their action on joins is the map

```text
  A * B → C * D
```

induced by the universal property of the join. When `f` and `g` are
equivalences, this map is an equivalence because pushouts are invariant under
equivalences of spans.

## Definitions

### The functorial action of joins

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D)
  where

  cocone-map-join : cocone pr1 pr2 (C * D)
  cocone-map-join =
    comp-cocone-hom-span
      ( pr1)
      ( pr2)
      ( pr1)
      ( pr2)
      ( f)
      ( g)
      ( map-product f g)
      ( cocone-join)
      ( refl-htpy)
      ( refl-htpy)

  map-join : A * B → C * D
  map-join = cogap-join (C * D) cocone-map-join

  compute-inl-map-join :
    map-join ∘ inl-join ~ inl-join ∘ f
  compute-inl-map-join =
    compute-inl-cogap-join cocone-map-join

  compute-inr-map-join :
    map-join ∘ inr-join ~ inr-join ∘ g
  compute-inr-map-join =
    compute-inr-cogap-join cocone-map-join

  compute-glue-map-join :
    statement-coherence-htpy-cocone pr1 pr2
      ( cocone-map pr1 pr2 cocone-join map-join)
      ( cocone-map-join)
      ( compute-inl-map-join)
      ( compute-inr-map-join)
  compute-glue-map-join =
    compute-glue-cogap-join cocone-map-join
```

## Properties

### The functorial action of joins preserves equivalences

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (e : A ≃ C) (e' : B ≃ D)
  where

  universal-property-pushout-cocone-map-join :
    universal-property-pushout pr1 pr2
      ( cocone-map-join (map-equiv e) (map-equiv e'))
  universal-property-pushout-cocone-map-join =
    universal-property-pushout-extended-by-equivalences
      ( pr1)
      ( pr2)
      ( pr1)
      ( pr2)
      ( map-equiv e)
      ( map-equiv e')
      ( map-product (map-equiv e) (map-equiv e'))
      ( cocone-join)
      ( up-join)
      ( refl-htpy)
      ( refl-htpy)
      ( is-equiv-map-equiv e)
      ( is-equiv-map-equiv e')
      ( is-equiv-map-product
        ( map-equiv e)
        ( map-equiv e')
        ( is-equiv-map-equiv e)
        ( is-equiv-map-equiv e'))

  is-equiv-map-join :
    is-equiv (map-join (map-equiv e) (map-equiv e'))
  is-equiv-map-join =
    is-equiv-up-pushout-up-pushout
      ( pr1)
      ( pr2)
      ( cocone-join)
      ( cocone-map-join (map-equiv e) (map-equiv e'))
      ( map-join (map-equiv e) (map-equiv e'))
      ( ( compute-inl-map-join (map-equiv e) (map-equiv e')) ,
        ( ( compute-inr-map-join (map-equiv e) (map-equiv e')) ,
          ( compute-glue-map-join (map-equiv e) (map-equiv e'))))
      ( up-join)
      ( universal-property-pushout-cocone-map-join)

  equiv-join : A * B ≃ C * D
  pr1 equiv-join = map-join (map-equiv e) (map-equiv e')
  pr2 equiv-join = is-equiv-map-join
```
