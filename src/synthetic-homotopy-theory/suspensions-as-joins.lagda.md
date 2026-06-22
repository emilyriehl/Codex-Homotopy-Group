# Suspensions as joins with the two-point type

```agda
module synthetic-homotopy-theory.suspensions-as-joins where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.suspensions-of-types
open import synthetic-homotopy-theory.universal-property-pushouts
open import synthetic-homotopy-theory.universal-property-suspensions

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The suspension of a type `X` can be modeled as the join of the standard
two-element type with `X`. The forward map

```text
Fin 2 * X → suspension X
```

sends the two points of `Fin 2` to the north and south poles and sends the
right copy of `X` to the south pole, using the meridians for the join paths.
The reverse map

```text
suspension X → Fin 2 * X
```

sends the poles to the two points of `Fin 2` and sends each meridian through
the corresponding point of the right copy of `X`.

These maps are the first reusable layer toward identifying spheres with join
powers of `Fin 2`.

## Definitions

### The map from `Fin 2 * X` to the suspension of `X`

```agda
module _
  {l : Level} (X : UU l)
  where

  left-map-span-join-Fin-2 : Fin 2 × X → Fin 2
  left-map-span-join-Fin-2 = pr1

  right-map-span-join-Fin-2 : Fin 2 × X → X
  right-map-span-join-Fin-2 = pr2

  zero-Fin-2 : Fin 2
  zero-Fin-2 = inl (inr star)

  one-Fin-2 : Fin 2
  one-Fin-2 = inr star

  cocone-map-suspension-join-Fin-2 :
    cocone
      ( left-map-span-join-Fin-2)
      ( right-map-span-join-Fin-2)
      ( suspension X)
  pr1 cocone-map-suspension-join-Fin-2 (inl (inr star)) =
    north-suspension
  pr1 cocone-map-suspension-join-Fin-2 (inr star) =
    south-suspension
  pr1 (pr2 cocone-map-suspension-join-Fin-2) x =
    south-suspension
  pr2 (pr2 cocone-map-suspension-join-Fin-2) ((inl (inr star)) , x) =
    meridian-suspension x
  pr2 (pr2 cocone-map-suspension-join-Fin-2) ((inr star) , x) =
    refl

  map-suspension-join-Fin-2 : Fin 2 * X → suspension X
  map-suspension-join-Fin-2 =
    cogap-join
      ( suspension X)
      ( cocone-map-suspension-join-Fin-2)
```

### The map from the suspension of `X` to `Fin 2 * X`

```agda
  suspension-structure-map-join-Fin-2-suspension :
    suspension-structure X (Fin 2 * X)
  pr1 suspension-structure-map-join-Fin-2-suspension =
    inl-join (zero-Fin-2)
  pr1 (pr2 suspension-structure-map-join-Fin-2-suspension) =
    inl-join (one-Fin-2)
  pr2 (pr2 suspension-structure-map-join-Fin-2-suspension) x =
    ( glue-join (zero-Fin-2 , x)) ∙
    ( inv (glue-join (one-Fin-2 , x)))

  map-join-Fin-2-suspension : suspension X → Fin 2 * X
  map-join-Fin-2-suspension =
    cogap-suspension suspension-structure-map-join-Fin-2-suspension
```

### Cocones over the `Fin 2` join span and suspension structures

```agda
  suspension-structure-cocone-join-Fin-2 :
    {l2 : Level} {Y : UU l2} →
    cocone
      ( left-map-span-join-Fin-2)
      ( right-map-span-join-Fin-2)
      ( Y) →
    suspension-structure X Y
  pr1 (suspension-structure-cocone-join-Fin-2 c) =
    horizontal-map-cocone
      ( left-map-span-join-Fin-2)
      ( right-map-span-join-Fin-2)
      ( c)
      ( zero-Fin-2)
  pr1 (pr2 (suspension-structure-cocone-join-Fin-2 c)) =
    horizontal-map-cocone
      ( left-map-span-join-Fin-2)
      ( right-map-span-join-Fin-2)
      ( c)
      ( one-Fin-2)
  pr2 (pr2 (suspension-structure-cocone-join-Fin-2 c)) x =
    ( coherence-square-cocone
      ( left-map-span-join-Fin-2)
      ( right-map-span-join-Fin-2)
      ( c)
      ( zero-Fin-2 , x)) ∙
    ( inv
      ( coherence-square-cocone
        ( left-map-span-join-Fin-2)
        ( right-map-span-join-Fin-2)
        ( c)
        ( one-Fin-2 , x)))

  cocone-join-Fin-2-suspension-structure :
    {l2 : Level} {Y : UU l2} →
    suspension-structure X Y →
    cocone
      ( left-map-span-join-Fin-2)
      ( right-map-span-join-Fin-2)
      ( Y)
  pr1 (cocone-join-Fin-2-suspension-structure s) (inl (inr star)) =
    north-suspension-structure s
  pr1 (cocone-join-Fin-2-suspension-structure s) (inr star) =
    south-suspension-structure s
  pr1 (pr2 (cocone-join-Fin-2-suspension-structure s)) x =
    south-suspension-structure s
  pr2 (pr2 (cocone-join-Fin-2-suspension-structure s))
    ((inl (inr star)) , x) =
    meridian-suspension-structure s x
  pr2 (pr2 (cocone-join-Fin-2-suspension-structure s))
    ((inr star) , x) =
    refl

  compute-zero-cocone-join-Fin-2-suspension-structure :
    {l2 : Level} {Y : UU l2} →
    (s : suspension-structure X Y) (x : X) →
    coherence-square-cocone
      ( left-map-span-join-Fin-2)
      ( right-map-span-join-Fin-2)
      ( cocone-join-Fin-2-suspension-structure s)
      ( zero-Fin-2 , x) ＝
    meridian-suspension-structure s x
  compute-zero-cocone-join-Fin-2-suspension-structure s x = refl

  compute-one-cocone-join-Fin-2-suspension-structure :
    {l2 : Level} {Y : UU l2} →
    (s : suspension-structure X Y) (x : X) →
    coherence-square-cocone
      ( left-map-span-join-Fin-2)
      ( right-map-span-join-Fin-2)
      ( cocone-join-Fin-2-suspension-structure s)
      ( one-Fin-2 , x) ＝
    refl
  compute-one-cocone-join-Fin-2-suspension-structure s x = refl
```

## Properties

### The comparison retracts suspension structures

```agda
  is-retraction-suspension-structure-cocone-join-Fin-2 :
    {l2 : Level} {Y : UU l2} →
    (s : suspension-structure X Y) →
    suspension-structure-cocone-join-Fin-2
      ( cocone-join-Fin-2-suspension-structure s) ＝
    s
  is-retraction-suspension-structure-cocone-join-Fin-2 (N , S , merid) =
    eq-htpy-suspension-structure
      ( refl , refl ,
        λ x →
        ( right-unit ∙
          ( ap
            ( λ p → merid x ∙ inv p)
            ( compute-one-cocone-join-Fin-2-suspension-structure
              ( N , S , merid)
              ( x)))) ∙
        right-unit)

  is-section-suspension-structure-cocone-join-Fin-2 :
    {l2 : Level} {Y : UU l2} →
    (c : cocone left-map-span-join-Fin-2 right-map-span-join-Fin-2 Y) →
    cocone-join-Fin-2-suspension-structure
      ( suspension-structure-cocone-join-Fin-2 c) ＝
    c
  is-section-suspension-structure-cocone-join-Fin-2 c =
    eq-htpy-cocone
      ( left-map-span-join-Fin-2)
      ( right-map-span-join-Fin-2)
      ( cocone-join-Fin-2-suspension-structure
        ( suspension-structure-cocone-join-Fin-2 c))
      ( c)
      ( horizontal-htpy , vertical-htpy , coherence-htpy)
    where
    horizontal-htpy :
      horizontal-map-cocone
        ( left-map-span-join-Fin-2)
        ( right-map-span-join-Fin-2)
        ( cocone-join-Fin-2-suspension-structure
          ( suspension-structure-cocone-join-Fin-2 c)) ~
      horizontal-map-cocone
        ( left-map-span-join-Fin-2)
        ( right-map-span-join-Fin-2)
        ( c)
    horizontal-htpy (inl (inr star)) = refl
    horizontal-htpy (inr star) = refl

    vertical-htpy :
      vertical-map-cocone
        ( left-map-span-join-Fin-2)
        ( right-map-span-join-Fin-2)
        ( cocone-join-Fin-2-suspension-structure
          ( suspension-structure-cocone-join-Fin-2 c)) ~
      vertical-map-cocone
        ( left-map-span-join-Fin-2)
        ( right-map-span-join-Fin-2)
        ( c)
    vertical-htpy x =
      coherence-square-cocone
        ( left-map-span-join-Fin-2)
        ( right-map-span-join-Fin-2)
        ( c)
        ( one-Fin-2 , x)

    coherence-htpy :
      statement-coherence-htpy-cocone
        ( left-map-span-join-Fin-2)
        ( right-map-span-join-Fin-2)
        ( cocone-join-Fin-2-suspension-structure
          ( suspension-structure-cocone-join-Fin-2 c))
        ( c)
        ( horizontal-htpy)
        ( vertical-htpy)
    coherence-htpy ((inl (inr star)) , x) =
      ( assoc
        ( coherence-square-cocone
          ( left-map-span-join-Fin-2)
          ( right-map-span-join-Fin-2)
          ( c)
          ( zero-Fin-2 , x))
        ( inv
          ( coherence-square-cocone
            ( left-map-span-join-Fin-2)
            ( right-map-span-join-Fin-2)
            ( c)
            ( one-Fin-2 , x)))
        ( coherence-square-cocone
          ( left-map-span-join-Fin-2)
          ( right-map-span-join-Fin-2)
          ( c)
          ( one-Fin-2 , x))) ∙
      ( ( ap
          ( λ p →
            coherence-square-cocone
              ( left-map-span-join-Fin-2)
              ( right-map-span-join-Fin-2)
              ( c)
              ( zero-Fin-2 , x) ∙ p)
          ( left-inv
            ( coherence-square-cocone
              ( left-map-span-join-Fin-2)
              ( right-map-span-join-Fin-2)
              ( c)
              ( one-Fin-2 , x)))) ∙
        ( right-unit))
    coherence-htpy ((inr star) , x) = refl

  is-equiv-suspension-structure-cocone-join-Fin-2 :
    {l2 : Level} {Y : UU l2} →
    is-equiv (suspension-structure-cocone-join-Fin-2 {Y = Y})
  is-equiv-suspension-structure-cocone-join-Fin-2 =
    is-equiv-is-invertible
      ( cocone-join-Fin-2-suspension-structure)
      ( is-retraction-suspension-structure-cocone-join-Fin-2)
      ( is-section-suspension-structure-cocone-join-Fin-2)

  equiv-suspension-structure-cocone-join-Fin-2 :
    {l2 : Level} {Y : UU l2} →
    cocone left-map-span-join-Fin-2 right-map-span-join-Fin-2 Y ≃
    suspension-structure X Y
  pr1 equiv-suspension-structure-cocone-join-Fin-2 =
    suspension-structure-cocone-join-Fin-2
  pr2 equiv-suspension-structure-cocone-join-Fin-2 =
    is-equiv-suspension-structure-cocone-join-Fin-2

  triangle-ev-suspension-cocone-map-suspension-join-Fin-2 :
    {l2 : Level} (Y : UU l2) →
    ev-suspension (suspension-structure-suspension X) Y ~
    ( suspension-structure-cocone-join-Fin-2 ∘
      cocone-map
        ( left-map-span-join-Fin-2)
        ( right-map-span-join-Fin-2)
        ( cocone-map-suspension-join-Fin-2))
  triangle-ev-suspension-cocone-map-suspension-join-Fin-2 Y h =
    eq-htpy-suspension-structure (refl , refl , λ x → refl)

  universal-property-pushout-cocone-map-suspension-join-Fin-2 :
    universal-property-pushout
      ( left-map-span-join-Fin-2)
      ( right-map-span-join-Fin-2)
      ( cocone-map-suspension-join-Fin-2)
  universal-property-pushout-cocone-map-suspension-join-Fin-2 Y =
    is-equiv-top-map-triangle
      ( ev-suspension (suspension-structure-suspension X) Y)
      ( suspension-structure-cocone-join-Fin-2)
      ( cocone-map
        ( left-map-span-join-Fin-2)
        ( right-map-span-join-Fin-2)
        ( cocone-map-suspension-join-Fin-2))
      ( triangle-ev-suspension-cocone-map-suspension-join-Fin-2 Y)
      ( is-equiv-suspension-structure-cocone-join-Fin-2)
      ( up-suspension Y)
```

### Computation rules for the map from the join to the suspension

```agda
  compute-inl-zero-map-suspension-join-Fin-2 :
    map-suspension-join-Fin-2 (inl-join (zero-Fin-2)) ＝
    north-suspension
  compute-inl-zero-map-suspension-join-Fin-2 =
    compute-inl-cogap-join
      ( cocone-map-suspension-join-Fin-2)
      ( zero-Fin-2)

  compute-inl-one-map-suspension-join-Fin-2 :
    map-suspension-join-Fin-2 (inl-join (one-Fin-2)) ＝
    south-suspension
  compute-inl-one-map-suspension-join-Fin-2 =
    compute-inl-cogap-join
      ( cocone-map-suspension-join-Fin-2)
      ( one-Fin-2)

  compute-inr-map-suspension-join-Fin-2 :
    (x : X) →
    map-suspension-join-Fin-2 (inr-join x) ＝ south-suspension
  compute-inr-map-suspension-join-Fin-2 =
    compute-inr-cogap-join cocone-map-suspension-join-Fin-2

  compute-glue-map-suspension-join-Fin-2 :
    statement-coherence-htpy-cocone
      ( left-map-span-join-Fin-2)
      ( right-map-span-join-Fin-2)
      ( cocone-map
        ( left-map-span-join-Fin-2)
        ( right-map-span-join-Fin-2)
        ( cocone-join)
        ( map-suspension-join-Fin-2))
      ( cocone-map-suspension-join-Fin-2)
      ( compute-inl-cogap-join cocone-map-suspension-join-Fin-2)
      ( compute-inr-cogap-join cocone-map-suspension-join-Fin-2)
  compute-glue-map-suspension-join-Fin-2 =
    compute-glue-cogap-join cocone-map-suspension-join-Fin-2

  compute-glue-zero-map-suspension-join-Fin-2 :
    (x : X) →
    ( ( ap map-suspension-join-Fin-2
        ( glue-join (zero-Fin-2 , x))) ∙
      ( compute-inr-map-suspension-join-Fin-2 x)) ＝
    ( compute-inl-zero-map-suspension-join-Fin-2 ∙
      meridian-suspension x)
  compute-glue-zero-map-suspension-join-Fin-2 x =
    compute-glue-map-suspension-join-Fin-2 (zero-Fin-2 , x)

  compute-glue-one-map-suspension-join-Fin-2 :
    (x : X) →
    ( ( ap map-suspension-join-Fin-2
        ( glue-join (one-Fin-2 , x))) ∙
      ( compute-inr-map-suspension-join-Fin-2 x)) ＝
    ( compute-inl-one-map-suspension-join-Fin-2 ∙ refl)
  compute-glue-one-map-suspension-join-Fin-2 x =
    compute-glue-map-suspension-join-Fin-2 (one-Fin-2 , x)

  htpy-cocone-map-suspension-join-Fin-2 :
    htpy-cocone
      ( left-map-span-join-Fin-2)
      ( right-map-span-join-Fin-2)
      ( cocone-map
        ( left-map-span-join-Fin-2)
        ( right-map-span-join-Fin-2)
        ( cocone-join)
        ( map-suspension-join-Fin-2))
      ( cocone-map-suspension-join-Fin-2)
  htpy-cocone-map-suspension-join-Fin-2 =
    ( compute-inl-cogap-join cocone-map-suspension-join-Fin-2 ,
      compute-inr-cogap-join cocone-map-suspension-join-Fin-2 ,
      compute-glue-map-suspension-join-Fin-2)

  is-equiv-map-suspension-join-Fin-2 :
    is-equiv map-suspension-join-Fin-2
  is-equiv-map-suspension-join-Fin-2 =
    is-equiv-up-pushout-up-pushout
      ( left-map-span-join-Fin-2)
      ( right-map-span-join-Fin-2)
      ( cocone-join)
      ( cocone-map-suspension-join-Fin-2)
      ( map-suspension-join-Fin-2)
      ( htpy-cocone-map-suspension-join-Fin-2)
      ( up-join)
      ( universal-property-pushout-cocone-map-suspension-join-Fin-2)

  equiv-suspension-join-Fin-2 : Fin 2 * X ≃ suspension X
  pr1 equiv-suspension-join-Fin-2 = map-suspension-join-Fin-2
  pr2 equiv-suspension-join-Fin-2 = is-equiv-map-suspension-join-Fin-2
```

### Computation rules for the map from the suspension to the join

```agda
  compute-north-map-join-Fin-2-suspension :
    map-join-Fin-2-suspension north-suspension ＝ inl-join (zero-Fin-2)
  compute-north-map-join-Fin-2-suspension =
    compute-north-cogap-suspension
      ( suspension-structure-map-join-Fin-2-suspension)

  compute-south-map-join-Fin-2-suspension :
    map-join-Fin-2-suspension south-suspension ＝ inl-join (one-Fin-2)
  compute-south-map-join-Fin-2-suspension =
    compute-south-cogap-suspension
      ( suspension-structure-map-join-Fin-2-suspension)

  compute-meridian-map-join-Fin-2-suspension :
    (x : X) →
    ( ( ap map-join-Fin-2-suspension (meridian-suspension x)) ∙
      compute-south-map-join-Fin-2-suspension) ＝
    ( compute-north-map-join-Fin-2-suspension ∙
      ( glue-join (zero-Fin-2 , x) ∙
        inv (glue-join (one-Fin-2 , x))))
  compute-meridian-map-join-Fin-2-suspension =
    compute-meridian-cogap-suspension
      ( suspension-structure-map-join-Fin-2-suspension)
```
