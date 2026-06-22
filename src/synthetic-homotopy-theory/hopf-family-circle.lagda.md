# The Hopf family over the 2-sphere

```agda
module synthetic-homotopy-theory.hopf-family-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.span-diagrams
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import structured-types.fiber-sequences
open import structured-types.fibers-of-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.descent-data-pushouts
open import synthetic-homotopy-theory.flattening-lemma-pushouts
open import synthetic-homotopy-theory.h-space-structure-circle
open import synthetic-homotopy-theory.hopf-construction-circle
open import synthetic-homotopy-theory.join-powers-of-types
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.spheres
open import synthetic-homotopy-theory.spheres-as-join-powers
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.suspensions-of-types
open import synthetic-homotopy-theory.universal-property-pushouts

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The Hopf fibration can be presented as a type family over the suspension of the
circle. Both pole fibers are the circle, and the meridian indexed by `x : S¹`
is classified by the equivalence given by left multiplication by `x`.

This file records that structural family over `S²`. Its total space is the
object that the flattening argument should identify with the total space of the
Hopf construction.

## Definitions

### The family over the 2-sphere

```agda
suspension-structure-hopf-family-sphere-1 :
  suspension-structure (sphere 1) (UU lzero)
pr1 suspension-structure-hopf-family-sphere-1 =
  sphere 1
pr1 (pr2 suspension-structure-hopf-family-sphere-1) =
  sphere 1
pr2 (pr2 suspension-structure-hopf-family-sphere-1) x =
  eq-equiv (equiv-left-mul-sphere-1 x)

hopf-family-sphere-1 : sphere 2 → UU lzero
hopf-family-sphere-1 =
  cogap-suspension suspension-structure-hopf-family-sphere-1
```

### Pole and meridian computations

```agda
compute-north-hopf-family-sphere-1 :
  hopf-family-sphere-1 (north-sphere 2) ＝ sphere 1
compute-north-hopf-family-sphere-1 =
  compute-north-cogap-suspension suspension-structure-hopf-family-sphere-1

compute-south-hopf-family-sphere-1 :
  hopf-family-sphere-1 (south-sphere 2) ＝ sphere 1
compute-south-hopf-family-sphere-1 =
  compute-south-cogap-suspension suspension-structure-hopf-family-sphere-1

compute-meridian-hopf-family-sphere-1 :
  (x : sphere 1) →
  ( ( ap hopf-family-sphere-1 (meridian-sphere 1 x)) ∙
    ( compute-south-hopf-family-sphere-1)) ＝
  ( ( compute-north-hopf-family-sphere-1) ∙
    ( eq-equiv (equiv-left-mul-sphere-1 x)))
compute-meridian-hopf-family-sphere-1 =
  compute-meridian-cogap-suspension suspension-structure-hopf-family-sphere-1
```

### The total space of the Hopf family

```agda
total-space-hopf-family-sphere-1 : UU lzero
total-space-hopf-family-sphere-1 =
  Σ (sphere 2) hopf-family-sphere-1
```

### The flattened span of the Hopf family

```agda
span-diagram-flattening-family-hopf-family-sphere-1 :
  span-diagram lzero lzero lzero
span-diagram-flattening-family-hopf-family-sphere-1 =
  span-diagram-flattening-pushout
    ( cocone-suspension (sphere 1))
    ( hopf-family-sphere-1)

equiv-domain-flattening-family-hopf-family-sphere-1 :
  domain-span-diagram span-diagram-flattening-family-hopf-family-sphere-1 ≃
  sphere 1
equiv-domain-flattening-family-hopf-family-sphere-1 =
  ( equiv-eq compute-north-hopf-family-sphere-1) ∘e
  ( left-unit-law-Σ
    ( λ _ → hopf-family-sphere-1 (north-sphere 2)))

equiv-codomain-flattening-family-hopf-family-sphere-1 :
  codomain-span-diagram span-diagram-flattening-family-hopf-family-sphere-1 ≃
  sphere 1
equiv-codomain-flattening-family-hopf-family-sphere-1 =
  ( equiv-eq compute-south-hopf-family-sphere-1) ∘e
  ( left-unit-law-Σ
    ( λ _ → hopf-family-sphere-1 (south-sphere 2)))

cocone-flattening-family-hopf-family-sphere-1 :
  cocone
    ( left-map-span-diagram
      span-diagram-flattening-family-hopf-family-sphere-1)
    ( right-map-span-diagram
      span-diagram-flattening-family-hopf-family-sphere-1)
    ( total-space-hopf-family-sphere-1)
cocone-flattening-family-hopf-family-sphere-1 =
  cocone-flattening-pushout
    ( hopf-family-sphere-1)
    ( terminal-map (sphere 1))
    ( terminal-map (sphere 1))
    ( cocone-suspension (sphere 1))

universal-property-pushout-cocone-flattening-family-hopf-family-sphere-1 :
  universal-property-pushout
    ( left-map-span-diagram
      span-diagram-flattening-family-hopf-family-sphere-1)
    ( right-map-span-diagram
      span-diagram-flattening-family-hopf-family-sphere-1)
    ( cocone-flattening-family-hopf-family-sphere-1)
universal-property-pushout-cocone-flattening-family-hopf-family-sphere-1 =
  flattening-lemma-pushout
    ( hopf-family-sphere-1)
    ( terminal-map (sphere 1))
    ( terminal-map (sphere 1))
    ( cocone-suspension (sphere 1))
    ( up-suspension' (sphere 1))
```

### The flattened Hopf-family descent span

```agda
span-diagram-suspension-sphere-1 : span-diagram lzero lzero lzero
span-diagram-suspension-sphere-1 =
  make-span-diagram
    ( terminal-map (sphere 1))
    ( terminal-map (sphere 1))

descent-data-hopf-family-sphere-1 :
  descent-data-pushout span-diagram-suspension-sphere-1 lzero lzero
pr1 descent-data-hopf-family-sphere-1 _ =
  sphere 1
pr1 (pr2 descent-data-hopf-family-sphere-1) _ =
  sphere 1
pr2 (pr2 descent-data-hopf-family-sphere-1) x =
  equiv-left-mul-sphere-1 x

span-diagram-flattening-hopf-family-sphere-1 :
  span-diagram lzero lzero lzero
span-diagram-flattening-hopf-family-sphere-1 =
  span-diagram-flattening-descent-data-pushout
    descent-data-hopf-family-sphere-1

equiv-spanning-type-flattening-hopf-family-sphere-1 :
  spanning-type-span-diagram
    span-diagram-flattening-family-hopf-family-sphere-1 ≃
  spanning-type-span-diagram
    span-diagram-flattening-hopf-family-sphere-1
equiv-spanning-type-flattening-hopf-family-sphere-1 =
  equiv-tot (λ _ → equiv-eq compute-north-hopf-family-sphere-1)

equiv-domain-comparison-flattening-hopf-family-sphere-1 :
  domain-span-diagram
    span-diagram-flattening-family-hopf-family-sphere-1 ≃
  domain-span-diagram
    span-diagram-flattening-hopf-family-sphere-1
equiv-domain-comparison-flattening-hopf-family-sphere-1 =
  equiv-tot (λ _ → equiv-eq compute-north-hopf-family-sphere-1)

equiv-codomain-comparison-flattening-hopf-family-sphere-1 :
  codomain-span-diagram
    span-diagram-flattening-family-hopf-family-sphere-1 ≃
  codomain-span-diagram
    span-diagram-flattening-hopf-family-sphere-1
equiv-codomain-comparison-flattening-hopf-family-sphere-1 =
  equiv-tot (λ _ → equiv-eq compute-south-hopf-family-sphere-1)

coherence-left-map-comparison-flattening-hopf-family-sphere-1 :
  coherence-square-maps
    ( left-map-span-diagram
      span-diagram-flattening-family-hopf-family-sphere-1)
    ( map-equiv equiv-spanning-type-flattening-hopf-family-sphere-1)
    ( map-equiv equiv-domain-comparison-flattening-hopf-family-sphere-1)
    ( left-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
coherence-left-map-comparison-flattening-hopf-family-sphere-1 _ =
  refl

equiv-meridian-hopf-family-sphere-1 :
  (x : sphere 1) →
  ( equiv-eq compute-south-hopf-family-sphere-1) ∘e
  ( equiv-eq (ap hopf-family-sphere-1 (meridian-sphere 1 x))) ＝
  ( equiv-left-mul-sphere-1 x) ∘e
  ( equiv-eq compute-north-hopf-family-sphere-1)
equiv-meridian-hopf-family-sphere-1 x =
  ( compute-equiv-eq-concat
    ( ap hopf-family-sphere-1 (meridian-sphere 1 x))
    ( compute-south-hopf-family-sphere-1)) ∙
  ( ap equiv-eq (compute-meridian-hopf-family-sphere-1 x)) ∙
  ( inv
    ( compute-equiv-eq-concat
      ( compute-north-hopf-family-sphere-1)
      ( eq-equiv (equiv-left-mul-sphere-1 x)))) ∙
  ( ap
    ( λ e → e ∘e equiv-eq compute-north-hopf-family-sphere-1)
    ( ap
      ( λ e → map-equiv e (equiv-left-mul-sphere-1 x))
      ( right-inverse-law-equiv equiv-univalence)))

compute-right-map-meridian-hopf-family-sphere-1 :
  (x : sphere 1) (y : hopf-family-sphere-1 (north-sphere 2)) →
  map-equiv (equiv-left-mul-sphere-1 x)
    ( map-eq compute-north-hopf-family-sphere-1 y) ＝
  map-eq compute-south-hopf-family-sphere-1
    ( tr hopf-family-sphere-1 (meridian-sphere 1 x) y)
compute-right-map-meridian-hopf-family-sphere-1 x y =
  inv
    ( ( ap
        ( λ f → map-eq compute-south-hopf-family-sphere-1 (f y))
        ( inv
          ( compute-map-eq-ap
            { B = hopf-family-sphere-1}
            ( meridian-sphere 1 x)))) ∙
      ( ap (λ e → map-equiv e y) (equiv-meridian-hopf-family-sphere-1 x)))

coherence-right-map-comparison-flattening-hopf-family-sphere-1 :
  coherence-square-maps
    ( right-map-span-diagram
      span-diagram-flattening-family-hopf-family-sphere-1)
    ( map-equiv equiv-spanning-type-flattening-hopf-family-sphere-1)
    ( map-equiv equiv-codomain-comparison-flattening-hopf-family-sphere-1)
    ( right-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
coherence-right-map-comparison-flattening-hopf-family-sphere-1 (x , y) =
  eq-pair-Σ refl
    ( compute-right-map-meridian-hopf-family-sphere-1 x y)

coherence-left-map-inv-comparison-flattening-hopf-family-sphere-1 :
  coherence-square-maps
    ( map-inv-equiv equiv-spanning-type-flattening-hopf-family-sphere-1)
    ( left-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( left-map-span-diagram
      span-diagram-flattening-family-hopf-family-sphere-1)
    ( map-inv-equiv equiv-domain-comparison-flattening-hopf-family-sphere-1)
coherence-left-map-inv-comparison-flattening-hopf-family-sphere-1 =
  inv-htpy
    ( vertical-inv-equiv-coherence-square-maps
      ( left-map-span-diagram
        span-diagram-flattening-family-hopf-family-sphere-1)
      ( equiv-spanning-type-flattening-hopf-family-sphere-1)
      ( equiv-domain-comparison-flattening-hopf-family-sphere-1)
      ( left-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
      ( coherence-left-map-comparison-flattening-hopf-family-sphere-1))

coherence-right-map-inv-comparison-flattening-hopf-family-sphere-1 :
  coherence-square-maps
    ( right-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( map-inv-equiv equiv-spanning-type-flattening-hopf-family-sphere-1)
    ( map-inv-equiv equiv-codomain-comparison-flattening-hopf-family-sphere-1)
    ( right-map-span-diagram
      span-diagram-flattening-family-hopf-family-sphere-1)
coherence-right-map-inv-comparison-flattening-hopf-family-sphere-1 =
  vertical-inv-equiv-coherence-square-maps
    ( right-map-span-diagram
      span-diagram-flattening-family-hopf-family-sphere-1)
    ( equiv-spanning-type-flattening-hopf-family-sphere-1)
    ( equiv-codomain-comparison-flattening-hopf-family-sphere-1)
    ( right-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( coherence-right-map-comparison-flattening-hopf-family-sphere-1)

cocone-total-space-flattening-hopf-family-sphere-1 :
  cocone
    ( left-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( right-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( total-space-hopf-family-sphere-1)
cocone-total-space-flattening-hopf-family-sphere-1 =
  comp-cocone-hom-span
    ( left-map-span-diagram
      span-diagram-flattening-family-hopf-family-sphere-1)
    ( right-map-span-diagram
      span-diagram-flattening-family-hopf-family-sphere-1)
    ( left-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( right-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( map-inv-equiv equiv-domain-comparison-flattening-hopf-family-sphere-1)
    ( map-inv-equiv equiv-codomain-comparison-flattening-hopf-family-sphere-1)
    ( map-inv-equiv equiv-spanning-type-flattening-hopf-family-sphere-1)
    ( cocone-flattening-family-hopf-family-sphere-1)
    ( coherence-left-map-inv-comparison-flattening-hopf-family-sphere-1)
    ( coherence-right-map-inv-comparison-flattening-hopf-family-sphere-1)

universal-property-pushout-cocone-total-space-flattening-hopf-family-sphere-1 :
  universal-property-pushout
    ( left-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( right-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( cocone-total-space-flattening-hopf-family-sphere-1)
universal-property-pushout-cocone-total-space-flattening-hopf-family-sphere-1 =
  universal-property-pushout-extended-by-equivalences
    ( left-map-span-diagram
      span-diagram-flattening-family-hopf-family-sphere-1)
    ( right-map-span-diagram
      span-diagram-flattening-family-hopf-family-sphere-1)
    ( left-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( right-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( map-inv-equiv equiv-domain-comparison-flattening-hopf-family-sphere-1)
    ( map-inv-equiv equiv-codomain-comparison-flattening-hopf-family-sphere-1)
    ( map-inv-equiv equiv-spanning-type-flattening-hopf-family-sphere-1)
    ( cocone-flattening-family-hopf-family-sphere-1)
    ( universal-property-pushout-cocone-flattening-family-hopf-family-sphere-1)
    ( coherence-left-map-inv-comparison-flattening-hopf-family-sphere-1)
    ( coherence-right-map-inv-comparison-flattening-hopf-family-sphere-1)
    ( is-equiv-map-inv-equiv
      equiv-domain-comparison-flattening-hopf-family-sphere-1)
    ( is-equiv-map-inv-equiv
      equiv-codomain-comparison-flattening-hopf-family-sphere-1)
    ( is-equiv-map-inv-equiv
      equiv-spanning-type-flattening-hopf-family-sphere-1)

equiv-domain-flattening-hopf-family-sphere-1 :
  domain-span-diagram span-diagram-flattening-hopf-family-sphere-1 ≃
  sphere 1
equiv-domain-flattening-hopf-family-sphere-1 =
  left-unit-law-Σ (λ _ → sphere 1)

equiv-codomain-flattening-hopf-family-sphere-1 :
  codomain-span-diagram span-diagram-flattening-hopf-family-sphere-1 ≃
  sphere 1
equiv-codomain-flattening-hopf-family-sphere-1 =
  left-unit-law-Σ (λ _ → sphere 1)

cocone-join-flattening-hopf-family-sphere-1 :
  cocone
    ( left-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( right-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( sphere 1 * sphere 1)
cocone-join-flattening-hopf-family-sphere-1 =
  comp-cocone-hom-span
    ( pr1)
    ( pr2)
    ( left-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( right-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( map-equiv equiv-domain-flattening-hopf-family-sphere-1)
    ( map-equiv equiv-codomain-flattening-hopf-family-sphere-1)
    ( hopf-shear-sphere-1)
    ( cocone-join)
    ( λ _ → refl)
    ( λ _ → refl)

universal-property-pushout-cocone-join-flattening-hopf-family-sphere-1 :
  universal-property-pushout
    ( left-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( right-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( cocone-join-flattening-hopf-family-sphere-1)
universal-property-pushout-cocone-join-flattening-hopf-family-sphere-1 =
  universal-property-pushout-extended-by-equivalences
    ( pr1)
    ( pr2)
    ( left-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( right-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( map-equiv equiv-domain-flattening-hopf-family-sphere-1)
    ( map-equiv equiv-codomain-flattening-hopf-family-sphere-1)
    ( hopf-shear-sphere-1)
    ( cocone-join)
    ( up-join)
    ( λ _ → refl)
    ( λ _ → refl)
    ( is-equiv-map-equiv equiv-domain-flattening-hopf-family-sphere-1)
    ( is-equiv-map-equiv equiv-codomain-flattening-hopf-family-sphere-1)
    ( is-equiv-map-equiv equiv-hopf-shear-sphere-1)

map-total-space-hopf-family-sphere-1-join-sphere-1 :
  total-space-hopf-family-sphere-1 → sphere 1 * sphere 1
map-total-space-hopf-family-sphere-1-join-sphere-1 =
  map-universal-property-pushout
    ( left-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( right-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( cocone-total-space-flattening-hopf-family-sphere-1)
    ( universal-property-pushout-cocone-total-space-flattening-hopf-family-sphere-1)
    ( cocone-join-flattening-hopf-family-sphere-1)

is-equiv-map-total-space-hopf-family-sphere-1-join-sphere-1 :
  is-equiv map-total-space-hopf-family-sphere-1-join-sphere-1
is-equiv-map-total-space-hopf-family-sphere-1-join-sphere-1 =
  is-equiv-up-pushout-up-pushout
    ( left-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( right-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
    ( cocone-total-space-flattening-hopf-family-sphere-1)
    ( cocone-join-flattening-hopf-family-sphere-1)
    ( map-total-space-hopf-family-sphere-1-join-sphere-1)
    ( htpy-cocone-map-universal-property-pushout
      ( left-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
      ( right-map-span-diagram span-diagram-flattening-hopf-family-sphere-1)
      ( cocone-total-space-flattening-hopf-family-sphere-1)
      ( universal-property-pushout-cocone-total-space-flattening-hopf-family-sphere-1)
      ( cocone-join-flattening-hopf-family-sphere-1))
    ( universal-property-pushout-cocone-total-space-flattening-hopf-family-sphere-1)
    ( universal-property-pushout-cocone-join-flattening-hopf-family-sphere-1)

equiv-total-space-hopf-family-sphere-1-join-sphere-1 :
  total-space-hopf-family-sphere-1 ≃ sphere 1 * sphere 1
pr1 equiv-total-space-hopf-family-sphere-1-join-sphere-1 =
  map-total-space-hopf-family-sphere-1-join-sphere-1
pr2 equiv-total-space-hopf-family-sphere-1-join-sphere-1 =
  is-equiv-map-total-space-hopf-family-sphere-1-join-sphere-1

equiv-total-space-hopf-family-sphere-1-total-space-hopf-construction-sphere-1 :
  total-space-hopf-family-sphere-1 ≃
  total-space-hopf-construction-sphere-1
equiv-total-space-hopf-family-sphere-1-total-space-hopf-construction-sphere-1 =
  equiv-total-space-hopf-family-sphere-1-join-sphere-1

equiv-total-space-hopf-family-sphere-1-join-power-Fin-2 :
  total-space-hopf-family-sphere-1 ≃
  join-power 2 (Fin 2) * join-power 2 (Fin 2)
equiv-total-space-hopf-family-sphere-1-join-power-Fin-2 =
  equiv-join-sphere-1-join-power-Fin-2 ∘e
  equiv-total-space-hopf-family-sphere-1-join-sphere-1
```

### The projection from the total space of the Hopf family

```agda
point-hopf-family-sphere-1 :
  hopf-family-sphere-1 (north-sphere 2)
point-hopf-family-sphere-1 =
  map-inv-equiv
    ( equiv-eq compute-north-hopf-family-sphere-1)
    ( north-sphere 1)

pointed-total-space-hopf-family-sphere-1 : Pointed-Type lzero
pr1 pointed-total-space-hopf-family-sphere-1 =
  total-space-hopf-family-sphere-1
pr2 pointed-total-space-hopf-family-sphere-1 =
  north-sphere 2 , point-hopf-family-sphere-1

projection-hopf-family-sphere-1 :
  total-space-hopf-family-sphere-1 → sphere 2
projection-hopf-family-sphere-1 =
  pr1

pointed-map-projection-hopf-family-sphere-1 :
  pointed-total-space-hopf-family-sphere-1 →∗ sphere-Pointed-Type 2
pr1 pointed-map-projection-hopf-family-sphere-1 =
  projection-hopf-family-sphere-1
pr2 pointed-map-projection-hopf-family-sphere-1 =
  refl
```

### The fiber over the north pole

```agda
equiv-fiber-projection-hopf-family-sphere-1 :
  type-Pointed-Type
    ( fiber-Pointed-Type pointed-map-projection-hopf-family-sphere-1) ≃
  sphere 1
equiv-fiber-projection-hopf-family-sphere-1 =
  ( equiv-eq compute-north-hopf-family-sphere-1) ∘e
  ( equiv-fiber-pr1 hopf-family-sphere-1 (north-sphere 2))

pointed-equiv-fiber-projection-hopf-family-sphere-1 :
  fiber-Pointed-Type pointed-map-projection-hopf-family-sphere-1 ≃∗
  sphere-Pointed-Type 1
pr1 pointed-equiv-fiber-projection-hopf-family-sphere-1 =
  equiv-fiber-projection-hopf-family-sphere-1
pr2 pointed-equiv-fiber-projection-hopf-family-sphere-1 =
  is-section-map-inv-equiv
    ( equiv-eq compute-north-hopf-family-sphere-1)
    ( north-sphere 1)

pointed-equiv-sphere-1-fiber-projection-hopf-family-sphere-1 :
  sphere-Pointed-Type 1 ≃∗
  fiber-Pointed-Type pointed-map-projection-hopf-family-sphere-1
pointed-equiv-sphere-1-fiber-projection-hopf-family-sphere-1 =
  inv-pointed-equiv pointed-equiv-fiber-projection-hopf-family-sphere-1
```

### The fiber sequence of the Hopf family

```agda
fiber-inclusion-hopf-family-sphere-1 :
  sphere-Pointed-Type 1 →∗ pointed-total-space-hopf-family-sphere-1
fiber-inclusion-hopf-family-sphere-1 =
  ( inclusion-fiber-Pointed-Type
    ( pointed-map-projection-hopf-family-sphere-1)) ∘∗
  ( pointed-map-pointed-equiv
    ( pointed-equiv-sphere-1-fiber-projection-hopf-family-sphere-1))

is-fiber-sequence-hopf-family-sphere-1 :
  is-fiber-sequence-Pointed-Type
    ( fiber-inclusion-hopf-family-sphere-1)
    ( pointed-map-projection-hopf-family-sphere-1)
pr1 is-fiber-sequence-hopf-family-sphere-1 =
  pointed-equiv-sphere-1-fiber-projection-hopf-family-sphere-1
pr2 is-fiber-sequence-hopf-family-sphere-1 =
  refl-pointed-htpy fiber-inclusion-hopf-family-sphere-1

fiber-sequence-hopf-family-sphere-1 :
  fiber-sequence-Pointed-Type lzero lzero lzero
pr1 fiber-sequence-hopf-family-sphere-1 =
  sphere-Pointed-Type 1
pr1 (pr2 fiber-sequence-hopf-family-sphere-1) =
  pointed-total-space-hopf-family-sphere-1
pr1 (pr2 (pr2 fiber-sequence-hopf-family-sphere-1)) =
  sphere-Pointed-Type 2
pr1 (pr2 (pr2 (pr2 fiber-sequence-hopf-family-sphere-1))) =
  fiber-inclusion-hopf-family-sphere-1
pr1 (pr2 (pr2 (pr2 (pr2 fiber-sequence-hopf-family-sphere-1)))) =
  pointed-map-projection-hopf-family-sphere-1
pr2 (pr2 (pr2 (pr2 (pr2 fiber-sequence-hopf-family-sphere-1)))) =
  is-fiber-sequence-hopf-family-sphere-1
```
