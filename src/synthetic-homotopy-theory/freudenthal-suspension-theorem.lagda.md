# The Freudenthal suspension theorem

```agda
module synthetic-homotopy-theory.freudenthal-suspension-theorem where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterated-successors-truncation-levels
open import foundation.standard-pullbacks
open import foundation.transport-along-identifications
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.gap-maps-pushouts
open import synthetic-homotopy-theory.suspensions-of-pointed-types
open import synthetic-homotopy-theory.suspensions-of-types
open import synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types
```

</details>

## Idea

The unit of the suspension-loop adjunction

```text
  A → ΩΣA
```

is the map appearing in the Freudenthal suspension theorem. If `A` is
`(n+1)`-connected, Freudenthal says that this unit is `(2n+2)`-connected. In
the natural-number-indexed part of agda-unimath's truncation levels, the two
bounds are recorded by the following functions.

## Definitions

### The connectivity range in the Freudenthal suspension theorem

```agda
freudenthal-domain-connectivity-level-ℕ : ℕ → ℕ
freudenthal-domain-connectivity-level-ℕ n = succ-ℕ n

freudenthal-connectivity-level-ℕ : ℕ → ℕ
freudenthal-connectivity-level-ℕ n = succ-ℕ (succ-ℕ (n +ℕ n))
```

### Truncation-level arithmetic for the Freudenthal range

```agda
compute-freudenthal-domain-connectivity-level-𝕋 :
  (n : ℕ) →
  truncation-level-ℕ (freudenthal-domain-connectivity-level-ℕ n) ＝
  succ-𝕋 (truncation-level-ℕ n)
compute-freudenthal-domain-connectivity-level-𝕋 n = refl

compute-freudenthal-connectivity-level-add+2-𝕋 :
  (n : ℕ) →
  truncation-level-ℕ (freudenthal-connectivity-level-ℕ n) ＝
  add+2-𝕋 (truncation-level-ℕ n) (truncation-level-ℕ n)
compute-freudenthal-connectivity-level-add+2-𝕋 zero-ℕ = refl
compute-freudenthal-connectivity-level-add+2-𝕋 (succ-ℕ n) =
  ( ap
    ( λ m → truncation-level-ℕ (succ-ℕ (succ-ℕ (succ-ℕ m))))
    ( left-successor-law-add-ℕ n n)) ∙
  ( ap
    ( λ k → succ-𝕋 (succ-𝕋 k))
    ( compute-freudenthal-connectivity-level-add+2-𝕋 n)) ∙
  ( inv
    ( ap
      ( succ-𝕋)
      ( left-successor-law-add+2-𝕋
        ( truncation-level-ℕ n)
        ( truncation-level-ℕ n))))
```

### The suspension stabilization map

```agda
pointed-map-Freudenthal-suspension :
  {l : Level} (A : Pointed-Type l) →
  A →∗ Ω (suspension-Pointed-Type A)
pointed-map-Freudenthal-suspension =
  pointed-map-unit-suspension-loop-adjunction

map-Freudenthal-suspension :
  {l : Level} (A : Pointed-Type l) →
  type-Pointed-Type A → type-Ω (suspension-Pointed-Type A)
map-Freudenthal-suspension A =
  map-pointed-map (pointed-map-Freudenthal-suspension A)
```

## Properties

### Computing the Freudenthal suspension map

```agda
compute-map-Freudenthal-suspension :
  {l : Level} (A : Pointed-Type l) (a : type-Pointed-Type A) →
  map-Freudenthal-suspension A a ＝
  ( meridian-suspension a ∙
    inv (meridian-suspension (point-Pointed-Type A)))
compute-map-Freudenthal-suspension A a = refl
```

### The Freudenthal suspension map as a gap map

The suspension is the pushout of the span `unit ← A → unit`. Its gap map lands
in the standard pullback of the two pole inclusions. Composing that gap map with
the equivalence from paths `north = south` to loops at `north` recovers the
Freudenthal suspension map.

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  cone-Freudenthal-suspension :
    cone
      ( point (north-suspension {X = type-Pointed-Type A}))
      ( point (south-suspension {X = type-Pointed-Type A}))
      ( type-Pointed-Type A)
  pr1 cone-Freudenthal-suspension = terminal-map (type-Pointed-Type A)
  pr1 (pr2 cone-Freudenthal-suspension) = terminal-map (type-Pointed-Type A)
  pr2 (pr2 cone-Freudenthal-suspension) = meridian-suspension

  gap-Freudenthal-suspension :
    type-Pointed-Type A →
    standard-pullback
      ( point (north-suspension {X = type-Pointed-Type A}))
      ( point (south-suspension {X = type-Pointed-Type A}))
  gap-Freudenthal-suspension =
    gap
      ( point (north-suspension {X = type-Pointed-Type A}))
      ( point (south-suspension {X = type-Pointed-Type A}))
      ( cone-Freudenthal-suspension)

  map-standard-pullback-Freudenthal-suspension :
    standard-pullback
      ( point (north-suspension {X = type-Pointed-Type A}))
      ( point (south-suspension {X = type-Pointed-Type A})) →
    type-Ω (suspension-Pointed-Type A)
  map-standard-pullback-Freudenthal-suspension t =
    ( coherence-square-standard-pullback t) ∙
    ( inv (meridian-suspension (point-Pointed-Type A)))

  map-inv-standard-pullback-Freudenthal-suspension :
    type-Ω (suspension-Pointed-Type A) →
    standard-pullback
      ( point (north-suspension {X = type-Pointed-Type A}))
      ( point (south-suspension {X = type-Pointed-Type A}))
  pr1 (map-inv-standard-pullback-Freudenthal-suspension p) = star
  pr1 (pr2 (map-inv-standard-pullback-Freudenthal-suspension p)) = star
  pr2 (pr2 (map-inv-standard-pullback-Freudenthal-suspension p)) =
    p ∙ meridian-suspension (point-Pointed-Type A)

  is-section-map-inv-standard-pullback-Freudenthal-suspension :
    ( map-standard-pullback-Freudenthal-suspension ∘
      map-inv-standard-pullback-Freudenthal-suspension) ~
    id
  is-section-map-inv-standard-pullback-Freudenthal-suspension p =
    ( assoc p
      ( meridian-suspension (point-Pointed-Type A))
      ( inv (meridian-suspension (point-Pointed-Type A)))) ∙
    ( ap
      ( p ∙_)
      ( right-inv (meridian-suspension (point-Pointed-Type A)))) ∙
    ( right-unit)

  is-retraction-map-inv-standard-pullback-Freudenthal-suspension :
    ( map-inv-standard-pullback-Freudenthal-suspension ∘
      map-standard-pullback-Freudenthal-suspension) ~
    id
  is-retraction-map-inv-standard-pullback-Freudenthal-suspension
    (star , star , p) =
    eq-Eq-standard-pullback
      ( point (north-suspension {X = type-Pointed-Type A}))
      ( point (south-suspension {X = type-Pointed-Type A}))
      ( refl)
      ( refl)
      ( ( left-unit) ∙
        ( inv
          ( ( assoc p
              ( inv (meridian-suspension (point-Pointed-Type A)))
              ( meridian-suspension (point-Pointed-Type A))) ∙
            ( ap
              ( p ∙_)
              ( left-inv (meridian-suspension (point-Pointed-Type A)))) ∙
            ( right-unit))) ∙
        ( inv right-unit))

  is-equiv-map-standard-pullback-Freudenthal-suspension :
    is-equiv map-standard-pullback-Freudenthal-suspension
  is-equiv-map-standard-pullback-Freudenthal-suspension =
    is-equiv-is-invertible
      ( map-inv-standard-pullback-Freudenthal-suspension)
      ( is-section-map-inv-standard-pullback-Freudenthal-suspension)
      ( is-retraction-map-inv-standard-pullback-Freudenthal-suspension)

  equiv-standard-pullback-Freudenthal-suspension :
    standard-pullback
      ( point (north-suspension {X = type-Pointed-Type A}))
      ( point (south-suspension {X = type-Pointed-Type A})) ≃
    type-Ω (suspension-Pointed-Type A)
  pr1 equiv-standard-pullback-Freudenthal-suspension =
    map-standard-pullback-Freudenthal-suspension
  pr2 equiv-standard-pullback-Freudenthal-suspension =
    is-equiv-map-standard-pullback-Freudenthal-suspension

  triangle-map-Freudenthal-suspension-gap :
    ( map-standard-pullback-Freudenthal-suspension ∘
      gap-Freudenthal-suspension) ~
    map-Freudenthal-suspension A
  triangle-map-Freudenthal-suspension-gap a = refl

  triangle-gap-pushout-suspension-gap-Freudenthal-suspension :
    gap-pushout
      ( terminal-map (type-Pointed-Type A))
      ( terminal-map (type-Pointed-Type A))
      ( cocone-suspension (type-Pointed-Type A)) ~
    gap-Freudenthal-suspension
  triangle-gap-pushout-suspension-gap-Freudenthal-suspension a = refl
```

### Reducing Freudenthal to connectivity of the suspension-square gap map

```agda
module _
  {l : Level} (n : ℕ) (A : Pointed-Type l)
  where

  is-connected-map-gap-Freudenthal-suspension : UU l
  is-connected-map-gap-Freudenthal-suspension =
    is-connected
      ( truncation-level-ℕ (freudenthal-domain-connectivity-level-ℕ n))
      ( type-Pointed-Type A) →
    is-connected-map
      ( truncation-level-ℕ (freudenthal-connectivity-level-ℕ n))
      ( gap-Freudenthal-suspension A)

  is-connected-map-Freudenthal-suspension-is-connected-map-gap :
    is-connected-map
      ( truncation-level-ℕ (freudenthal-connectivity-level-ℕ n))
      ( gap-Freudenthal-suspension A) →
    is-connected-map
      ( truncation-level-ℕ (freudenthal-connectivity-level-ℕ n))
      ( map-Freudenthal-suspension A)
  is-connected-map-Freudenthal-suspension-is-connected-map-gap H =
    is-connected-map-htpy'
      ( truncation-level-ℕ (freudenthal-connectivity-level-ℕ n))
      ( triangle-map-Freudenthal-suspension-gap A)
      ( is-connected-map-comp
        ( truncation-level-ℕ (freudenthal-connectivity-level-ℕ n))
        ( is-connected-map-is-equiv
          ( is-equiv-map-standard-pullback-Freudenthal-suspension A))
        ( H))

  is-connected-map-gap-Freudenthal-suspension-is-connected-map-gap-pushout-suspension :
    is-connected-map
      ( truncation-level-ℕ (freudenthal-connectivity-level-ℕ n))
      ( gap-pushout
        ( terminal-map (type-Pointed-Type A))
        ( terminal-map (type-Pointed-Type A))
        ( cocone-suspension (type-Pointed-Type A))) →
    is-connected-map
      ( truncation-level-ℕ (freudenthal-connectivity-level-ℕ n))
      ( gap-Freudenthal-suspension A)
  is-connected-map-gap-Freudenthal-suspension-is-connected-map-gap-pushout-suspension =
    is-connected-map-htpy'
      ( truncation-level-ℕ (freudenthal-connectivity-level-ℕ n))
      ( triangle-gap-pushout-suspension-gap-Freudenthal-suspension A)

  is-connected-map-Freudenthal-suspension-is-connected-map-gap-pushout-suspension :
    is-connected-map
      ( truncation-level-ℕ (freudenthal-connectivity-level-ℕ n))
      ( gap-pushout
        ( terminal-map (type-Pointed-Type A))
        ( terminal-map (type-Pointed-Type A))
        ( cocone-suspension (type-Pointed-Type A))) →
    is-connected-map
      ( truncation-level-ℕ (freudenthal-connectivity-level-ℕ n))
      ( map-Freudenthal-suspension A)
  is-connected-map-Freudenthal-suspension-is-connected-map-gap-pushout-suspension H =
    is-connected-map-Freudenthal-suspension-is-connected-map-gap
      ( is-connected-map-gap-Freudenthal-suspension-is-connected-map-gap-pushout-suspension
        ( H))

  is-connected-map-Freudenthal-suspension-is-connected-map-gap-pushout-suspension-add+2 :
    is-connected-map
      ( add+2-𝕋 (truncation-level-ℕ n) (truncation-level-ℕ n))
      ( gap-pushout
        ( terminal-map (type-Pointed-Type A))
        ( terminal-map (type-Pointed-Type A))
        ( cocone-suspension (type-Pointed-Type A))) →
    is-connected-map
      ( truncation-level-ℕ (freudenthal-connectivity-level-ℕ n))
      ( map-Freudenthal-suspension A)
  is-connected-map-Freudenthal-suspension-is-connected-map-gap-pushout-suspension-add+2 H =
    is-connected-map-Freudenthal-suspension-is-connected-map-gap-pushout-suspension
      ( tr
        ( λ k →
          is-connected-map k
            ( gap-pushout
              ( terminal-map (type-Pointed-Type A))
              ( terminal-map (type-Pointed-Type A))
              ( cocone-suspension (type-Pointed-Type A))))
        ( inv (compute-freudenthal-connectivity-level-add+2-𝕋 n))
        ( H))
```

### The Freudenthal suspension theorem as a reusable target statement

```agda
is-connected-map-Freudenthal-suspension :
  {l : Level} (n : ℕ) (A : Pointed-Type l) → UU l
is-connected-map-Freudenthal-suspension n A =
  is-connected
    ( truncation-level-ℕ (freudenthal-domain-connectivity-level-ℕ n))
    ( type-Pointed-Type A) →
  is-connected-map
    ( truncation-level-ℕ (freudenthal-connectivity-level-ℕ n))
    ( map-Freudenthal-suspension A)

is-connected-map-Freudenthal-suspension-is-connected-map-gap-Freudenthal-suspension :
  {l : Level} (n : ℕ) (A : Pointed-Type l) →
  is-connected-map-gap-Freudenthal-suspension n A →
  is-connected-map-Freudenthal-suspension n A
is-connected-map-Freudenthal-suspension-is-connected-map-gap-Freudenthal-suspension
  n A H c =
  is-connected-map-Freudenthal-suspension-is-connected-map-gap n A (H c)
```
