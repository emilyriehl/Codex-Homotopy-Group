# Fiber sequences of fiber inclusions

```agda
module synthetic-homotopy-theory.fiber-sequences-fiber-inclusions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.fiber-sequences
open import structured-types.fibers-of-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.connecting-fiber-sequences
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

The first shifted fiber sequence associated to a pointed map `g : E →∗ B`
identifies the fiber of the canonical fiber inclusion with the loop space of
the base. Equivalently, it packages

```text
  Ω B →∗ fiber g →∗ E
```

as a pointed fiber sequence.

## Definitions

```agda
module _
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B)
  where

  map-fiber-inclusion-path-Pointed-Type :
    map-pointed-map g (point-Pointed-Type E) ＝ point-Pointed-Type B →
    type-Pointed-Type
      ( fiber-Pointed-Type (inclusion-fiber-Pointed-Type g))
  map-fiber-inclusion-path-Pointed-Type p =
    ( ( point-Pointed-Type E , p) , refl)

  map-inv-fiber-inclusion-path-Pointed-Type :
    type-Pointed-Type
      ( fiber-Pointed-Type (inclusion-fiber-Pointed-Type g)) →
    map-pointed-map g (point-Pointed-Type E) ＝ point-Pointed-Type B
  map-inv-fiber-inclusion-path-Pointed-Type ((x , p) , q) =
    inv (ap (map-pointed-map g) q) ∙ p

  is-section-map-inv-fiber-inclusion-path-Pointed-Type :
    (x :
      type-Pointed-Type
        ( fiber-Pointed-Type (inclusion-fiber-Pointed-Type g))) →
    map-fiber-inclusion-path-Pointed-Type
      ( map-inv-fiber-inclusion-path-Pointed-Type x) ＝ x
  is-section-map-inv-fiber-inclusion-path-Pointed-Type
    ((.(point-Pointed-Type E) , p) , refl) =
    refl

  is-retraction-map-inv-fiber-inclusion-path-Pointed-Type :
    (p : map-pointed-map g (point-Pointed-Type E) ＝ point-Pointed-Type B) →
    map-inv-fiber-inclusion-path-Pointed-Type
      ( map-fiber-inclusion-path-Pointed-Type p) ＝ p
  is-retraction-map-inv-fiber-inclusion-path-Pointed-Type p = refl

  is-equiv-map-fiber-inclusion-path-Pointed-Type :
    is-equiv map-fiber-inclusion-path-Pointed-Type
  is-equiv-map-fiber-inclusion-path-Pointed-Type =
    is-equiv-is-invertible
      ( map-inv-fiber-inclusion-path-Pointed-Type)
      ( is-section-map-inv-fiber-inclusion-path-Pointed-Type)
      ( is-retraction-map-inv-fiber-inclusion-path-Pointed-Type)

  equiv-fiber-inclusion-path-Pointed-Type :
    ( map-pointed-map g (point-Pointed-Type E) ＝ point-Pointed-Type B) ≃
    type-Pointed-Type
      ( fiber-Pointed-Type (inclusion-fiber-Pointed-Type g))
  pr1 equiv-fiber-inclusion-path-Pointed-Type =
    map-fiber-inclusion-path-Pointed-Type
  pr2 equiv-fiber-inclusion-path-Pointed-Type =
    is-equiv-map-fiber-inclusion-path-Pointed-Type

  equiv-fiber-inclusion-boundary-fiber-Pointed-Type :
    type-Ω B ≃
    type-Pointed-Type
      ( fiber-Pointed-Type (inclusion-fiber-Pointed-Type g))
  equiv-fiber-inclusion-boundary-fiber-Pointed-Type =
    equiv-fiber-inclusion-path-Pointed-Type ∘e
    equiv-concat (preserves-point-pointed-map g) (point-Pointed-Type B)

  dependent-identification-eq-pair-fiber-inclusion-Pointed-Type :
    {p q : map-pointed-map g (point-Pointed-Type E) ＝ point-Pointed-Type B}
    (α : p ＝ q) →
    dependent-identification
      ( λ x → pr1 x ＝ point-Pointed-Type E)
      ( eq-pair-Σ
        { A = type-Pointed-Type E}
        { B = λ x → map-pointed-map g x ＝ point-Pointed-Type B}
        { s = point-Pointed-Type E , p}
        { t = point-Pointed-Type E , q}
        ( refl)
        ( α))
      ( refl)
      ( refl)
  dependent-identification-eq-pair-fiber-inclusion-Pointed-Type refl =
    refl

  preserves-point-equiv-fiber-inclusion-boundary-fiber-Pointed-Type :
    map-equiv equiv-fiber-inclusion-boundary-fiber-Pointed-Type refl ＝
    point-Pointed-Type
      ( fiber-Pointed-Type (inclusion-fiber-Pointed-Type g))
  preserves-point-equiv-fiber-inclusion-boundary-fiber-Pointed-Type =
    eq-pair-Σ
      ( eq-pair-Σ
        { A = type-Pointed-Type E}
        { B = λ x → map-pointed-map g x ＝ point-Pointed-Type B}
        { s =
          point-Pointed-Type E ,
          preserves-point-pointed-map g ∙ refl}
        { t = point-Pointed-Type E , preserves-point-pointed-map g}
        ( refl)
        ( right-unit))
      ( dependent-identification-eq-pair-fiber-inclusion-Pointed-Type
        ( right-unit))

  pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type :
    Ω B ≃∗ fiber-Pointed-Type (inclusion-fiber-Pointed-Type g)
  pr1 pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type =
    equiv-fiber-inclusion-boundary-fiber-Pointed-Type
  pr2 pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type =
    preserves-point-equiv-fiber-inclusion-boundary-fiber-Pointed-Type

  pointed-htpy-boundary-fiber-inclusion-boundary-fiber-Pointed-Type :
    connecting-map-Pointed-Type g ~∗
    ( inclusion-fiber-Pointed-Type (inclusion-fiber-Pointed-Type g) ∘∗
      pointed-map-pointed-equiv
        pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type)
  pr1 pointed-htpy-boundary-fiber-inclusion-boundary-fiber-Pointed-Type p =
    refl
  pr2 pointed-htpy-boundary-fiber-inclusion-boundary-fiber-Pointed-Type =
    ( inv
      ( ap-pr1-eq-pair-Σ
        ( eq-pair-Σ
          { A = type-Pointed-Type E}
          { B = λ x → map-pointed-map g x ＝ point-Pointed-Type B}
          { s =
            point-Pointed-Type E ,
            preserves-point-pointed-map g ∙ refl}
          { t = point-Pointed-Type E , preserves-point-pointed-map g}
          ( refl)
          ( right-unit))
        ( dependent-identification-eq-pair-fiber-inclusion-Pointed-Type
          ( right-unit)))) ∙
    ( inv right-unit)

  is-fiber-sequence-boundary-fiber-Pointed-Type :
    is-fiber-sequence-Pointed-Type
      ( connecting-map-Pointed-Type g)
      ( inclusion-fiber-Pointed-Type g)
  pr1 is-fiber-sequence-boundary-fiber-Pointed-Type =
    pointed-equiv-fiber-inclusion-boundary-fiber-Pointed-Type
  pr2 is-fiber-sequence-boundary-fiber-Pointed-Type =
    pointed-htpy-boundary-fiber-inclusion-boundary-fiber-Pointed-Type

  fiber-sequence-boundary-fiber-Pointed-Type :
    fiber-sequence-Pointed-Type l2 (l1 ⊔ l2) l1
  pr1 fiber-sequence-boundary-fiber-Pointed-Type =
    Ω B
  pr1 (pr2 fiber-sequence-boundary-fiber-Pointed-Type) =
    fiber-Pointed-Type g
  pr1 (pr2 (pr2 fiber-sequence-boundary-fiber-Pointed-Type)) =
    E
  pr1 (pr2 (pr2 (pr2 fiber-sequence-boundary-fiber-Pointed-Type))) =
    connecting-map-Pointed-Type g
  pr1 (pr2 (pr2 (pr2 (pr2 fiber-sequence-boundary-fiber-Pointed-Type)))) =
    inclusion-fiber-Pointed-Type g
  pr2 (pr2 (pr2 (pr2 (pr2 fiber-sequence-boundary-fiber-Pointed-Type)))) =
    is-fiber-sequence-boundary-fiber-Pointed-Type
```
