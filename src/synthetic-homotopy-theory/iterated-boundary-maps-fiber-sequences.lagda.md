# Iterated boundary maps of fiber sequences

```agda
module synthetic-homotopy-theory.iterated-boundary-maps-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import structured-types.fiber-sequences
open import structured-types.fibers-of-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.whiskering-pointed-homotopies-composition

open import synthetic-homotopy-theory.connecting-fiber-sequences
open import synthetic-homotopy-theory.fibers-boundary-maps-pointed-maps
open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.iterated-loop-fiber-sequences
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.reassociation-iterated-loop-spaces
```

</details>

## Idea

The **iterated boundary maps** of a fiber sequence are the recursive looped
connecting maps and the fresh canonical connecting maps of the iterated loop
fiber sequences. Keeping both conventions named separately follows the
Coq-HoTT/Rocq `loops_les` pattern: the recursive map classifies the chosen
homotopy-group boundary homomorphism, while the fresh canonical map is the
natural source for shifted set-truncated exactness.

## Definitions

### Recursive and canonical boundary maps

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  boundary-pointed-map-fiber-sequence : Ω (base-fiber-sequence-Pointed-Type S) →∗
    fiber-fiber-sequence-Pointed-Type S
  boundary-pointed-map-fiber-sequence =
    connecting-map-fiber-sequence-Pointed-Type S

  pointed-map-iterated-boundary-fiber-sequence :
    (n : ℕ) →
    iterated-loop-space
      ( succ-ℕ n)
      ( base-fiber-sequence-Pointed-Type S) →∗
    iterated-loop-space
      ( n)
      ( fiber-fiber-sequence-Pointed-Type S)
  pointed-map-iterated-boundary-fiber-sequence zero-ℕ =
    boundary-pointed-map-fiber-sequence
  pointed-map-iterated-boundary-fiber-sequence (succ-ℕ n) =
    pointed-map-Ω (pointed-map-iterated-boundary-fiber-sequence n)

  reassociate-pointed-map-iterated-boundary-fiber-sequence :
    (n : ℕ) →
    tr
      (λ X → X →∗ iterated-loop-space n (fiber-fiber-sequence-Pointed-Type S))
      (reassociate-succ-iterated-loop-space n (base-fiber-sequence-Pointed-Type S))
      (pointed-map-iterated-boundary-fiber-sequence n) ＝
    pointed-map-iterated-loop-space n boundary-pointed-map-fiber-sequence
  reassociate-pointed-map-iterated-boundary-fiber-sequence zero-ℕ = refl
  reassociate-pointed-map-iterated-boundary-fiber-sequence (succ-ℕ n) =
    tr-pointed-map-Ω
      (reassociate-succ-iterated-loop-space n (base-fiber-sequence-Pointed-Type S))
      (refl)
      (pointed-map-iterated-boundary-fiber-sequence n) ∙
    ap pointed-map-Ω
      (reassociate-pointed-map-iterated-boundary-fiber-sequence n)

  reassociate-Ω-pointed-map-iterated-boundary-fiber-sequence :
    (n : ℕ) →
    tr
      (λ X → X →∗ Ω (iterated-loop-space n (fiber-fiber-sequence-Pointed-Type S)))
      (reassociate-Ω-succ-iterated-loop-space n (base-fiber-sequence-Pointed-Type S))
      (pointed-map-Ω (pointed-map-iterated-boundary-fiber-sequence n)) ＝
    pointed-map-Ω
      (pointed-map-iterated-loop-space n boundary-pointed-map-fiber-sequence)
  reassociate-Ω-pointed-map-iterated-boundary-fiber-sequence n =
    tr-pointed-map-Ω
      (reassociate-succ-iterated-loop-space n (base-fiber-sequence-Pointed-Type S))
      (refl)
      (pointed-map-iterated-boundary-fiber-sequence n) ∙
    ap pointed-map-Ω
      (reassociate-pointed-map-iterated-boundary-fiber-sequence n)

  canonical-pointed-map-iterated-boundary-fiber-sequence :
    (n : ℕ) →
    iterated-loop-space
      ( succ-ℕ n)
      ( base-fiber-sequence-Pointed-Type S) →∗
    iterated-loop-space
      ( n)
      ( fiber-fiber-sequence-Pointed-Type S)
  canonical-pointed-map-iterated-boundary-fiber-sequence n =
    pointed-map-inv-pointed-equiv
      ( pointed-equiv-iterated-loop-fiber-fiber-sequence S n) ∘∗
    boundary-fiber-Pointed-Type
      ( pointed-map-iterated-loop-space
        ( n)
        ( fibration-fiber-sequence-Pointed-Type S))

  canonical-pointed-map-iterated-loop-boundary-fiber-sequence :
    (n : ℕ) →
    Ω
      ( iterated-loop-space
        ( succ-ℕ n)
        ( base-fiber-sequence-Pointed-Type S)) →∗
    Ω
      ( iterated-loop-space
        ( n)
        ( fiber-fiber-sequence-Pointed-Type S))
  canonical-pointed-map-iterated-loop-boundary-fiber-sequence n =
    pointed-map-inv-pointed-equiv
      ( pointed-equiv-fiber-fiber-sequence-Pointed-Type
        ( iterated-loop-fiber-sequence S (succ-ℕ n))) ∘∗
    boundary-fiber-Pointed-Type
      ( fibration-fiber-sequence-Pointed-Type
        ( iterated-loop-fiber-sequence S (succ-ℕ n)))

  loop-canonical-pointed-map-iterated-boundary-fiber-sequence :
    (n : ℕ) →
    Ω
      ( iterated-loop-space
        ( succ-ℕ n)
        ( base-fiber-sequence-Pointed-Type S)) →∗
    Ω
      ( iterated-loop-space
        ( n)
        ( fiber-fiber-sequence-Pointed-Type S))
  loop-canonical-pointed-map-iterated-boundary-fiber-sequence n =
    pointed-map-Ω
      ( canonical-pointed-map-iterated-boundary-fiber-sequence n)

  equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type :
    type-Pointed-Type
      ( fiber-Pointed-Type
        ( boundary-fiber-Pointed-Type
          ( fibration-fiber-sequence-Pointed-Type S))) ≃
    type-Pointed-Type (fiber-Pointed-Type boundary-pointed-map-fiber-sequence)
  equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type =
    equiv-tot
      ( λ q →
        ( equiv-concat'
          ( map-pointed-map boundary-pointed-map-fiber-sequence q)
          ( preserves-point-map-inv-pointed-equiv
            ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))) ∘e
        ( equiv-ap
          ( equiv-inv-pointed-equiv
            ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S))
          ( map-pointed-map
            ( boundary-fiber-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S))
            ( q))
          ( point-Pointed-Type
            ( fiber-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S)))))

  preserves-point-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type :
    map-equiv
      ( equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type)
      ( point-Pointed-Type
        ( fiber-Pointed-Type
          ( boundary-fiber-Pointed-Type
            ( fibration-fiber-sequence-Pointed-Type S)))) ＝
    point-Pointed-Type (fiber-Pointed-Type boundary-pointed-map-fiber-sequence)
  preserves-point-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type =
    refl

  pointed-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type :
    fiber-Pointed-Type
      ( boundary-fiber-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S)) ≃∗
    fiber-Pointed-Type boundary-pointed-map-fiber-sequence
  pr1 pointed-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type =
    equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type
  pr2 pointed-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type =
    preserves-point-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type

  pointed-htpy-inclusion-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type :
    inclusion-fiber-Pointed-Type
      ( boundary-fiber-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S)) ~∗
    ( inclusion-fiber-Pointed-Type boundary-pointed-map-fiber-sequence ∘∗
      pointed-map-pointed-equiv
        pointed-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type)
  pr1 pointed-htpy-inclusion-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type u =
    refl
  pr2 pointed-htpy-inclusion-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type =
    refl

  equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type :
    type-Ω (total-space-fiber-sequence-Pointed-Type S) ≃
    type-Pointed-Type (fiber-Pointed-Type boundary-pointed-map-fiber-sequence)
  equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type =
    equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type ∘e
    equiv-fiber-boundary-map-Ω-direct-Pointed-Type
      ( fibration-fiber-sequence-Pointed-Type S)

  htpy-inclusion-fiber-boundary-fiber-sequence-direct-Pointed-Type :
    (p : type-Ω (total-space-fiber-sequence-Pointed-Type S)) →
    map-Ω (fibration-fiber-sequence-Pointed-Type S) p ＝
    map-pointed-map
      ( inclusion-fiber-Pointed-Type boundary-pointed-map-fiber-sequence)
      ( map-equiv equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type p)
  htpy-inclusion-fiber-boundary-fiber-sequence-direct-Pointed-Type p =
    refl

  preserves-point-equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type :
    map-equiv equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type refl ＝
    point-Pointed-Type (fiber-Pointed-Type boundary-pointed-map-fiber-sequence)
  preserves-point-equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type =
    ( ap
      ( map-equiv
        equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type)
      ( preserves-point-equiv-fiber-boundary-map-Ω-direct-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))) ∙
    preserves-point-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type

  pointed-equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type :
    Ω (total-space-fiber-sequence-Pointed-Type S) ≃∗
    fiber-Pointed-Type boundary-pointed-map-fiber-sequence
  pointed-equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type =
    comp-pointed-equiv
      ( pointed-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type)
      ( pointed-equiv-fiber-boundary-map-Ω-direct-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))

  pointed-htpy-inclusion-fiber-boundary-fiber-sequence-direct-Pointed-Type :
    pointed-map-Ω (fibration-fiber-sequence-Pointed-Type S) ~∗
    ( inclusion-fiber-Pointed-Type boundary-pointed-map-fiber-sequence ∘∗
      pointed-map-pointed-equiv
        pointed-equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type)
  pointed-htpy-inclusion-fiber-boundary-fiber-sequence-direct-Pointed-Type =
    concat-pointed-htpy
      ( pointed-htpy-inclusion-fiber-boundary-map-Ω-direct-Pointed-Type
        ( fibration-fiber-sequence-Pointed-Type S))
      ( concat-pointed-htpy
        ( right-whisker-comp-pointed-htpy
          ( inclusion-fiber-Pointed-Type
            ( boundary-fiber-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S)))
          ( inclusion-fiber-Pointed-Type boundary-pointed-map-fiber-sequence ∘∗
            pointed-map-pointed-equiv
              pointed-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type)
          ( pointed-htpy-inclusion-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type)
          ( pointed-map-pointed-equiv
            ( pointed-equiv-fiber-boundary-map-Ω-direct-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S))))
        ( associative-comp-pointed-map
          ( inclusion-fiber-Pointed-Type boundary-pointed-map-fiber-sequence)
          ( pointed-map-pointed-equiv
            pointed-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type)
          ( pointed-map-pointed-equiv
            ( pointed-equiv-fiber-boundary-map-Ω-direct-Pointed-Type
              ( fibration-fiber-sequence-Pointed-Type S)))))

  is-fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type :
    is-fiber-sequence-Pointed-Type
      ( pointed-map-Ω (fibration-fiber-sequence-Pointed-Type S))
      ( boundary-pointed-map-fiber-sequence)
  pr1 is-fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type =
    pointed-equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type
  pr2 is-fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type =
    pointed-htpy-inclusion-fiber-boundary-fiber-sequence-direct-Pointed-Type

  fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type :
    fiber-sequence-Pointed-Type l2 l3 l1
  pr1 fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type =
    Ω (total-space-fiber-sequence-Pointed-Type S)
  pr1 (pr2 fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type) =
    Ω (base-fiber-sequence-Pointed-Type S)
  pr1 (pr2 (pr2 fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type)) =
    fiber-fiber-sequence-Pointed-Type S
  pr1 (pr2 (pr2 (pr2 fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type))) =
    pointed-map-Ω (fibration-fiber-sequence-Pointed-Type S)
  pr1 (pr2 (pr2 (pr2 (pr2 fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type)))) =
    boundary-pointed-map-fiber-sequence
  pr2 (pr2 (pr2 (pr2 (pr2 fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type)))) =
    is-fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type

```
