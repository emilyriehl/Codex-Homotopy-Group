# Set-truncated direct iterated exactness of homotopy groups of fiber sequences

```agda
module synthetic-homotopy-theory.set-truncated-direct-iterated-exactness-homotopy-groups-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.set-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import structured-types.exact-sequences-pointed-sets
open import structured-types.fiber-sequences
open import structured-types.pointed-maps

open import synthetic-homotopy-theory.connecting-fiber-sequences
open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.iterated-boundary-maps-fiber-sequences
open import synthetic-homotopy-theory.iterated-loop-fiber-sequences
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.reassociation-iterated-loop-spaces
open import synthetic-homotopy-theory.set-truncated-exactness-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.set-truncated-iterated-maps-homotopy-groups-fiber-sequences
```

</details>

## Idea

The **direct set-truncated iterated exactness statements** are the
compatibility theorems obtained from the structural connecting fiber sequence.
They first state exactness in the natural `Omega^n(Omega X)` indexing and then
transport it to the public shifted `Omega^(n+1) X` indexing by reassociation.

The historical `direct` names are retained as aliases for this structural
connecting-map route.

## Theorems

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  is-exact-set-truncation-iterated-loop-connecting-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( Ω (total-space-fiber-sequence-Pointed-Type S)))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( Ω (base-fiber-sequence-Pointed-Type S)))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-connecting-fibration-fiber-sequence S n)
      ( hom-trunc-iterated-loop-connecting-map-fiber-sequence S n)
  is-exact-set-truncation-iterated-loop-connecting-fiber-sequence
    zero-ℕ =
    is-exact-set-truncation-loop-fiber-sequence
      ( fiber-sequence-connecting-map-fiber-sequence-Pointed-Type S)
  is-exact-set-truncation-iterated-loop-connecting-fiber-sequence
    ( succ-ℕ n) =
    is-exact-set-truncation-loop-fiber-sequence
      ( iterated-loop-fiber-sequence
        ( fiber-sequence-connecting-map-fiber-sequence-Pointed-Type S)
        ( succ-ℕ n))

  is-exact-set-truncation-direct-iterated-loop-fibration-boundary-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( Ω (total-space-fiber-sequence-Pointed-Type S)))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( Ω (base-fiber-sequence-Pointed-Type S)))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-direct-iterated-loop-fibration-fiber-sequence S n)
      ( hom-trunc-direct-iterated-loop-boundary-fiber-sequence S n)
  is-exact-set-truncation-direct-iterated-loop-fibration-boundary-fiber-sequence =
    is-exact-set-truncation-iterated-loop-connecting-fiber-sequence

  eq-tr-hom-trunc-reassociate-iterated-loop-fibration-fiber-sequence :
    (n : ℕ) →
    tr
      (λ X →
        hom-Pointed-Set X
          ( trunc-Pointed-Set
            ( Ω
              ( iterated-loop-space
                ( n)
                ( Ω (base-fiber-sequence-Pointed-Type S))))))
      ( ap
        ( trunc-Pointed-Set)
        ( reassociate-Ω-succ-iterated-loop-space
          ( n)
          ( total-space-fiber-sequence-Pointed-Type S)))
      ( tr
        (λ Y →
          hom-Pointed-Set
            ( trunc-Pointed-Set
              ( Ω
                ( iterated-loop-space
                  ( succ-ℕ n)
                  ( total-space-fiber-sequence-Pointed-Type S))))
            ( Y))
        ( ap
          ( trunc-Pointed-Set)
          ( reassociate-Ω-succ-iterated-loop-space
            ( n)
            ( base-fiber-sequence-Pointed-Type S)))
        ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))) ＝
    hom-trunc-direct-iterated-loop-fibration-fiber-sequence S n
  eq-tr-hom-trunc-reassociate-iterated-loop-fibration-fiber-sequence n =
    tr-hom-trunc-Pointed-Set
      ( reassociate-Ω-succ-iterated-loop-space
        ( n)
        ( total-space-fiber-sequence-Pointed-Type S))
      ( reassociate-Ω-succ-iterated-loop-space
        ( n)
        ( base-fiber-sequence-Pointed-Type S))
      ( pointed-map-Ω
        ( pointed-map-iterated-loop-space
          ( succ-ℕ n)
          ( fibration-fiber-sequence-Pointed-Type S))) ∙
    ap
      ( hom-trunc-Pointed-Set)
      ( reassociate-Ω-pointed-map-iterated-loop-space
        ( n)
        ( fibration-fiber-sequence-Pointed-Type S))

  eq-tr-hom-trunc-reassociate-iterated-loop-boundary-fiber-sequence :
    (n : ℕ) →
    tr
      (λ X →
        hom-Pointed-Set X
          ( trunc-Pointed-Set
            ( Ω
              ( iterated-loop-space
                ( n)
                ( fiber-fiber-sequence-Pointed-Type S)))))
      ( ap
        ( trunc-Pointed-Set)
        ( reassociate-Ω-succ-iterated-loop-space
          ( n)
          ( base-fiber-sequence-Pointed-Type S)))
      ( tr
        (λ Y →
          hom-Pointed-Set
            ( trunc-Pointed-Set
              ( Ω
                ( iterated-loop-space
                  ( succ-ℕ n)
                  ( base-fiber-sequence-Pointed-Type S))))
            ( Y))
        ( refl
          { x =
            trunc-Pointed-Set
              ( Ω
                ( iterated-loop-space
                  ( n)
                  ( fiber-fiber-sequence-Pointed-Type S)))})
        ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)) ＝
    hom-trunc-direct-iterated-loop-boundary-fiber-sequence S n
  eq-tr-hom-trunc-reassociate-iterated-loop-boundary-fiber-sequence n =
    tr-hom-trunc-Pointed-Set
      ( reassociate-Ω-succ-iterated-loop-space
        ( n)
        ( base-fiber-sequence-Pointed-Type S))
      ( refl
        { x =
          Ω
            ( iterated-loop-space
              ( n)
              ( fiber-fiber-sequence-Pointed-Type S))})
      ( pointed-map-Ω (pointed-map-iterated-boundary-fiber-sequence S n)) ∙
    ap
      ( hom-trunc-Pointed-Set)
      ( reassociate-Ω-pointed-map-iterated-boundary-fiber-sequence S n)

  is-exact-set-truncation-iterated-loop-fibration-connecting-map-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)
  is-exact-set-truncation-iterated-loop-fibration-connecting-map-fiber-sequence n =
    is-exact-hom-Pointed-Set-tr
      ( ap
        ( trunc-Pointed-Set)
        ( reassociate-Ω-succ-iterated-loop-space
          ( n)
          ( total-space-fiber-sequence-Pointed-Type S)))
      ( ap
        ( trunc-Pointed-Set)
        ( reassociate-Ω-succ-iterated-loop-space
          ( n)
          ( base-fiber-sequence-Pointed-Type S)))
      ( refl
        { x =
          trunc-Pointed-Set
            ( Ω
              ( iterated-loop-space
                ( n)
                ( fiber-fiber-sequence-Pointed-Type S)))})
      ( hom-trunc-direct-iterated-loop-fibration-fiber-sequence S n)
      ( hom-trunc-direct-iterated-loop-boundary-fiber-sequence S n)
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)
      ( eq-tr-hom-trunc-reassociate-iterated-loop-fibration-fiber-sequence n)
      ( eq-tr-hom-trunc-reassociate-iterated-loop-boundary-fiber-sequence n)
      ( is-exact-set-truncation-direct-iterated-loop-fibration-boundary-fiber-sequence n)

  is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-direct :
    (n : ℕ) →
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)
  is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-direct =
    is-exact-set-truncation-iterated-loop-fibration-connecting-map-fiber-sequence

  is-exact-set-truncation-first-iterated-loop-fibration-boundary-fiber-sequence-direct :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( 1)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( 1)
            ( base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( 0)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S 1)
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S 0)
  is-exact-set-truncation-first-iterated-loop-fibration-boundary-fiber-sequence-direct =
    is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-direct
      ( 0)

  is-exact-set-truncation-second-iterated-loop-fibration-boundary-fiber-sequence-direct :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( 2)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( 2)
            ( base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( 1)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S 2)
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S 1)
  is-exact-set-truncation-second-iterated-loop-fibration-boundary-fiber-sequence-direct =
    is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-direct
      ( 1)
```
