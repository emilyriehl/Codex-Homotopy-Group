# Diagonal stability for homotopy groups of spheres

```agda
module synthetic-homotopy-theory.stability-diagonal-homotopy-groups-spheres where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.connected-maps
open import foundation.identity-types
open import foundation.iterated-successors-truncation-levels
open import foundation.transport-along-identifications
open import foundation.truncation-levels
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.homotopy-automorphism-groups
open import group-theory.isomorphisms-groups

open import structured-types.pointed-types

open import synthetic-homotopy-theory.connected-maps-homotopy-groups
open import synthetic-homotopy-theory.connectedness-spheres
open import synthetic-homotopy-theory.freudenthal-suspension-theorem
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.reassociation-iterated-loop-spaces
open import synthetic-homotopy-theory.spheres
```

</details>

## Idea

Freudenthal says that the unit map `Sⁿ → ΩSⁿ⁺¹` is much more connected than
is needed on the diagonal. The only bookkeeping required is the reusable
truncation-level arithmetic translating the Freudenthal range into the range
needed by the concrete homotopy group functor.

## Lemmas

### Moving a successor through an iterated successor

```agda
preserves-succ-iterate-succ-𝕋 :
  (n : ℕ) (k : 𝕋) →
  iterate-succ-𝕋 n (succ-𝕋 k) ＝ succ-𝕋 (iterate-succ-𝕋 n k)
preserves-succ-iterate-succ-𝕋 zero-ℕ k = refl
preserves-succ-iterate-succ-𝕋 (succ-ℕ n) k =
  preserves-succ-iterate-succ-𝕋 n (succ-𝕋 k)
```

### The Freudenthal range dominates the diagonal range

```agda
compute-add+2-truncation-level-ℕ-diagonal-𝕋 :
  (n : ℕ) →
  add+2-𝕋 (truncation-level-ℕ n) (truncation-level-ℕ n) ＝
  iterate-succ-𝕋 n (iterate-succ-𝕋 (succ-ℕ (succ-ℕ n)) zero-𝕋)
compute-add+2-truncation-level-ℕ-diagonal-𝕋 zero-ℕ = refl
compute-add+2-truncation-level-ℕ-diagonal-𝕋 (succ-ℕ n) =
  ( ap
    ( succ-𝕋)
    ( left-successor-law-add+2-𝕋
      ( truncation-level-ℕ n)
      ( truncation-level-ℕ n))) ∙
  ( ap
    ( λ k → succ-𝕋 (succ-𝕋 k))
    ( compute-add+2-truncation-level-ℕ-diagonal-𝕋 n)) ∙
  ( ap
    ( succ-𝕋)
    ( inv
      ( preserves-succ-iterate-succ-𝕋
        ( n)
        ( iterate-succ-𝕋 (succ-ℕ (succ-ℕ n)) zero-𝕋)))) ∙
  ( inv
    ( preserves-succ-iterate-succ-𝕋
      ( n)
      ( succ-𝕋 (iterate-succ-𝕋 (succ-ℕ (succ-ℕ n)) zero-𝕋)))) ∙
  ( ap
    ( λ k → iterate-succ-𝕋 n (succ-𝕋 k))
    ( inv (reassociate-iterate-succ-𝕋 (succ-ℕ (succ-ℕ n)) zero-𝕋)))

is-connected-map-is-connected-map-freudenthal-diagonal-𝕋 :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (n : ℕ) →
  is-connected-map
    ( truncation-level-ℕ (freudenthal-connectivity-level-ℕ n))
    ( f) →
  is-connected-map
    ( iterate-succ-𝕋 (succ-ℕ (succ-ℕ n)) zero-𝕋)
    ( f)
is-connected-map-is-connected-map-freudenthal-diagonal-𝕋 n H =
  is-connected-map-is-connected-map-iterate-succ-𝕋
    ( n)
    ( iterate-succ-𝕋 (succ-ℕ (succ-ℕ n)) zero-𝕋)
    ( tr
      ( λ k → is-connected-map k _)
      ( ( compute-freudenthal-connectivity-level-add+2-𝕋 n) ∙
        ( compute-add+2-truncation-level-ℕ-diagonal-𝕋 n))
      ( H))
```

### Looping shifts concrete homotopy group presentations

```agda
eq-group-concrete-homotopy-group-loop :
  {l : Level} (n : ℕ) (A : Pointed-Type l) →
  group-Concrete-Group (concrete-homotopy-group n (Ω A)) ＝
  group-Concrete-Group (concrete-homotopy-group (succ-ℕ n) A)
eq-group-concrete-homotopy-group-loop n A =
  ap
    ( λ X → group-Concrete-Group (concrete-group-Pointed-Type X))
    ( inv-reassociate-succ-iterated-loop-space n A)
```

## Theorem

### Freudenthal gives diagonal stabilization for spheres

```agda
is-connected-map-Freudenthal-suspension-sphere-succ-succ :
  (n : ℕ) →
  is-connected-map
    ( iterate-succ-𝕋 (succ-ℕ (succ-ℕ n)) zero-𝕋)
    ( map-Freudenthal-suspension
      ( sphere-Pointed-Type (succ-ℕ (succ-ℕ n))))
is-connected-map-Freudenthal-suspension-sphere-succ-succ n =
  is-connected-map-is-connected-map-freudenthal-diagonal-𝕋
    ( n)
    ( is-connected-map-Freudenthal-suspension-Blakers-Massey
      ( n)
      ( sphere-Pointed-Type (succ-ℕ (succ-ℕ n)))
      ( is-connected-sphere-succ-succ n))

iso-stabilization-diagonal-homotopy-group-sphere-succ-succ :
  (n : ℕ) →
  iso-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group
        ( succ-ℕ n)
        ( sphere-Pointed-Type (succ-ℕ (succ-ℕ n)))))
    ( group-Concrete-Group
      ( concrete-homotopy-group
        ( succ-ℕ (succ-ℕ n))
        ( sphere-Pointed-Type (succ-ℕ (succ-ℕ (succ-ℕ n))))))
iso-stabilization-diagonal-homotopy-group-sphere-succ-succ n =
  tr
    ( λ K →
      iso-Group
        ( group-Concrete-Group
          ( concrete-homotopy-group
            ( succ-ℕ n)
            ( sphere-Pointed-Type (succ-ℕ (succ-ℕ n)))))
        ( K))
    ( eq-group-concrete-homotopy-group-loop
      ( succ-ℕ n)
      ( sphere-Pointed-Type (succ-ℕ (succ-ℕ (succ-ℕ n)))))
    ( iso-concrete-homotopy-group-is-connected-map
      ( succ-ℕ n)
      ( pointed-map-Freudenthal-suspension
        ( sphere-Pointed-Type (succ-ℕ (succ-ℕ n))))
      ( is-connected-map-Freudenthal-suspension-sphere-succ-succ n))
```
