# Connected maps and homotopy groups

```agda
module synthetic-homotopy-theory.connected-maps-homotopy-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.connected-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.iterated-successors-truncation-levels
open import foundation.transport-along-identifications
open import foundation.truncation-equivalences
open import foundation.truncation-levels
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.homomorphisms-concrete-groups
open import group-theory.homomorphisms-groups
open import group-theory.isomorphisms-groups

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.connected-maps-loop-spaces
open import synthetic-homotopy-theory.functoriality-homotopy-groups
open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.isomorphisms-homotopy-groups
open import synthetic-homotopy-theory.underlying-maps-concrete-homotopy-groups
```

</details>

## Idea

Looping a connected pointed map lowers its connectivity by one. Iterating this
observation gives a reusable criterion for a pointed map to induce an
isomorphism on concrete homotopy groups.

## Theorem

### Iterated loop maps lower connectivity iteratively

```agda
is-connected-map-iterated-loop-space :
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (f : A →∗ B) (n : ℕ) (k : 𝕋) →
  is-connected-map (iterate-succ-𝕋 n k) (map-pointed-map f) →
  is-connected-map k
    ( map-pointed-map (pointed-map-iterated-loop-space n f))
is-connected-map-iterated-loop-space f zero-ℕ k H = H
is-connected-map-iterated-loop-space f (succ-ℕ n) k H =
  is-connected-map-map-Ω
    ( k)
    ( pointed-map-iterated-loop-space n f)
    ( is-connected-map-iterated-loop-space f n (succ-𝕋 k) H)

is-connected-map-is-connected-map-iterate-succ-𝕋 :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (n : ℕ) (k : 𝕋) →
  is-connected-map (iterate-succ-𝕋 n k) f → is-connected-map k f
is-connected-map-is-connected-map-iterate-succ-𝕋 zero-ℕ k H = H
is-connected-map-is-connected-map-iterate-succ-𝕋 (succ-ℕ n) k H =
  is-connected-map-is-connected-map-iterate-succ-𝕋 n k
    ( is-connected-map-is-connected-map-succ-𝕋
      ( iterate-succ-𝕋 n k)
      ( tr
        ( λ r → is-connected-map r _)
        ( reassociate-iterate-succ-𝕋 n k)
        ( H)))
```

### Connected pointed maps induce homotopy group isomorphisms

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (n : ℕ) (f : A →∗ B)
  where

  is-equiv-map-set-trunc-loop-map-concrete-homotopy-group-is-connected-map :
    is-connected-map
      ( iterate-succ-𝕋 (succ-ℕ n) zero-𝕋)
      ( map-pointed-map f) →
    is-equiv (map-set-trunc-loop-map-concrete-homotopy-group n f)
  is-equiv-map-set-trunc-loop-map-concrete-homotopy-group-is-connected-map H =
    is-truncation-equivalence-is-connected-map
      ( map-pointed-map (pointed-map-iterated-loop-space (succ-ℕ n) f))
      ( is-connected-map-iterated-loop-space
        ( f)
        ( succ-ℕ n)
        ( zero-𝕋)
        ( H))

  is-equiv-hom-group-concrete-homotopy-group-is-connected-map :
    is-connected-map
      ( iterate-succ-𝕋 (succ-ℕ n) zero-𝕋)
      ( map-pointed-map f) →
    is-equiv-hom-Group
      ( group-Concrete-Group (concrete-homotopy-group n A))
      ( group-Concrete-Group (concrete-homotopy-group n B))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group n A)
        ( concrete-homotopy-group n B)
        ( hom-concrete-homotopy-group n f))
  is-equiv-hom-group-concrete-homotopy-group-is-connected-map H =
    is-equiv-map-underlying-hom-concrete-homotopy-group-is-equiv-map-set-trunc-loop-map
      ( n)
      ( f)
      ( is-equiv-map-set-trunc-loop-map-concrete-homotopy-group-is-connected-map
        ( H))

  is-iso-hom-group-concrete-homotopy-group-is-connected-map :
    is-connected-map
      ( iterate-succ-𝕋 (succ-ℕ n) zero-𝕋)
      ( map-pointed-map f) →
    is-iso-Group
      ( group-Concrete-Group (concrete-homotopy-group n A))
      ( group-Concrete-Group (concrete-homotopy-group n B))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group n A)
        ( concrete-homotopy-group n B)
        ( hom-concrete-homotopy-group n f))
  is-iso-hom-group-concrete-homotopy-group-is-connected-map H =
    is-iso-is-equiv-hom-Group
      ( group-Concrete-Group (concrete-homotopy-group n A))
      ( group-Concrete-Group (concrete-homotopy-group n B))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group n A)
        ( concrete-homotopy-group n B)
        ( hom-concrete-homotopy-group n f))
      ( is-equiv-hom-group-concrete-homotopy-group-is-connected-map H)

  iso-concrete-homotopy-group-is-connected-map :
    is-connected-map
      ( iterate-succ-𝕋 (succ-ℕ n) zero-𝕋)
      ( map-pointed-map f) →
    iso-Group
      ( group-Concrete-Group (concrete-homotopy-group n A))
      ( group-Concrete-Group (concrete-homotopy-group n B))
  pr1 (iso-concrete-homotopy-group-is-connected-map H) =
    hom-group-hom-Concrete-Group
      ( concrete-homotopy-group n A)
      ( concrete-homotopy-group n B)
      ( hom-concrete-homotopy-group n f)
  pr2 (iso-concrete-homotopy-group-is-connected-map H) =
    is-iso-hom-group-concrete-homotopy-group-is-connected-map H
```
