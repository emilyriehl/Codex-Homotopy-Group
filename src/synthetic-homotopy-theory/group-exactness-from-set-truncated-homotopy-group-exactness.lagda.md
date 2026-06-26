# Group exactness from set-truncated homotopy-group exactness

```agda
module synthetic-homotopy-theory.group-exactness-from-set-truncated-homotopy-group-exactness where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-contractible-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositional-truncations
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.exact-sequences-groups
open import group-theory.functoriality-homotopy-automorphism-groups
open import group-theory.groups
open import group-theory.homotopy-automorphism-groups
open import group-theory.homomorphisms-concrete-groups
open import group-theory.homomorphisms-groups
open import group-theory.images-of-group-homomorphisms
open import group-theory.kernels-homomorphisms-groups

open import structured-types.exact-sequences-pointed-sets
open import structured-types.fiber-sequences
open import structured-types.pointed-maps
open import structured-types.pointed-sets
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.long-exact-sequence-homotopy-groups
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.set-truncated-iterated-exactness-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.underlying-groups-concrete-homotopy-groups
open import synthetic-homotopy-theory.underlying-maps-concrete-homotopy-groups
```

</details>

## Idea

The set-truncated long exact sequence gives exactness for pointed sets built
from loop spaces. The final Hopf comparison needs exactness for the ordinary
groups underlying concrete homotopy groups. This file isolates that transport
step, keeping it separate from the construction of the set-level exactness
statements.

The missing proof will use the underlying-type equivalences for concrete
homotopy groups and the naturality squares for the induced maps to transport
image and kernel membership between the two exactness formulations.

## Theorems

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Pointed-Set l1) (B : Pointed-Set l2) (C : Pointed-Set l3)
  (G : Group l4) (H : Group l5) (K : Group l6)
  (f-set : hom-Pointed-Set A B) (g-set : hom-Pointed-Set B C)
  (f-group : hom-Group G H) (g-group : hom-Group H K)
  (eA : type-Group G → type-Pointed-Set A)
  (dA : type-Pointed-Set A → type-Group G)
  (eB : type-Group H → type-Pointed-Set B)
  (eC : type-Group K → type-Pointed-Set C)
  (is-injective-eB : is-injective eB)
  (is-injective-eC : is-injective eC)
  (is-section-dA : (x : type-Pointed-Set A) → eA (dA x) ＝ x)
  (preserves-unit-eC : eC (unit-Group K) ＝ point-Pointed-Set C)
  (coherence-f :
    (x : type-Group G) →
    eB (map-hom-Group G H f-group x) ＝
    map-pointed-map f-set (eA x))
  (coherence-g :
    (x : type-Group H) →
    eC (map-hom-Group H K g-group x) ＝
    map-pointed-map g-set (eB x))
  where

  is-exact-hom-Group-is-exact-hom-Pointed-Set :
    is-exact-hom-Pointed-Set A B C f-set g-set →
    is-exact-hom-Group G H K f-group g-group
  pr1 (is-exact-hom-Group-is-exact-hom-Pointed-Set E y) I =
    apply-universal-property-trunc-Prop I
      ( subset-kernel-hom-Group H K g-group y)
      ( λ where
        (x , p) →
          inv
            ( is-injective-eC
              ( ( coherence-g y) ∙
                ( is-in-kernel-mere-preimage-is-exact-hom-Pointed-Set
                  ( A)
                  ( B)
                  ( C)
                  ( f-set)
                  ( g-set)
                  ( E)
                  ( eB y)
                  ( unit-trunc-Prop
                    ( eA x ,
                      ( inv (coherence-f x)) ∙
                      ( ap eB p)))) ∙
                ( inv preserves-unit-eC))))
  pr2 (is-exact-hom-Group-is-exact-hom-Pointed-Set E y) K' =
    apply-universal-property-trunc-Prop
      ( mere-preimage-is-in-kernel-is-exact-hom-Pointed-Set
        ( A)
        ( B)
        ( C)
        ( f-set)
        ( g-set)
        ( E)
        ( eB y)
        ( ( inv (coherence-g y)) ∙
          ( inv (ap eC K')) ∙
          ( preserves-unit-eC)))
      ( subset-image-hom-Group G H f-group y)
      ( λ where
        (x , p) →
          unit-trunc-Prop
            ( dA x ,
              is-injective-eB
                ( ( coherence-f (dA x)) ∙
                  ( ap (map-pointed-map f-set) (is-section-dA x)) ∙
                  ( p))))

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Pointed-Set l1) (B : Pointed-Set l2) (C : Pointed-Set l3)
  (G : Group l4) (H : Group l5) (K : Group l6)
  (f-set : hom-Pointed-Set A B) (g-set : hom-Pointed-Set B C)
  (f-group : hom-Group G H) (g-group : hom-Group H K)
  (eA : type-Group G → type-Pointed-Set A)
  (dA : type-Pointed-Set A → type-Group G)
  (eB : type-Group H → type-Pointed-Set B)
  (is-injective-eB : is-injective eB)
  (is-section-dA : (x : type-Pointed-Set A) → eA (dA x) ＝ x)
  (is-contr-K : is-contr (type-Group K))
  (is-contr-C : is-contr (type-Pointed-Set C))
  (coherence-f :
    (x : type-Group G) →
    eB (map-hom-Group G H f-group x) ＝
    map-pointed-map f-set (eA x))
  where

  is-exact-hom-Group-is-exact-hom-Pointed-Set-is-trivial-codomain :
    is-exact-hom-Pointed-Set A B C f-set g-set →
    is-exact-hom-Group G H K f-group g-group
  pr1
    ( is-exact-hom-Group-is-exact-hom-Pointed-Set-is-trivial-codomain E y)
    I =
    eq-is-contr is-contr-K
  pr2
    ( is-exact-hom-Group-is-exact-hom-Pointed-Set-is-trivial-codomain E y)
    K' =
    apply-universal-property-trunc-Prop
      ( mere-preimage-is-in-kernel-is-exact-hom-Pointed-Set
        ( A)
        ( B)
        ( C)
        ( f-set)
        ( g-set)
        ( E)
        ( eB y)
        ( eq-is-contr is-contr-C))
      ( subset-image-hom-Group G H f-group y)
      ( λ where
        (x , p) →
          unit-trunc-Prop
            ( dA x ,
              is-injective-eB
                ( ( coherence-f (dA x)) ∙
                  ( ap (map-pointed-map f-set) (is-section-dA x)) ∙
                  ( p))))

module _
  {l1 l2 l3 : Level}
  (A : Pointed-Type l1) (B : Pointed-Type l2) (C : Pointed-Type l3)
  (f : A →∗ B) (g : B →∗ C)
  where

  is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (Ω A))
      ( trunc-Pointed-Set (Ω B))
      ( trunc-Pointed-Set (Ω C))
      ( hom-trunc-Pointed-Set (pointed-map-Ω f))
      ( hom-trunc-Pointed-Set (pointed-map-Ω g)) →
    is-exact-hom-Group
      ( group-Concrete-Group (concrete-group-Pointed-Type A))
      ( group-Concrete-Group (concrete-group-Pointed-Type B))
      ( group-Concrete-Group (concrete-group-Pointed-Type C))
      ( hom-group-hom-Concrete-Group
        ( concrete-group-Pointed-Type A)
        ( concrete-group-Pointed-Type B)
        ( hom-concrete-group-Pointed-Type f))
      ( hom-group-hom-Concrete-Group
        ( concrete-group-Pointed-Type B)
        ( concrete-group-Pointed-Type C)
        ( hom-concrete-group-Pointed-Type g))
  is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type =
    is-exact-hom-Group-is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (Ω A))
      ( trunc-Pointed-Set (Ω B))
      ( trunc-Pointed-Set (Ω C))
      ( group-Concrete-Group (concrete-group-Pointed-Type A))
      ( group-Concrete-Group (concrete-group-Pointed-Type B))
      ( group-Concrete-Group (concrete-group-Pointed-Type C))
      ( hom-trunc-Pointed-Set (pointed-map-Ω f))
      ( hom-trunc-Pointed-Set (pointed-map-Ω g))
      ( hom-group-hom-Concrete-Group
        ( concrete-group-Pointed-Type A)
        ( concrete-group-Pointed-Type B)
        ( hom-concrete-group-Pointed-Type f))
      ( hom-group-hom-Concrete-Group
        ( concrete-group-Pointed-Type B)
        ( concrete-group-Pointed-Type C)
        ( hom-concrete-group-Pointed-Type g))
      ( map-underlying-type-concrete-group-Pointed-Type A)
      ( map-inv-underlying-type-concrete-group-Pointed-Type A)
      ( map-underlying-type-concrete-group-Pointed-Type B)
      ( map-underlying-type-concrete-group-Pointed-Type C)
      ( is-injective-equiv
        ( equiv-underlying-type-concrete-group-Pointed-Type B))
      ( is-injective-equiv
        ( equiv-underlying-type-concrete-group-Pointed-Type C))
      ( is-section-map-inv-underlying-type-concrete-group-Pointed-Type A)
      ( preserves-unit-map-underlying-type-concrete-group-Pointed-Type C)
      ( naturality-map-underlying-type-concrete-group-Pointed-Type f)
      ( naturality-map-underlying-type-concrete-group-Pointed-Type g)

  is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type-is-trivial-codomain :
    (g-set :
      hom-Pointed-Set
        ( trunc-Pointed-Set (Ω B))
        ( trunc-Pointed-Set (Ω C))) →
    (g-group :
      hom-Group
        ( group-Concrete-Group (concrete-group-Pointed-Type B))
        ( group-Concrete-Group (concrete-group-Pointed-Type C))) →
    is-contr
      ( type-Group
        ( group-Concrete-Group (concrete-group-Pointed-Type C))) →
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (Ω A))
      ( trunc-Pointed-Set (Ω B))
      ( trunc-Pointed-Set (Ω C))
      ( hom-trunc-Pointed-Set (pointed-map-Ω f))
      ( g-set) →
    is-exact-hom-Group
      ( group-Concrete-Group (concrete-group-Pointed-Type A))
      ( group-Concrete-Group (concrete-group-Pointed-Type B))
      ( group-Concrete-Group (concrete-group-Pointed-Type C))
      ( hom-group-hom-Concrete-Group
        ( concrete-group-Pointed-Type A)
        ( concrete-group-Pointed-Type B)
        ( hom-concrete-group-Pointed-Type f))
      ( g-group)
  is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type-is-trivial-codomain
    g-set g-group is-contr-target =
    is-exact-hom-Group-is-exact-hom-Pointed-Set-is-trivial-codomain
      ( trunc-Pointed-Set (Ω A))
      ( trunc-Pointed-Set (Ω B))
      ( trunc-Pointed-Set (Ω C))
      ( group-Concrete-Group (concrete-group-Pointed-Type A))
      ( group-Concrete-Group (concrete-group-Pointed-Type B))
      ( group-Concrete-Group (concrete-group-Pointed-Type C))
      ( hom-trunc-Pointed-Set (pointed-map-Ω f))
      ( g-set)
      ( hom-group-hom-Concrete-Group
        ( concrete-group-Pointed-Type A)
        ( concrete-group-Pointed-Type B)
        ( hom-concrete-group-Pointed-Type f))
      ( g-group)
      ( map-underlying-type-concrete-group-Pointed-Type A)
      ( map-inv-underlying-type-concrete-group-Pointed-Type A)
      ( map-underlying-type-concrete-group-Pointed-Type B)
      ( is-injective-equiv
        ( equiv-underlying-type-concrete-group-Pointed-Type B))
      ( is-section-map-inv-underlying-type-concrete-group-Pointed-Type A)
      ( is-contr-target)
      ( is-contr-equiv'
        ( type-Concrete-Group (concrete-group-Pointed-Type C))
        ( equiv-underlying-type-concrete-group-Pointed-Type C)
        ( is-contr-target))
      ( naturality-map-underlying-type-concrete-group-Pointed-Type f)

module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  is-exact-hom-Group-is-exact-set-truncation-iterated-loop-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( base-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-fiber-inclusion-fiber-sequence S n)
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S n) →
    is-exact-hom-Group
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S)))
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( n)
          ( total-space-fiber-sequence-Pointed-Type S)))
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( n)
          ( base-fiber-sequence-Pointed-Type S)))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( n)
          ( total-space-fiber-sequence-Pointed-Type S))
        ( hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence S n))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( n)
          ( total-space-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( n)
          ( base-fiber-sequence-Pointed-Type S))
        ( hom-fibration-concrete-homotopy-group-fiber-sequence S n))
  is-exact-hom-Group-is-exact-set-truncation-iterated-loop-fiber-sequence n =
    is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type
      ( iterated-loop-space
        ( n)
        ( fiber-fiber-sequence-Pointed-Type S))
      ( iterated-loop-space
        ( n)
        ( total-space-fiber-sequence-Pointed-Type S))
      ( iterated-loop-space
        ( n)
        ( base-fiber-sequence-Pointed-Type S))
      ( pointed-map-iterated-loop-space
        ( n)
        ( fiber-inclusion-fiber-sequence-Pointed-Type S))
      ( pointed-map-iterated-loop-space
        ( n)
        ( fibration-fiber-sequence-Pointed-Type S))

  is-exact-hom-Group-is-exact-set-truncation-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Pointed-Set
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
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence
        ( S)
        ( n))
      ( hom-trunc-iterated-loop-fiber-inclusion-fiber-sequence S n) →
    is-exact-hom-Group
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( succ-ℕ n)
          ( base-fiber-sequence-Pointed-Type S)))
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S)))
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( n)
          ( total-space-fiber-sequence-Pointed-Type S)))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( succ-ℕ n)
          ( base-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S))
        ( canonical-boundary-hom-concrete-homotopy-group-fiber-sequence S n))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( n)
          ( total-space-fiber-sequence-Pointed-Type S))
        ( hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence S n))
  is-exact-hom-Group-is-exact-set-truncation-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence
    n =
    is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type
      ( iterated-loop-space
        ( succ-ℕ n)
        ( base-fiber-sequence-Pointed-Type S))
      ( iterated-loop-space
        ( n)
        ( fiber-fiber-sequence-Pointed-Type S))
      ( iterated-loop-space
        ( n)
        ( total-space-fiber-sequence-Pointed-Type S))
      ( canonical-pointed-map-iterated-boundary-fiber-sequence S n)
      ( pointed-map-iterated-loop-space
        ( n)
        ( fiber-inclusion-fiber-sequence-Pointed-Type S))

  is-exact-hom-Group-is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence :
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
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S n) →
    is-exact-hom-Group
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( succ-ℕ n)
          ( total-space-fiber-sequence-Pointed-Type S)))
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( succ-ℕ n)
          ( base-fiber-sequence-Pointed-Type S)))
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S)))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( succ-ℕ n)
          ( total-space-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( succ-ℕ n)
          ( base-fiber-sequence-Pointed-Type S))
        ( hom-fibration-concrete-homotopy-group-fiber-sequence S (succ-ℕ n)))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( succ-ℕ n)
          ( base-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S))
        ( boundary-hom-concrete-homotopy-group-fiber-sequence S n))
  is-exact-hom-Group-is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence n =
    is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type
      ( iterated-loop-space
        ( succ-ℕ n)
        ( total-space-fiber-sequence-Pointed-Type S))
      ( iterated-loop-space
        ( succ-ℕ n)
        ( base-fiber-sequence-Pointed-Type S))
      ( iterated-loop-space
        ( n)
        ( fiber-fiber-sequence-Pointed-Type S))
      ( pointed-map-iterated-loop-space
        ( succ-ℕ n)
        ( fibration-fiber-sequence-Pointed-Type S))
      ( pointed-map-iterated-boundary-fiber-sequence S n)

```
