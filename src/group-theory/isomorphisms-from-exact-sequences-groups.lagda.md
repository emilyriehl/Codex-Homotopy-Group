# Isomorphisms from exact sequences of groups

```agda
module group-theory.isomorphisms-from-exact-sequences-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.surjective-maps
open import foundation.universe-levels

open import group-theory.exact-sequences-groups
open import group-theory.full-subgroups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.images-of-group-homomorphisms
open import group-theory.isomorphisms-groups
open import group-theory.kernels-homomorphisms-groups
open import group-theory.subgroups
open import group-theory.surjective-group-homomorphisms
open import group-theory.trivial-groups
```

</details>

## Idea

An exact segment

```text
A → B → C → D
```

whose outer groups `A` and `D` are trivial identifies the middle homomorphism
`B → C` as a group isomorphism.

This file records the algebraic extraction needed to turn the Hopf long exact
sequence into the comparison `π₃(S³) ≅ π₃(S²)`.

## Theorem

### Exactness with trivial outer groups gives an isomorphism

```agda
is-iso-is-exact-is-trivial-outer-groups :
  {l1 l2 l3 l4 : Level}
  (A : Group l1) (B : Group l2) (C : Group l3) (D : Group l4)
  (f : hom-Group A B) (g : hom-Group B C) (h : hom-Group C D) →
  is-trivial-Group A →
  is-trivial-Group D →
  is-exact-hom-Group A B C f g →
  is-exact-hom-Group B C D g h →
  is-iso-Group B C g
is-iso-is-exact-is-trivial-outer-groups
  A B C D f g h is-trivial-A is-trivial-D is-exact-f-g is-exact-g-h =
  is-iso-is-equiv-hom-Group B C g
    ( is-equiv-is-emb-is-surjective
      ( is-surjective-is-full-subgroup-image-hom-Group B C g
        is-full-image-g)
      ( is-emb-is-injective (is-set-type-Group C) is-injective-g))
  where
  is-full-image-g : is-full-Subgroup C (image-hom-Group B C g)
  is-full-image-g x =
    backward-implication
      ( is-exact-g-h x)
      ( eq-is-contr is-trivial-D)

  is-in-kernel-left-div-g :
    {x y : type-Group B} →
    map-hom-Group B C g x ＝ map-hom-Group B C g y →
    is-in-kernel-hom-Group B C g (left-div-Group B x y)
  is-in-kernel-left-div-g p =
    ( inv (is-unit-left-div-eq-Group C p)) ∙
    ( inv (preserves-left-div-hom-Group B C g))

  is-unit-left-div-is-in-image-f :
    {x y : type-Group B} →
    is-in-Subgroup B
      ( image-hom-Group A B f)
      ( left-div-Group B x y) →
    is-unit-Group B (left-div-Group B x y)
  is-unit-left-div-is-in-image-f {x} {y} u =
    apply-universal-property-trunc-Prop u
      ( is-unit-prop-Group B (left-div-Group B x y))
      ( λ where
        (a , q) →
          ( inv q) ∙
          ( ap
            ( map-hom-Group A B f)
            ( eq-is-contr is-trivial-A {x = a} {y = unit-Group A})) ∙
          ( preserves-unit-hom-Group A B f))

  is-injective-g : is-injective (map-hom-Group B C g)
  is-injective-g {x} {y} p =
    eq-is-unit-left-div-Group B
      ( is-unit-left-div-is-in-image-f
        ( backward-implication
          ( is-exact-f-g (left-div-Group B x y))
          ( is-in-kernel-left-div-g p)))
```
