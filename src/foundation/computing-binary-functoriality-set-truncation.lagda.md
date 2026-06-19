# Computing binary functoriality of set truncation

```agda
module foundation.computing-binary-functoriality-set-truncation where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-set-truncation
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.set-truncations
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

The binary functorial action of set truncation is defined by distributing set
truncation over binary products and then applying the unary functorial action.
On two points in the image of the set-truncation unit, it computes to the point
given by applying the original binary map.

## Theorem

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : A → B → C)
  where

  compute-binary-map-trunc-Set-unit-trunc-Set :
    (x : A) (y : B) →
    binary-map-trunc-Set f (unit-trunc-Set x) (unit-trunc-Set y) ＝
    unit-trunc-Set (f x y)
  compute-binary-map-trunc-Set-unit-trunc-Set x y =
    ( ap
      ( map-trunc-Set (λ (t : A × B) → f (pr1 t) (pr2 t)))
      ( is-injective-equiv
        ( equiv-distributive-trunc-product-Set A B)
        ( ( is-section-map-inv-equiv
            ( equiv-distributive-trunc-product-Set A B)
            ( unit-trunc-Set x , unit-trunc-Set y)) ∙
          ( inv (triangle-distributive-trunc-product-Set A B (x , y)))))) ∙
    ( naturality-unit-trunc-Set
      ( λ (t : A × B) → f (pr1 t) (pr2 t))
      ( x , y))

module _
  {l1 l2 l3 : Level}
  where

  preserves-binary-map-map-inv-equiv-unit-trunc-Set :
    (X : Set l1) (Y : Set l2) (Z : Set l3)
    (f : type-Set X → type-Set Y → type-Set Z)
    (x : type-trunc-Set (type-Set X))
    (y : type-trunc-Set (type-Set Y)) →
    map-inv-equiv (equiv-unit-trunc-Set Z)
      ( binary-map-trunc-Set f x y) ＝
    f ( map-inv-equiv (equiv-unit-trunc-Set X) x)
      ( map-inv-equiv (equiv-unit-trunc-Set Y) y)
  preserves-binary-map-map-inv-equiv-unit-trunc-Set X Y Z f =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ x y →
        set-Prop
          ( Id-Prop
            ( Z)
            ( map-inv-equiv (equiv-unit-trunc-Set Z)
              ( binary-map-trunc-Set f x y))
            ( f
              ( map-inv-equiv (equiv-unit-trunc-Set X) x)
              ( map-inv-equiv (equiv-unit-trunc-Set Y) y))))
      ( λ p q →
        ( ap
          ( map-inv-equiv (equiv-unit-trunc-Set Z))
          ( compute-binary-map-trunc-Set-unit-trunc-Set f p q)) ∙
        ( is-retraction-map-inv-equiv
          ( equiv-unit-trunc-Set Z)
          ( f p q)) ∙
        ( ap-binary
          ( f)
          ( inv
            ( is-retraction-map-inv-equiv
              ( equiv-unit-trunc-Set X)
              ( p)))
          ( inv
            ( is-retraction-map-inv-equiv
              ( equiv-unit-trunc-Set Y)
              ( q)))))
```
