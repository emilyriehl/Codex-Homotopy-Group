# Fibers of pushout-products

```agda
module synthetic-homotopy-theory.fibers-pushout-products where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterated-successors-truncation-levels
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.truncation-levels
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.connectivity-joins-of-types
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushout-products
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The
[pushout-product](synthetic-homotopy-theory.pushout-products.md) of two maps is
fiberwise a join. This file starts by recording the elementary fiber
computations for the product maps that occur in the defining square of the
pushout-product.

## Product-map fibers in a pushout-product square

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (x : X) (y : Y)
  where

  equiv-right-unit-product-fiber-id :
    fiber f x ≃ fiber f x × fiber (id {A = Y}) y
  pr1 equiv-right-unit-product-fiber-id u = u , (y , refl)
  pr2 equiv-right-unit-product-fiber-id =
    is-equiv-is-invertible
      ( pr1)
      ( λ (u , v) →
        eq-pair
          ( refl)
          ( eq-is-contr (is-torsorial-Id' y)))
      ( refl-htpy)

  equiv-left-unit-product-fiber-id :
    fiber g y ≃ fiber (id {A = X}) x × fiber g y
  pr1 equiv-left-unit-product-fiber-id v = (x , refl) , v
  pr2 equiv-left-unit-product-fiber-id =
    is-equiv-is-invertible
      ( pr2)
      ( λ (u , v) →
        eq-pair
          ( eq-is-contr (is-torsorial-Id' x))
          ( refl))
      ( refl-htpy)

  equiv-fiber-left-map-pushout-product :
    fiber f x ≃ fiber (map-product f (id {A = Y})) (x , y)
  equiv-fiber-left-map-pushout-product =
    ( inv-equiv (compute-fiber-map-product f (id {A = Y}) (x , y))) ∘e
    equiv-right-unit-product-fiber-id

  equiv-fiber-right-map-pushout-product :
    fiber g y ≃ fiber (map-product (id {A = X}) g) (x , y)
  equiv-fiber-right-map-pushout-product =
    ( inv-equiv (compute-fiber-map-product (id {A = X}) g (x , y))) ∘e
    equiv-left-unit-product-fiber-id

  equiv-fiber-top-map-pushout-product :
    fiber f x × fiber g y ≃
    fiber
      ( ( map-product f (id {A = Y})) ∘
        ( map-product (id {A = A}) g))
      ( x , y)
  equiv-fiber-top-map-pushout-product =
    inv-equiv (compute-fiber-map-product f g (x , y))

  coherence-left-map-fiber-pushout-product :
    coherence-square-maps
      ( map-equiv equiv-fiber-top-map-pushout-product)
      ( pr1)
      ( horizontal-map-span-cogap-fiber
        ( map-product (id {A = A}) g)
        ( map-product f (id {A = B}))
        ( cocone-pushout-product f g)
        ( x , y))
      ( map-equiv equiv-fiber-left-map-pushout-product)
  coherence-left-map-fiber-pushout-product ((a , refl) , (b , refl)) = refl

  coherence-right-map-fiber-pushout-product :
    coherence-square-maps
      ( pr2)
      ( map-equiv equiv-fiber-top-map-pushout-product)
      ( map-equiv equiv-fiber-right-map-pushout-product)
      ( vertical-map-span-cogap-fiber
        ( map-product (id {A = A}) g)
        ( map-product f (id {A = B}))
        ( cocone-pushout-product f g)
        ( x , y))
  coherence-right-map-fiber-pushout-product ((a , refl) , (b , refl)) =
    ( ap
      ( map-inv-equiv e)
      ( inv (eq-pair-eq-fiber path-glue-cogap))) ∙
    ( is-retraction-map-inv-equiv e target-fiber)
    where
    left-map = map-product (id {A = A}) g
    right-map = map-product f (id {A = B})
    square-cocone = cocone-pushout-product f g
    z = f a , g b
    pushout-cogap = cogap left-map right-map square-cocone
    glue = glue-pushout left-map right-map (a , b)

    e =
      equiv-fiber-vertical-map-cocone-cogap-inr
        left-map right-map square-cocone z

    target-fiber :
      fiber (vertical-map-cocone left-map right-map square-cocone) z
    target-fiber = map-equiv equiv-fiber-right-map-pushout-product (b , refl)

    path-inl :
      pushout-cogap (inl-pushout left-map right-map (a , g b)) ＝ z
    path-inl =
      compute-inl-cogap left-map right-map square-cocone (a , g b) ∙ refl

    path-inr :
      pushout-cogap (inr-pushout left-map right-map (f a , b)) ＝ z
    path-inr =
      compute-inr-cogap left-map right-map square-cocone (f a , b) ∙ refl

    path-glue-cogap :
      path-inr ＝ tr (λ w → pushout-cogap w ＝ z) glue path-inl
    path-glue-cogap =
      ( right-unit) ∙
      ( left-transpose-eq-concat
        ( ap pushout-cogap glue)
        ( compute-inr-cogap left-map right-map square-cocone (f a , b))
        ( path-inl)
        ( compute-glue-cogap left-map right-map square-cocone (a , b))) ∙
      ( inv (tr-Id-left (ap pushout-cogap glue) path-inl)) ∙
      ( substitution-law-tr (_＝ z) pushout-cogap glue)

  universal-property-join-cocone-fiber-cogap-pushout-product :
    {l : Level} →
    Σ ( cocone
        ( pr1 {B = λ _ → fiber g y})
        ( pr2 {B = λ _ → fiber g y})
        ( fiber
          ( cogap
            ( map-product (id {A = A}) g)
            ( map-product f (id {A = B}))
            ( cocone-pushout-product f g))
          ( x , y)))
      ( universal-property-pushout-Level l
        ( pr1 {B = λ _ → fiber g y})
        ( pr2 {B = λ _ → fiber g y}))
  universal-property-join-cocone-fiber-cogap-pushout-product =
    universal-property-pushout-cogap-fiber-up-to-equiv
      ( map-product (id {A = A}) g)
      ( map-product f (id {A = B}))
      ( cocone-pushout-product f g)
      ( x , y)
      ( fiber f x × fiber g y)
      ( fiber f x)
      ( fiber g y)
      ( equiv-fiber-left-map-pushout-product)
      ( equiv-fiber-right-map-pushout-product)
      ( equiv-fiber-top-map-pushout-product)
      ( pr1)
      ( pr2)
      ( coherence-left-map-fiber-pushout-product)
      ( coherence-right-map-fiber-pushout-product)

  join-cocone-fiber-cogap-pushout-product :
    cocone
      ( pr1 {B = λ _ → fiber g y})
      ( pr2 {B = λ _ → fiber g y})
      ( fiber
        ( cogap
          ( map-product (id {A = A}) g)
          ( map-product f (id {A = B}))
          ( cocone-pushout-product f g))
        ( x , y))
  join-cocone-fiber-cogap-pushout-product =
    pr1 (universal-property-join-cocone-fiber-cogap-pushout-product {lzero})

  universal-property-join-fiber-cogap-pushout-product :
    universal-property-pushout
      ( pr1 {B = λ _ → fiber g y})
      ( pr2 {B = λ _ → fiber g y})
      ( join-cocone-fiber-cogap-pushout-product)
  universal-property-join-fiber-cogap-pushout-product =
    pr2 universal-property-join-cocone-fiber-cogap-pushout-product

  fiber-cogap-pushout-product-join-fibers :
    fiber f x * fiber g y →
    fiber
      ( cogap
        ( map-product (id {A = A}) g)
        ( map-product f (id {A = B}))
        ( cocone-pushout-product f g))
      ( x , y)
  fiber-cogap-pushout-product-join-fibers =
    cogap-join
      ( fiber
        ( cogap
          ( map-product (id {A = A}) g)
          ( map-product f (id {A = B}))
          ( cocone-pushout-product f g))
        ( x , y))
      ( join-cocone-fiber-cogap-pushout-product)

  is-equiv-fiber-cogap-pushout-product-join-fibers :
    is-equiv fiber-cogap-pushout-product-join-fibers
  is-equiv-fiber-cogap-pushout-product-join-fibers =
    is-equiv-up-pushout-up-pushout
      ( pr1 {B = λ _ → fiber g y})
      ( pr2 {B = λ _ → fiber g y})
      ( cocone-join)
      ( join-cocone-fiber-cogap-pushout-product)
      ( fiber-cogap-pushout-product-join-fibers)
      ( htpy-cocone-map-universal-property-pushout
        ( pr1 {B = λ _ → fiber g y})
        ( pr2 {B = λ _ → fiber g y})
        ( cocone-join)
        ( up-join)
        ( join-cocone-fiber-cogap-pushout-product))
      ( up-join)
      ( universal-property-join-fiber-cogap-pushout-product)

  equiv-fiber-cogap-pushout-product-join-fibers :
    (fiber f x * fiber g y) ≃
    fiber
      ( cogap
        ( map-product (id {A = A}) g)
        ( map-product f (id {A = B}))
        ( cocone-pushout-product f g))
      ( x , y)
  pr1 equiv-fiber-cogap-pushout-product-join-fibers =
    fiber-cogap-pushout-product-join-fibers
  pr2 equiv-fiber-cogap-pushout-product-join-fibers =
    is-equiv-fiber-cogap-pushout-product-join-fibers
```

## Connectivity of pushout-products

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  is-connected-map-cogap-pushout-product-is-connected-maps :
    (k n : 𝕋) →
    is-connected-map k f →
    is-connected-map n g →
    is-connected-map (add+2-𝕋 k n)
      ( cogap
        ( map-product (id {A = A}) g)
          ( map-product f (id {A = B}))
          ( cocone-pushout-product f g))
  is-connected-map-cogap-pushout-product-is-connected-maps k n H K
    (x , y) =
    is-connected-equiv'
      ( equiv-fiber-cogap-pushout-product-join-fibers f g x y)
      ( is-connected-join-is-connected k n (H x) (K y))
```
