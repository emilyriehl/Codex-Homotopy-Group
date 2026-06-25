# Fibers of dependent pushout-products

```agda
module synthetic-homotopy-theory.fibers-dependent-pushout-products where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterated-successors-truncation-levels
open import foundation.transport-along-identifications
open import foundation.truncation-levels
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.connectivity-joins-of-types
open import synthetic-homotopy-theory.dependent-pushout-products
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The
[dependent pushout-product](synthetic-homotopy-theory.dependent-pushout-products.md)
of `f : A → X` and a family of maps `g : (x : X) → B x → Y x`
is fiberwise a join. At a point `(x , y) : Σ X Y`, its fiber is equivalent to
the join

```text
  fiber f x * fiber (g x) y.
```

This file records the fiber computation and the resulting connectivity theorem.

## Product-map fibers in a dependent pushout-product square

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {X : UU l2}
  {B : X → UU l3} {Y : X → UU l4}
  (f : A → X) (g : (x : X) → B x → Y x)
  (x : X) (y : Y x)
  where

  equiv-fiber-left-map-dependent-pushout-product :
    fiber f x ≃ fiber (map-Σ Y f (λ _ → id)) (x , y)
  pr1 equiv-fiber-left-map-dependent-pushout-product (a , refl) =
    ((a , y) , refl)
  pr2 equiv-fiber-left-map-dependent-pushout-product =
    is-equiv-is-invertible
      ( λ { ((a , _) , refl) → (a , refl)})
      ( λ { ((a , _) , refl) → refl})
      ( λ { (a , refl) → refl})

  equiv-fiber-right-map-dependent-pushout-product :
    fiber (g x) y ≃ fiber (map-Σ Y id g) (x , y)
  pr1 equiv-fiber-right-map-dependent-pushout-product (b , refl) =
    ((x , b) , refl)
  pr2 equiv-fiber-right-map-dependent-pushout-product =
    is-equiv-is-invertible
      ( λ { ((.x , b) , refl) → (b , refl)})
      ( λ { ((.x , b) , refl) → refl})
      ( λ { (b , refl) → refl})

  equiv-fiber-top-map-dependent-pushout-product :
    fiber f x × fiber (g x) y ≃
    fiber
      ( ( map-Σ Y f (λ _ → id)) ∘
        ( map-Σ (Y ∘ f) id (g ∘ f)))
      ( x , y)
  pr1 equiv-fiber-top-map-dependent-pushout-product
    ((a , refl) , (b , refl)) =
    ((a , b) , refl)
  pr2 equiv-fiber-top-map-dependent-pushout-product =
    is-equiv-is-invertible
      ( λ { ((a , b) , refl) → ((a , refl) , (b , refl))})
      ( λ { ((a , b) , refl) → refl})
      ( λ { ((a , refl) , (b , refl)) → refl})

  coherence-left-map-fiber-dependent-pushout-product :
    coherence-square-maps
      ( map-equiv equiv-fiber-top-map-dependent-pushout-product)
      ( pr1)
      ( horizontal-map-span-cogap-fiber
        ( map-Σ (Y ∘ f) id (g ∘ f))
        ( map-Σ B f (λ _ → id))
        ( cocone-dependent-pushout-product f g)
        ( x , y))
      ( map-equiv equiv-fiber-left-map-dependent-pushout-product)
  coherence-left-map-fiber-dependent-pushout-product
    ((a , refl) , (b , refl)) =
    refl

  coherence-right-map-fiber-dependent-pushout-product :
    coherence-square-maps
      ( pr2)
      ( map-equiv equiv-fiber-top-map-dependent-pushout-product)
      ( map-equiv equiv-fiber-right-map-dependent-pushout-product)
      ( vertical-map-span-cogap-fiber
        ( map-Σ (Y ∘ f) id (g ∘ f))
        ( map-Σ B f (λ _ → id))
        ( cocone-dependent-pushout-product f g)
        ( x , y))
  coherence-right-map-fiber-dependent-pushout-product
    ((a , refl) , (b , refl)) =
    ( ap
      ( map-inv-equiv e)
      ( inv (eq-pair-eq-fiber path-glue-cogap))) ∙
    ( is-retraction-map-inv-equiv e target-fiber)
    where
    left-map = map-Σ (Y ∘ f) id (g ∘ f)
    right-map = map-Σ B f (λ _ → id)
    square-cocone = cocone-dependent-pushout-product f g
    z = f a , g (f a) b
    pushout-cogap = cogap left-map right-map square-cocone
    glue = glue-pushout left-map right-map (a , b)

    e =
      equiv-fiber-vertical-map-cocone-cogap-inr
        left-map right-map square-cocone z

    target-fiber :
      fiber (vertical-map-cocone left-map right-map square-cocone) z
    target-fiber =
      map-equiv equiv-fiber-right-map-dependent-pushout-product (b , refl)

    path-inl :
      pushout-cogap (inl-pushout left-map right-map (a , g (f a) b)) ＝ z
    path-inl =
      compute-inl-cogap left-map right-map square-cocone (a , g (f a) b) ∙
      refl

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

  universal-property-join-cocone-fiber-cogap-dependent-pushout-product :
    {l : Level} →
    Σ ( cocone
        ( pr1 {B = λ _ → fiber (g x) y})
        ( pr2 {B = λ _ → fiber (g x) y})
        ( fiber
          ( cogap
            ( map-Σ (Y ∘ f) id (g ∘ f))
            ( map-Σ B f (λ _ → id))
            ( cocone-dependent-pushout-product f g))
          ( x , y)))
      ( universal-property-pushout-Level l
        ( pr1 {B = λ _ → fiber (g x) y})
        ( pr2 {B = λ _ → fiber (g x) y}))
  universal-property-join-cocone-fiber-cogap-dependent-pushout-product =
    universal-property-pushout-cogap-fiber-up-to-equiv
      ( map-Σ (Y ∘ f) id (g ∘ f))
      ( map-Σ B f (λ _ → id))
      ( cocone-dependent-pushout-product f g)
      ( x , y)
      ( fiber f x × fiber (g x) y)
      ( fiber f x)
      ( fiber (g x) y)
      ( equiv-fiber-left-map-dependent-pushout-product)
      ( equiv-fiber-right-map-dependent-pushout-product)
      ( equiv-fiber-top-map-dependent-pushout-product)
      ( pr1)
      ( pr2)
      ( coherence-left-map-fiber-dependent-pushout-product)
      ( coherence-right-map-fiber-dependent-pushout-product)

  join-cocone-fiber-cogap-dependent-pushout-product :
    cocone
      ( pr1 {B = λ _ → fiber (g x) y})
      ( pr2 {B = λ _ → fiber (g x) y})
      ( fiber
        ( cogap
          ( map-Σ (Y ∘ f) id (g ∘ f))
          ( map-Σ B f (λ _ → id))
          ( cocone-dependent-pushout-product f g))
        ( x , y))
  join-cocone-fiber-cogap-dependent-pushout-product =
    pr1
      ( universal-property-join-cocone-fiber-cogap-dependent-pushout-product
        {lzero})

  universal-property-join-fiber-cogap-dependent-pushout-product :
    universal-property-pushout
      ( pr1 {B = λ _ → fiber (g x) y})
      ( pr2 {B = λ _ → fiber (g x) y})
      ( join-cocone-fiber-cogap-dependent-pushout-product)
  universal-property-join-fiber-cogap-dependent-pushout-product =
    pr2 universal-property-join-cocone-fiber-cogap-dependent-pushout-product

  fiber-cogap-dependent-pushout-product-join-fibers :
    fiber f x * fiber (g x) y →
    fiber
      ( cogap
        ( map-Σ (Y ∘ f) id (g ∘ f))
        ( map-Σ B f (λ _ → id))
        ( cocone-dependent-pushout-product f g))
      ( x , y)
  fiber-cogap-dependent-pushout-product-join-fibers =
    cogap-join
      ( fiber
        ( cogap
          ( map-Σ (Y ∘ f) id (g ∘ f))
          ( map-Σ B f (λ _ → id))
          ( cocone-dependent-pushout-product f g))
        ( x , y))
      ( join-cocone-fiber-cogap-dependent-pushout-product)

  is-equiv-fiber-cogap-dependent-pushout-product-join-fibers :
    is-equiv fiber-cogap-dependent-pushout-product-join-fibers
  is-equiv-fiber-cogap-dependent-pushout-product-join-fibers =
    is-equiv-up-pushout-up-pushout
      ( pr1 {B = λ _ → fiber (g x) y})
      ( pr2 {B = λ _ → fiber (g x) y})
      ( cocone-join)
      ( join-cocone-fiber-cogap-dependent-pushout-product)
      ( fiber-cogap-dependent-pushout-product-join-fibers)
      ( htpy-cocone-map-universal-property-pushout
        ( pr1 {B = λ _ → fiber (g x) y})
        ( pr2 {B = λ _ → fiber (g x) y})
        ( cocone-join)
        ( up-join)
        ( join-cocone-fiber-cogap-dependent-pushout-product))
      ( up-join)
      ( universal-property-join-fiber-cogap-dependent-pushout-product)

  equiv-fiber-cogap-dependent-pushout-product-join-fibers :
    (fiber f x * fiber (g x) y) ≃
    fiber
      ( cogap
        ( map-Σ (Y ∘ f) id (g ∘ f))
        ( map-Σ B f (λ _ → id))
        ( cocone-dependent-pushout-product f g))
      ( x , y)
  pr1 equiv-fiber-cogap-dependent-pushout-product-join-fibers =
    fiber-cogap-dependent-pushout-product-join-fibers
  pr2 equiv-fiber-cogap-dependent-pushout-product-join-fibers =
    is-equiv-fiber-cogap-dependent-pushout-product-join-fibers
```

## Connectivity of dependent pushout-products

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {X : UU l2}
  {B : X → UU l3} {Y : X → UU l4}
  (f : A → X) (g : (x : X) → B x → Y x)
  where

  is-connected-map-cogap-dependent-pushout-product-is-connected-maps :
    (k n : 𝕋) →
    is-connected-map k f →
    ((x : X) → is-connected-map n (g x)) →
    is-connected-map (add+2-𝕋 k n)
      ( cogap
        ( map-Σ (Y ∘ f) id (g ∘ f))
        ( map-Σ B f (λ _ → id))
        ( cocone-dependent-pushout-product f g))
  is-connected-map-cogap-dependent-pushout-product-is-connected-maps
    k n H K (x , y) =
    is-connected-equiv'
      ( equiv-fiber-cogap-dependent-pushout-product-join-fibers f g x y)
      ( is-connected-join-is-connected k n (H x) (K x y))
```
