# Type arithmetic for joins of types

```agda
module synthetic-homotopy-theory.type-arithmetic-joins-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.dependent-identifications
open import foundation.constant-type-families
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.flattening-lemma-pushouts
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

This file records arithmetic laws for the **join of types**. The first such law
is commutativity:

```text
  A * B ≃ B * A.
```

The proof is a pushout argument. The standard cocone on `B * A` is first
swapped, and then extended along the commutativity equivalence
`A × B ≃ B × A`.

## Laws

### Commutativity of joins

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  cocone-commutative-join : cocone pr1 pr2 (B * A)
  cocone-commutative-join =
    comp-cocone-hom-span
      ( pr2)
      ( pr1)
      ( pr1)
      ( pr2)
      ( id)
      ( id)
      ( map-commutative-product)
      ( swap-cocone pr1 pr2 (B * A) cocone-join)
      ( refl-htpy)
      ( refl-htpy)

  map-commutative-join : A * B → B * A
  map-commutative-join =
    cogap-join (B * A) cocone-commutative-join

  compute-inl-map-commutative-join :
    map-commutative-join ∘ inl-join ~ inr-join
  compute-inl-map-commutative-join =
    compute-inl-cogap-join cocone-commutative-join

  compute-inr-map-commutative-join :
    map-commutative-join ∘ inr-join ~ inl-join
  compute-inr-map-commutative-join =
    compute-inr-cogap-join cocone-commutative-join

  compute-glue-map-commutative-join :
    statement-coherence-htpy-cocone pr1 pr2
      ( cocone-map pr1 pr2 cocone-join map-commutative-join)
      ( cocone-commutative-join)
      ( compute-inl-map-commutative-join)
      ( compute-inr-map-commutative-join)
  compute-glue-map-commutative-join =
    compute-glue-cogap-join cocone-commutative-join

  universal-property-pushout-cocone-commutative-join :
    universal-property-pushout pr1 pr2 cocone-commutative-join
  universal-property-pushout-cocone-commutative-join =
    universal-property-pushout-extended-by-equivalences
      ( pr2)
      ( pr1)
      ( pr1)
      ( pr2)
      ( id)
      ( id)
      ( map-commutative-product)
      ( swap-cocone pr1 pr2 (B * A) cocone-join)
      ( universal-property-pushout-swap-cocone-universal-property-pushout
        ( pr1)
        ( pr2)
        ( B * A)
        ( cocone-join)
        ( up-join))
      ( refl-htpy)
      ( refl-htpy)
      ( is-equiv-id)
      ( is-equiv-id)
      ( is-equiv-map-commutative-product)

  is-equiv-map-commutative-join : is-equiv map-commutative-join
  is-equiv-map-commutative-join =
    is-equiv-up-pushout-up-pushout
      ( pr1)
      ( pr2)
      ( cocone-join)
      ( cocone-commutative-join)
      ( map-commutative-join)
      ( ( compute-inl-map-commutative-join) ,
        ( ( compute-inr-map-commutative-join) ,
          ( compute-glue-map-commutative-join)))
      ( up-join)
      ( universal-property-pushout-cocone-commutative-join)

  commutative-join : A * B ≃ B * A
  pr1 commutative-join = map-commutative-join
  pr2 commutative-join = is-equiv-map-commutative-join
```

### Products preserve join pushouts

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  left-map-span-product-join : (A × B) × C → A × C
  left-map-span-product-join =
    map-product (λ (t : A × B) → pr1 t) (id {A = C})

  right-map-span-product-join : (A × B) × C → B × C
  right-map-span-product-join =
    map-product (λ (t : A × B) → pr2 t) (id {A = C})

  coherence-vertical-map-span-flattening-join-product :
    horizontal-map-span-flattening-pushout
      ( λ _ → C)
      ( λ (t : A × B) → pr1 t)
      ( λ (t : A × B) → pr2 t)
      ( cocone-join) ~
    right-map-span-product-join
  coherence-vertical-map-span-flattening-join-product (t , c) =
    eq-pair-Σ refl (tr-constant-type-family (glue-join t) c)

  universal-property-pushout-product-join-data :
    {l : Level} →
    Σ ( cocone
        ( left-map-span-product-join)
        ( right-map-span-product-join)
        ( (A * B) × C))
      ( universal-property-pushout-Level l
        ( left-map-span-product-join)
        ( right-map-span-product-join))
  universal-property-pushout-product-join-data =
    universal-property-pushout-extension-by-equivalences
      ( vertical-map-span-flattening-pushout
        ( λ _ → C)
        ( λ (t : A × B) → pr1 t)
        ( λ (t : A × B) → pr2 t)
        ( cocone-join))
      ( horizontal-map-span-flattening-pushout
        ( λ _ → C)
        ( λ (t : A × B) → pr1 t)
        ( λ (t : A × B) → pr2 t)
        ( cocone-join))
      ( left-map-span-product-join)
      ( right-map-span-product-join)
      ( id {A = A × C})
      ( id {A = B × C})
      ( id {A = (A × B) × C})
      ( cocone-flattening-pushout (λ _ → C) pr1 pr2 cocone-join)
      ( flattening-lemma-pushout (λ _ → C) pr1 pr2 cocone-join up-join)
      ( refl-htpy)
      ( coherence-vertical-map-span-flattening-join-product)
      ( is-equiv-id {A = A × C})
      ( is-equiv-id {A = B × C})
      ( is-equiv-id {A = (A × B) × C})

  cocone-product-join :
    cocone
      ( left-map-span-product-join)
      ( right-map-span-product-join)
      ( (A * B) × C)
  cocone-product-join =
    pr1 (universal-property-pushout-product-join-data {l = lzero})

  universal-property-pushout-cocone-product-join :
    universal-property-pushout
      ( left-map-span-product-join)
      ( right-map-span-product-join)
      ( cocone-product-join)
  universal-property-pushout-cocone-product-join =
    pr2 universal-property-pushout-product-join-data
```

### Associativity of joins

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  cocone-left-map-associative-join :
    cocone pr1 pr2 (A * (B * C))
  pr1 cocone-left-map-associative-join = inl-join
  pr1 (pr2 cocone-left-map-associative-join) = inr-join ∘ inl-join
  pr2 (pr2 cocone-left-map-associative-join) (a , b) =
    glue-join (a , inl-join b)

  map-left-associative-join : A * B → A * (B * C)
  map-left-associative-join =
    cogap-join (A * (B * C)) cocone-left-map-associative-join

  compute-inl-map-left-associative-join :
    map-left-associative-join ∘ inl-join ~ inl-join
  compute-inl-map-left-associative-join =
    compute-inl-cogap-join cocone-left-map-associative-join

  compute-inr-map-left-associative-join :
    map-left-associative-join ∘ inr-join ~ inr-join ∘ inl-join
  compute-inr-map-left-associative-join =
    compute-inr-cogap-join cocone-left-map-associative-join

  compute-glue-map-left-associative-join :
    statement-coherence-htpy-cocone pr1 pr2
      ( cocone-map pr1 pr2 cocone-join map-left-associative-join)
      ( cocone-left-map-associative-join)
      ( compute-inl-map-left-associative-join)
      ( compute-inr-map-left-associative-join)
  compute-glue-map-left-associative-join =
    compute-glue-cogap-join cocone-left-map-associative-join

  naturality-glue-left-join :
    (a : A) (b : B) (c : C) →
    glue-join (a , inl-join b) ∙
    ap inr-join (glue-join (b , c)) ＝
    glue-join (a , inr-join c)
  naturality-glue-left-join a b c =
    inv
      ( map-inv-compute-dependent-identification-eq-value-function
        ( λ _ → inl-join {A = A} {B = B * C} a)
        ( inr-join)
        ( glue-join (b , c))
        ( glue-join (a , inl-join b))
        ( glue-join (a , inr-join c))
        ( apd (λ y → glue-join (a , y)) (glue-join (b , c)))) ∙
    ap
      ( λ p → p ∙ glue-join (a , inr-join c))
      ( ap-const (inl-join {A = A} {B = B * C} a) (glue-join (b , c)))

  tr-dependent-function-type-fixed-domain :
    {l4 l5 l6 : Level} {X : UU l4} {D : UU l5}
    (P : X → D → UU l6) {x y : X} →
    (p : x ＝ y) (h : (d : D) → P x d) (d : D) →
    tr (λ z → (d' : D) → P z d') p h d ＝
    tr (λ z → P z d) p (h d)
  tr-dependent-function-type-fixed-domain P refl h d = refl

  compute-tr-function-left-map-associative-join :
    (t : A × B) (c : C)
    (h :
      (c' : C) →
      map-left-associative-join (inl-join (pr1 t)) ＝
      inr-join (inr-join c')) →
    ( tr
      ( λ x → (c' : C) →
        map-left-associative-join x ＝ inr-join (inr-join c'))
      ( glue-join t)
      ( h)
      ( c)) ＝
    tr
      ( λ x → map-left-associative-join x ＝ inr-join (inr-join c))
      ( glue-join t)
      ( h c)
  compute-tr-function-left-map-associative-join t c h =
    tr-dependent-function-type-fixed-domain
      ( λ x c' → map-left-associative-join x ＝ inr-join (inr-join c'))
      ( glue-join t)
      ( h)
      ( c)

  compute-tr-Id-left-map-left-associative-join :
    (t : A × B) (c : C)
    (q :
      map-left-associative-join (inl-join (pr1 t)) ＝
      inr-join (inr-join c)) →
    tr
      ( λ x → map-left-associative-join x ＝ inr-join (inr-join c))
      ( glue-join t)
      ( q) ＝
    inv (ap map-left-associative-join (glue-join t)) ∙ q
  compute-tr-Id-left-map-left-associative-join t c q =
    inv
      ( substitution-law-tr
        ( λ x → x ＝ inr-join (inr-join c))
        ( map-left-associative-join)
        ( glue-join t)) ∙
    tr-Id-left (ap map-left-associative-join (glue-join t)) q

  left-transpose-compute-glue-map-left-associative-join :
    (t : A × B) →
    inv (ap map-left-associative-join (glue-join t)) ∙
    ( compute-inl-map-left-associative-join (pr1 t) ∙
      glue-join (pr1 t , inl-join (pr2 t))) ＝
    compute-inr-map-left-associative-join (pr2 t)
  left-transpose-compute-glue-map-left-associative-join t =
    equational-reasoning
      inv apm ∙ (linl ∙ glue-inl)
      ＝ inv apm ∙ (apm ∙ rinr)
        by ap (inv apm ∙_) (inv (compute-glue-map-left-associative-join t))
      ＝ (inv apm ∙ apm) ∙ rinr
        by inv (assoc (inv apm) apm rinr)
      ＝ rinr
        by ap (_∙ rinr) (left-inv apm)
    where
    apm = ap map-left-associative-join (glue-join t)
    linl = compute-inl-map-left-associative-join (pr1 t)
    rinr = compute-inr-map-left-associative-join (pr2 t)
    glue-inl = glue-join (pr1 t , inl-join (pr2 t))

  pointwise-coherence-left-map-associative-join :
    (t : A × B) (c : C) →
    ( tr
      ( λ x → (c' : C) →
        map-left-associative-join x ＝ inr-join (inr-join c'))
      ( glue-join t)
      ( λ c' →
        compute-inl-map-left-associative-join (pr1 t) ∙
        glue-join (pr1 t , inr-join c'))
      ( c)) ＝
    ( compute-inr-map-left-associative-join (pr2 t) ∙
      ap inr-join (glue-join (pr2 t , c)))
  pointwise-coherence-left-map-associative-join t c =
    equational-reasoning
      tr
        ( λ x → (c' : C) →
          map-left-associative-join x ＝ inr-join (inr-join c'))
        ( glue-join t)
        ( h)
        ( c)
      ＝ tr
          ( λ x → map-left-associative-join x ＝ inr-join (inr-join c))
          ( glue-join t)
          ( h c)
        by compute-tr-function-left-map-associative-join t c h
      ＝ inv apm ∙ (linl ∙ glue-inr)
        by compute-tr-Id-left-map-left-associative-join t c (h c)
      ＝ inv apm ∙ (linl ∙ (glue-inl ∙ apinr))
        by ap (λ p → inv apm ∙ (linl ∙ p))
          ( inv (naturality-glue-left-join (pr1 t) (pr2 t) c))
      ＝ inv apm ∙ ((linl ∙ glue-inl) ∙ apinr)
        by ap (inv apm ∙_) (inv (assoc linl glue-inl apinr))
      ＝ (inv apm ∙ (linl ∙ glue-inl)) ∙ apinr
        by inv (assoc (inv apm) (linl ∙ glue-inl) apinr)
      ＝ rinr ∙ apinr
        by ap (_∙ apinr)
          ( left-transpose-compute-glue-map-left-associative-join t)
    where
    h :
      (c' : C) →
      map-left-associative-join (inl-join (pr1 t)) ＝
      inr-join (inr-join c')
    h c' =
      compute-inl-map-left-associative-join (pr1 t) ∙
      glue-join (pr1 t , inr-join c')

    apm = ap map-left-associative-join (glue-join t)
    linl = compute-inl-map-left-associative-join (pr1 t)
    rinr = compute-inr-map-left-associative-join (pr2 t)
    glue-inl = glue-join (pr1 t , inl-join (pr2 t))
    glue-inr = glue-join (pr1 t , inr-join c)
    apinr = ap inr-join (glue-join (pr2 t , c))

  coherence-left-map-associative-join :
    (t : A × B) →
    dependent-identification
      ( λ x → (c : C) →
        map-left-associative-join x ＝ inr-join (inr-join c))
      ( glue-join t)
      ( λ c →
        compute-inl-map-left-associative-join (pr1 t) ∙
        glue-join (pr1 t , inr-join c))
      ( λ c →
        compute-inr-map-left-associative-join (pr2 t) ∙
        ap inr-join (glue-join (pr2 t , c)))
  coherence-left-map-associative-join t =
    eq-htpy (pointwise-coherence-left-map-associative-join t)

  dependent-cocone-left-map-associative-join :
    dependent-cocone pr1 pr2 cocone-join
      ( λ x → (c : C) →
        map-left-associative-join x ＝ inr-join (inr-join c))
  pr1 dependent-cocone-left-map-associative-join a c =
    compute-inl-map-left-associative-join a ∙ glue-join (a , inr-join c)
  pr1 (pr2 dependent-cocone-left-map-associative-join) b c =
    compute-inr-map-left-associative-join b ∙ ap inr-join (glue-join (b , c))
  pr2 (pr2 dependent-cocone-left-map-associative-join) =
    coherence-left-map-associative-join

  coherence-map-associative-join :
    (x : A * B) (c : C) →
    map-left-associative-join x ＝ inr-join (inr-join c)
  coherence-map-associative-join =
    dependent-cogap-join dependent-cocone-left-map-associative-join

  cocone-associative-join :
    cocone pr1 pr2 (A * (B * C))
  pr1 cocone-associative-join =
    map-left-associative-join
  pr1 (pr2 cocone-associative-join) =
    inr-join ∘ inr-join
  pr2 (pr2 cocone-associative-join) (x , c) =
    coherence-map-associative-join x c

  map-associative-join : (A * B) * C → A * (B * C)
  map-associative-join =
    cogap-join (A * (B * C)) cocone-associative-join

  compute-inl-map-associative-join :
    map-associative-join ∘ inl-join ~ map-left-associative-join
  compute-inl-map-associative-join =
    compute-inl-cogap-join cocone-associative-join

  compute-inr-map-associative-join :
    map-associative-join ∘ inr-join ~ inr-join ∘ inr-join
  compute-inr-map-associative-join =
    compute-inr-cogap-join cocone-associative-join

  compute-glue-map-associative-join :
    statement-coherence-htpy-cocone pr1 pr2
      ( cocone-map pr1 pr2 cocone-join map-associative-join)
      ( cocone-associative-join)
      ( compute-inl-map-associative-join)
      ( compute-inr-map-associative-join)
  compute-glue-map-associative-join =
    compute-glue-cogap-join cocone-associative-join
```
