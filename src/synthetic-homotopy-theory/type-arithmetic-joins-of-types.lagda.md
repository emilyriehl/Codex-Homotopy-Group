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

```agda
naturality-homotopy :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f g : X → Y}
  (H : f ~ g) {x y : X} (p : x ＝ y) →
  ap f p ∙ H y ＝ H x ∙ ap g p
naturality-homotopy H refl = inv right-unit
```

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

  compute-inl-coherence-map-associative-join :
    (a : A) (c : C) →
    coherence-map-associative-join (inl-join a) c ＝
    compute-inl-map-left-associative-join a ∙ glue-join (a , inr-join c)
  compute-inl-coherence-map-associative-join a c =
    ap (λ h → h c) (compute-inl-dependent-cogap-join
      dependent-cocone-left-map-associative-join a)

  compute-inr-coherence-map-associative-join :
    (b : B) (c : C) →
    coherence-map-associative-join (inr-join b) c ＝
    compute-inr-map-left-associative-join b ∙ ap inr-join (glue-join (b , c))
  compute-inr-coherence-map-associative-join b c =
    ap (λ h → h c) (compute-inr-dependent-cogap-join
      dependent-cocone-left-map-associative-join b)

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

  cocone-right-map-associative-join :
    cocone pr1 pr2 ((A * B) * C)
  pr1 cocone-right-map-associative-join =
    inl-join ∘ inr-join
  pr1 (pr2 cocone-right-map-associative-join) =
    inr-join
  pr2 (pr2 cocone-right-map-associative-join) (b , c) =
    glue-join (inr-join b , c)

  map-right-associative-join : B * C → (A * B) * C
  map-right-associative-join =
    cogap-join ((A * B) * C) cocone-right-map-associative-join

  compute-inl-map-right-associative-join :
    map-right-associative-join ∘ inl-join ~ inl-join ∘ inr-join
  compute-inl-map-right-associative-join =
    compute-inl-cogap-join cocone-right-map-associative-join

  compute-inr-map-right-associative-join :
    map-right-associative-join ∘ inr-join ~ inr-join
  compute-inr-map-right-associative-join =
    compute-inr-cogap-join cocone-right-map-associative-join

  compute-glue-map-right-associative-join :
    statement-coherence-htpy-cocone pr1 pr2
      ( cocone-map pr1 pr2 cocone-join map-right-associative-join)
      ( cocone-right-map-associative-join)
      ( compute-inl-map-right-associative-join)
      ( compute-inr-map-right-associative-join)
  compute-glue-map-right-associative-join =
    compute-glue-cogap-join cocone-right-map-associative-join

  naturality-glue-right-join :
    (a : A) (b : B) (c : C) →
    ap inl-join (glue-join (a , b)) ∙
    glue-join (inr-join b , c) ＝
    glue-join (inl-join a , c)
  naturality-glue-right-join a b c =
    map-inv-compute-dependent-identification-eq-value-function
      ( inl-join {A = A * B} {B = C})
      ( λ _ → inr-join {A = A * B} {B = C} c)
      ( glue-join (a , b))
      ( glue-join (inl-join a , c))
      ( glue-join (inr-join b , c))
      ( apd (λ x → glue-join {A = A * B} {B = C} (x , c))
        ( glue-join (a , b))) ∙
    ap
      ( glue-join (inl-join a , c) ∙_)
      ( ap-const (inr-join {A = A * B} {B = C} c) (glue-join (a , b))) ∙
    right-unit

  compute-tr-Id-right-map-right-associative-join :
    (a : A) (t : B × C)
    (q :
      inl-join (inl-join a) ＝
      map-right-associative-join (inl-join (pr1 t))) →
    tr
      ( λ y → inl-join (inl-join a) ＝ map-right-associative-join y)
      ( glue-join t)
      ( q) ＝
    q ∙ ap map-right-associative-join (glue-join t)
  compute-tr-Id-right-map-right-associative-join a t q =
    inv
      ( substitution-law-tr
        ( λ y → inl-join (inl-join a) ＝ y)
        ( map-right-associative-join)
        ( glue-join t)) ∙
    tr-Id-right (ap map-right-associative-join (glue-join t)) q

  right-transpose-compute-glue-map-right-associative-join :
    (t : B × C) →
    inv (compute-inl-map-right-associative-join (pr1 t)) ∙
    ap map-right-associative-join (glue-join t) ＝
    glue-join (inr-join (pr1 t) , pr2 t) ∙
    inv (compute-inr-map-right-associative-join (pr2 t))
  right-transpose-compute-glue-map-right-associative-join t =
    equational-reasoning
      inv linl ∙ apm
      ＝ (inv linl ∙ apm) ∙ refl
        by inv right-unit
      ＝ (inv linl ∙ apm) ∙ (rinr ∙ inv rinr)
        by ap ((inv linl ∙ apm) ∙_) (inv (right-inv rinr))
      ＝ ((inv linl ∙ apm) ∙ rinr) ∙ inv rinr
        by inv (assoc (inv linl ∙ apm) rinr (inv rinr))
      ＝ (inv linl ∙ (apm ∙ rinr)) ∙ inv rinr
        by ap (_∙ inv rinr) (assoc (inv linl) apm rinr)
      ＝ (inv linl ∙ (linl ∙ glue-inr)) ∙ inv rinr
        by ap (λ p → (inv linl ∙ p) ∙ inv rinr)
          ( compute-glue-map-right-associative-join t)
      ＝ ((inv linl ∙ linl) ∙ glue-inr) ∙ inv rinr
        by ap (_∙ inv rinr) (inv (assoc (inv linl) linl glue-inr))
      ＝ glue-inr ∙ inv rinr
        by ap (_∙ inv rinr) (ap (_∙ glue-inr) (left-inv linl))
    where
    apm = ap map-right-associative-join (glue-join t)
    linl = compute-inl-map-right-associative-join (pr1 t)
    rinr = compute-inr-map-right-associative-join (pr2 t)
    glue-inr = glue-join (inr-join (pr1 t) , pr2 t)

  coherence-right-map-associative-join :
    (a : A) (t : B × C) →
    dependent-identification
      ( λ y → inl-join (inl-join a) ＝ map-right-associative-join y)
      ( glue-join t)
      ( ap inl-join (glue-join (a , pr1 t)) ∙
        inv (compute-inl-map-right-associative-join (pr1 t)))
      ( glue-join (inl-join a , pr2 t) ∙
        inv (compute-inr-map-right-associative-join (pr2 t)))
  coherence-right-map-associative-join a t =
    equational-reasoning
      tr
        ( λ y → inl-join (inl-join a) ＝ map-right-associative-join y)
        ( glue-join t)
        ( h)
      ＝ h ∙ apm
        by compute-tr-Id-right-map-right-associative-join a t h
      ＝ (apinl ∙ inv linl) ∙ apm
        by refl
      ＝ apinl ∙ (inv linl ∙ apm)
        by assoc apinl (inv linl) apm
      ＝ apinl ∙ (glue-inr ∙ inv rinr)
        by ap (apinl ∙_)
          ( right-transpose-compute-glue-map-right-associative-join t)
      ＝ (apinl ∙ glue-inr) ∙ inv rinr
        by inv (assoc apinl glue-inr (inv rinr))
      ＝ glue-inl ∙ inv rinr
        by ap (_∙ inv rinr)
          ( naturality-glue-right-join a (pr1 t) (pr2 t))
    where
    h :
      inl-join (inl-join a) ＝
      map-right-associative-join (inl-join (pr1 t))
    h =
      ap inl-join (glue-join (a , pr1 t)) ∙
      inv (compute-inl-map-right-associative-join (pr1 t))

    apm = ap map-right-associative-join (glue-join t)
    apinl = ap inl-join (glue-join (a , pr1 t))
    linl = compute-inl-map-right-associative-join (pr1 t)
    rinr = compute-inr-map-right-associative-join (pr2 t)
    glue-inl = glue-join (inl-join a , pr2 t)
    glue-inr = glue-join (inr-join (pr1 t) , pr2 t)

  dependent-cocone-right-map-associative-join :
    (a : A) →
    dependent-cocone pr1 pr2 cocone-join
      ( λ y → inl-join (inl-join a) ＝ map-right-associative-join y)
  pr1 (dependent-cocone-right-map-associative-join a) b =
    ap inl-join (glue-join (a , b)) ∙
    inv (compute-inl-map-right-associative-join b)
  pr1 (pr2 (dependent-cocone-right-map-associative-join a)) c =
    glue-join (inl-join a , c) ∙
    inv (compute-inr-map-right-associative-join c)
  pr2 (pr2 (dependent-cocone-right-map-associative-join a)) =
    coherence-right-map-associative-join a

  coherence-map-inv-associative-join :
    (a : A) (y : B * C) →
    inl-join (inl-join a) ＝ map-right-associative-join y
  coherence-map-inv-associative-join a =
    dependent-cogap-join (dependent-cocone-right-map-associative-join a)

  cocone-inv-associative-join :
    cocone pr1 pr2 ((A * B) * C)
  pr1 cocone-inv-associative-join =
    inl-join ∘ inl-join
  pr1 (pr2 cocone-inv-associative-join) =
    map-right-associative-join
  pr2 (pr2 cocone-inv-associative-join) (a , y) =
    coherence-map-inv-associative-join a y

  map-inv-associative-join : A * (B * C) → (A * B) * C
  map-inv-associative-join =
    cogap-join ((A * B) * C) cocone-inv-associative-join

  compute-inl-map-inv-associative-join :
    map-inv-associative-join ∘ inl-join ~ inl-join ∘ inl-join
  compute-inl-map-inv-associative-join =
    compute-inl-cogap-join cocone-inv-associative-join

  compute-inr-map-inv-associative-join :
    map-inv-associative-join ∘ inr-join ~ map-right-associative-join
  compute-inr-map-inv-associative-join =
    compute-inr-cogap-join cocone-inv-associative-join

  compute-glue-map-inv-associative-join :
    statement-coherence-htpy-cocone pr1 pr2
      ( cocone-map pr1 pr2 cocone-join map-inv-associative-join)
      ( cocone-inv-associative-join)
      ( compute-inl-map-inv-associative-join)
      ( compute-inr-map-inv-associative-join)
  compute-glue-map-inv-associative-join =
    compute-glue-cogap-join cocone-inv-associative-join

  compute-inl-map-associative-map-right-associative-join :
    (b : B) →
    map-associative-join (map-right-associative-join (inl-join b)) ＝
    inr-join (inl-join b)
  compute-inl-map-associative-map-right-associative-join b =
    ap map-associative-join (compute-inl-map-right-associative-join b) ∙
    compute-inl-map-associative-join (inr-join b) ∙
    compute-inr-map-left-associative-join b

  compute-inr-map-associative-map-right-associative-join :
    (c : C) →
    map-associative-join (map-right-associative-join (inr-join c)) ＝
    inr-join (inr-join c)
  compute-inr-map-associative-map-right-associative-join c =
    ap map-associative-join (compute-inr-map-right-associative-join c) ∙
    compute-inr-map-associative-join c

  coherence-map-associative-map-right-associative-join :
    (t : B × C) →
    dependent-identification
      ( λ y → map-associative-join (map-right-associative-join y) ＝ inr-join y)
      ( glue-join t)
      ( compute-inl-map-associative-map-right-associative-join (pr1 t))
      ( compute-inr-map-associative-map-right-associative-join (pr2 t))
  coherence-map-associative-map-right-associative-join t =
    map-compute-dependent-identification-eq-value-function
      ( map-associative-join ∘ map-right-associative-join)
      ( inr-join)
      ( glue-join t)
      ( compute-inl-map-associative-map-right-associative-join (pr1 t))
      ( compute-inr-map-associative-map-right-associative-join (pr2 t))
      ( equational-reasoning
        ap (map-associative-join ∘ map-right-associative-join) p ∙ r
        ＝ ap map-associative-join (ap map-right-associative-join p) ∙ r
          by ap (_∙ r)
            ( ap-comp map-associative-join map-right-associative-join p)
        ＝ ( ap map-associative-join (ap map-right-associative-join p) ∙
            ap map-associative-join rinr) ∙
            ainr
          by inv
            ( assoc
              ( ap map-associative-join (ap map-right-associative-join p))
              ( ap map-associative-join rinr)
              ( ainr))
        ＝ ap map-associative-join
            ( ap map-right-associative-join p ∙ rinr) ∙
            ainr
          by ap (_∙ ainr)
            ( inv
              ( ap-concat
                ( map-associative-join)
                ( ap map-right-associative-join p)
                ( rinr)))
        ＝ ap map-associative-join (rinl ∙ glueR) ∙ ainr
          by ap (λ q → ap map-associative-join q ∙ ainr)
            ( compute-glue-map-right-associative-join t)
        ＝ ( ap map-associative-join rinl ∙
            ap map-associative-join glueR) ∙
            ainr
          by ap (_∙ ainr)
            ( ap-concat map-associative-join rinl glueR)
        ＝ ap map-associative-join rinl ∙
            ( ap map-associative-join glueR ∙ ainr)
          by assoc
            ( ap map-associative-join rinl)
            ( ap map-associative-join glueR)
            ( ainr)
        ＝ ap map-associative-join rinl ∙
            ( ainl ∙ coherence-map-associative-join (inr-join b) c)
          by ap (ap map-associative-join rinl ∙_)
            ( compute-glue-map-associative-join (inr-join b , c))
        ＝ ap map-associative-join rinl ∙ (ainl ∙ (linr ∙ apinr))
          by ap
            ( λ q → ap map-associative-join rinl ∙ (ainl ∙ q))
            ( compute-inr-coherence-map-associative-join b c)
        ＝ ap map-associative-join rinl ∙ ((ainl ∙ linr) ∙ apinr)
          by ap (ap map-associative-join rinl ∙_)
            ( inv (assoc ainl linr apinr))
        ＝ (ap map-associative-join rinl ∙ (ainl ∙ linr)) ∙ apinr
          by inv (assoc (ap map-associative-join rinl) (ainl ∙ linr) apinr)
        ＝ ((ap map-associative-join rinl ∙ ainl) ∙ linr) ∙ apinr
          by ap (_∙ apinr)
            ( inv (assoc (ap map-associative-join rinl) ainl linr)))
    where
    b = pr1 t
    c = pr2 t
    p = glue-join t
    rinl = compute-inl-map-right-associative-join b
    rinr = compute-inr-map-right-associative-join c
    ainl = compute-inl-map-associative-join (inr-join b)
    ainr = compute-inr-map-associative-join c
    linr = compute-inr-map-left-associative-join b
    glueR = glue-join (inr-join b , c)
    apinr = ap inr-join p
    r = ap map-associative-join rinr ∙ ainr

  dependent-cocone-map-associative-map-right-associative-join :
    dependent-cocone pr1 pr2 cocone-join
      ( λ y → map-associative-join (map-right-associative-join y) ＝
        inr-join y)
  pr1 dependent-cocone-map-associative-map-right-associative-join =
    compute-inl-map-associative-map-right-associative-join
  pr1 (pr2 dependent-cocone-map-associative-map-right-associative-join) =
    compute-inr-map-associative-map-right-associative-join
  pr2 (pr2 dependent-cocone-map-associative-map-right-associative-join) =
    coherence-map-associative-map-right-associative-join

  compute-map-associative-map-right-associative-join :
    map-associative-join ∘ map-right-associative-join ~ inr-join
  compute-map-associative-map-right-associative-join =
    dependent-cogap-join
      dependent-cocone-map-associative-map-right-associative-join

  compute-inl-map-inv-map-left-associative-join :
    (a : A) →
    map-inv-associative-join (map-left-associative-join (inl-join a)) ＝
    inl-join (inl-join a)
  compute-inl-map-inv-map-left-associative-join a =
    ap map-inv-associative-join (compute-inl-map-left-associative-join a) ∙
    compute-inl-map-inv-associative-join a

  compute-inr-map-inv-map-left-associative-join :
    (b : B) →
    map-inv-associative-join (map-left-associative-join (inr-join b)) ＝
    inl-join (inr-join b)
  compute-inr-map-inv-map-left-associative-join b =
    ( ap map-inv-associative-join
      ( compute-inr-map-left-associative-join b) ∙
      compute-inr-map-inv-associative-join (inl-join b)) ∙
    compute-inl-map-right-associative-join b

  coherence-map-inv-map-left-associative-join :
    (t : A × B) →
    dependent-identification
      ( λ x → map-inv-associative-join (map-left-associative-join x) ＝
        inl-join x)
      ( glue-join t)
      ( compute-inl-map-inv-map-left-associative-join (pr1 t))
      ( compute-inr-map-inv-map-left-associative-join (pr2 t))
  coherence-map-inv-map-left-associative-join t =
    map-compute-dependent-identification-eq-value-function
      ( map-inv-associative-join ∘ map-left-associative-join)
      ( inl-join)
      ( glue-join t)
      ( compute-inl-map-inv-map-left-associative-join a)
      ( compute-inr-map-inv-map-left-associative-join b)
      ( equational-reasoning
        ap (map-inv-associative-join ∘ map-left-associative-join) p ∙ r
        ＝ ap map-inv-associative-join (ap map-left-associative-join p) ∙ r
          by ap (_∙ r)
            ( ap-comp
              ( map-inv-associative-join)
              ( map-left-associative-join)
              ( p))
        ＝ ap map-inv-associative-join (ap map-left-associative-join p) ∙
            (ap map-inv-associative-join linr ∙ (finr ∙ rinl))
          by ap
            ( ap map-inv-associative-join (ap map-left-associative-join p) ∙_)
            ( assoc (ap map-inv-associative-join linr) finr rinl)
        ＝ ( ap map-inv-associative-join (ap map-left-associative-join p) ∙
            ap map-inv-associative-join linr) ∙ (finr ∙ rinl)
          by inv
            ( assoc
              ( ap map-inv-associative-join
                ( ap map-left-associative-join p))
              ( ap map-inv-associative-join linr)
              ( finr ∙ rinl))
        ＝ ap map-inv-associative-join
            ( ap map-left-associative-join p ∙ linr) ∙
            ( finr ∙ rinl)
          by ap (_∙ (finr ∙ rinl))
            ( inv
              ( ap-concat
                ( map-inv-associative-join)
                ( ap map-left-associative-join p)
                ( linr)))
        ＝ ap map-inv-associative-join (linl ∙ glueOuter) ∙
            ( finr ∙ rinl)
          by ap (λ q → ap map-inv-associative-join q ∙ (finr ∙ rinl))
            ( compute-glue-map-left-associative-join t)
        ＝ (ap map-inv-associative-join linl ∙
            ap map-inv-associative-join glueOuter) ∙
            ( finr ∙ rinl)
          by ap (_∙ (finr ∙ rinl))
            ( ap-concat map-inv-associative-join linl glueOuter)
        ＝ ap map-inv-associative-join linl ∙
            ( ap map-inv-associative-join glueOuter ∙ (finr ∙ rinl))
          by assoc
            ( ap map-inv-associative-join linl)
            ( ap map-inv-associative-join glueOuter)
            ( finr ∙ rinl)
        ＝ ap map-inv-associative-join linl ∙
            ((ap map-inv-associative-join glueOuter ∙ finr) ∙ rinl)
          by ap (ap map-inv-associative-join linl ∙_)
            ( inv (assoc (ap map-inv-associative-join glueOuter) finr rinl))
        ＝ ap map-inv-associative-join linl ∙
            ((finl ∙ coherence-map-inv-associative-join a (inl-join b)) ∙
              rinl)
          by ap
            ( λ q → ap map-inv-associative-join linl ∙ (q ∙ rinl))
            ( compute-glue-map-inv-associative-join (a , inl-join b))
        ＝ ap map-inv-associative-join linl ∙
            ((finl ∙ (apinl ∙ inv rinl)) ∙ rinl)
          by ap
            ( λ q →
              ap map-inv-associative-join linl ∙
              ((finl ∙ q) ∙ rinl))
            ( compute-inl-dependent-cogap-join
              ( dependent-cocone-right-map-associative-join a)
              ( b))
        ＝ ap map-inv-associative-join linl ∙
            (finl ∙ ((apinl ∙ inv rinl) ∙ rinl))
          by ap (ap map-inv-associative-join linl ∙_)
            ( assoc finl (apinl ∙ inv rinl) rinl)
        ＝ ap map-inv-associative-join linl ∙
            (finl ∙ (apinl ∙ (inv rinl ∙ rinl)))
          by ap (λ q → ap map-inv-associative-join linl ∙ (finl ∙ q))
            ( assoc apinl (inv rinl) rinl)
        ＝ ap map-inv-associative-join linl ∙
            (finl ∙ (apinl ∙ refl))
          by ap
            ( λ q →
              ap map-inv-associative-join linl ∙ (finl ∙ (apinl ∙ q)))
            ( left-inv rinl)
        ＝ ap map-inv-associative-join linl ∙
            (finl ∙ apinl)
          by ap (λ q → ap map-inv-associative-join linl ∙ (finl ∙ q))
            ( right-unit)
        ＝ (ap map-inv-associative-join linl ∙ finl) ∙ apinl
          by inv (assoc (ap map-inv-associative-join linl) finl apinl))
    where
    a = pr1 t
    b = pr2 t
    p = glue-join t
    linl = compute-inl-map-left-associative-join a
    linr = compute-inr-map-left-associative-join b
    finl = compute-inl-map-inv-associative-join a
    finr = compute-inr-map-inv-associative-join (inl-join b)
    rinl = compute-inl-map-right-associative-join b
    glueOuter = glue-join (a , inl-join b)
    apinl = ap inl-join p
    r = compute-inr-map-inv-map-left-associative-join b

  dependent-cocone-map-inv-map-left-associative-join :
    dependent-cocone pr1 pr2 cocone-join
      ( λ x → map-inv-associative-join (map-left-associative-join x) ＝
        inl-join x)
  pr1 dependent-cocone-map-inv-map-left-associative-join =
    compute-inl-map-inv-map-left-associative-join
  pr1 (pr2 dependent-cocone-map-inv-map-left-associative-join) =
    compute-inr-map-inv-map-left-associative-join
  pr2 (pr2 dependent-cocone-map-inv-map-left-associative-join) =
    coherence-map-inv-map-left-associative-join

  compute-map-inv-map-left-associative-join :
    map-inv-associative-join ∘ map-left-associative-join ~ inl-join
  compute-map-inv-map-left-associative-join =
    dependent-cogap-join dependent-cocone-map-inv-map-left-associative-join

  compute-inl-map-inv-map-associative-join :
    (x : A * B) →
    map-inv-associative-join (map-associative-join (inl-join x)) ＝
    inl-join x
  compute-inl-map-inv-map-associative-join x =
    ap map-inv-associative-join (compute-inl-map-associative-join x) ∙
    compute-map-inv-map-left-associative-join x

  compute-inr-map-inv-map-associative-join :
    (c : C) →
    map-inv-associative-join (map-associative-join (inr-join c)) ＝
    inr-join c
  compute-inr-map-inv-map-associative-join c =
    ( ap map-inv-associative-join
      ( compute-inr-map-associative-join c) ∙
      compute-inr-map-inv-associative-join (inr-join c)) ∙
    compute-inr-map-right-associative-join c

  triangle-family-map-inv-coherence-map-associative-join :
    (x : A * B) (c : C) → UU (l1 ⊔ l2 ⊔ l3)
  triangle-family-map-inv-coherence-map-associative-join x c =
    ap map-inv-associative-join (coherence-map-associative-join x c) ∙
    ( compute-inr-map-inv-associative-join (inr-join c) ∙
      compute-inr-map-right-associative-join c) ＝
    compute-map-inv-map-left-associative-join x ∙
    ap id (glue-join (x , c))

  compute-inl-triangle-map-inv-coherence-map-associative-join :
    (a : A) (c : C) →
    triangle-family-map-inv-coherence-map-associative-join
      ( inl-join a)
      ( c)
  compute-inl-triangle-map-inv-coherence-map-associative-join a c =
    equational-reasoning
      ap map-inv-associative-join coh ∙ (finr ∙ rinr)
      ＝ ap map-inv-associative-join (linl ∙ glueOuter) ∙ (finr ∙ rinr)
        by ap (λ q → ap map-inv-associative-join q ∙ (finr ∙ rinr))
          ( compute-inl-coherence-map-associative-join a c)
      ＝ (ap map-inv-associative-join linl ∙
          ap map-inv-associative-join glueOuter) ∙
          ( finr ∙ rinr)
        by ap (_∙ (finr ∙ rinr))
          ( ap-concat map-inv-associative-join linl glueOuter)
      ＝ ap map-inv-associative-join linl ∙
          (ap map-inv-associative-join glueOuter ∙ (finr ∙ rinr))
        by assoc
          ( ap map-inv-associative-join linl)
          ( ap map-inv-associative-join glueOuter)
          ( finr ∙ rinr)
      ＝ ap map-inv-associative-join linl ∙
          ((ap map-inv-associative-join glueOuter ∙ finr) ∙ rinr)
        by ap (ap map-inv-associative-join linl ∙_)
          ( inv (assoc (ap map-inv-associative-join glueOuter) finr rinr))
      ＝ ap map-inv-associative-join linl ∙
          ((finl ∙ coherence-map-inv-associative-join a (inr-join c)) ∙
            rinr)
        by ap
          ( λ q → ap map-inv-associative-join linl ∙ (q ∙ rinr))
          ( compute-glue-map-inv-associative-join (a , inr-join c))
      ＝ ap map-inv-associative-join linl ∙
          ((finl ∙ (glueOuter' ∙ inv rinr)) ∙ rinr)
        by ap
          ( λ q →
            ap map-inv-associative-join linl ∙ ((finl ∙ q) ∙ rinr))
          ( compute-inr-dependent-cogap-join
            ( dependent-cocone-right-map-associative-join a)
            ( c))
      ＝ ap map-inv-associative-join linl ∙
          (finl ∙ ((glueOuter' ∙ inv rinr) ∙ rinr))
        by ap (ap map-inv-associative-join linl ∙_)
          ( assoc finl (glueOuter' ∙ inv rinr) rinr)
      ＝ ap map-inv-associative-join linl ∙
          (finl ∙ (glueOuter' ∙ (inv rinr ∙ rinr)))
        by ap
          ( λ q → ap map-inv-associative-join linl ∙ (finl ∙ q))
          ( assoc glueOuter' (inv rinr) rinr)
      ＝ ap map-inv-associative-join linl ∙
          (finl ∙ (glueOuter' ∙ refl))
        by ap
          ( λ q →
            ap map-inv-associative-join linl ∙ (finl ∙ (glueOuter' ∙ q)))
          ( left-inv rinr)
      ＝ ap map-inv-associative-join linl ∙ (finl ∙ glueOuter')
        by ap (λ q → ap map-inv-associative-join linl ∙ (finl ∙ q))
          ( right-unit)
      ＝ (ap map-inv-associative-join linl ∙ finl) ∙ glueOuter'
        by inv (assoc (ap map-inv-associative-join linl) finl glueOuter')
      ＝ (ap map-inv-associative-join linl ∙ finl) ∙ ap id glueOuter'
        by ap
          ( λ q → (ap map-inv-associative-join linl ∙ finl) ∙ q)
          ( inv (ap-id glueOuter'))
      ＝ compute-map-inv-map-left-associative-join (inl-join a) ∙
          ap id glueOuter'
        by ap (_∙ ap id glueOuter')
          ( inv
            ( compute-inl-dependent-cogap-join
              ( dependent-cocone-map-inv-map-left-associative-join)
              ( a)))
    where
    coh = coherence-map-associative-join (inl-join a) c
    linl = compute-inl-map-left-associative-join a
    finl = compute-inl-map-inv-associative-join a
    finr = compute-inr-map-inv-associative-join (inr-join c)
    rinr = compute-inr-map-right-associative-join c
    glueOuter = glue-join (a , inr-join c)
    glueOuter' = glue-join (inl-join a , c)

  compute-inr-triangle-map-inv-coherence-map-associative-join :
    (b : B) (c : C) →
    triangle-family-map-inv-coherence-map-associative-join
      ( inr-join b)
      ( c)
  compute-inr-triangle-map-inv-coherence-map-associative-join b c =
    equational-reasoning
      ap map-inv-associative-join coh ∙ (finr ∙ rinr)
      ＝ ap map-inv-associative-join (linr ∙ apinr) ∙ (finr ∙ rinr)
        by ap (λ q → ap map-inv-associative-join q ∙ (finr ∙ rinr))
          ( compute-inr-coherence-map-associative-join b c)
      ＝ (ap map-inv-associative-join linr ∙
          ap map-inv-associative-join apinr) ∙
          ( finr ∙ rinr)
        by ap (_∙ (finr ∙ rinr))
          ( ap-concat map-inv-associative-join linr apinr)
      ＝ ap map-inv-associative-join linr ∙
          (ap map-inv-associative-join apinr ∙ (finr ∙ rinr))
        by assoc
          ( ap map-inv-associative-join linr)
          ( ap map-inv-associative-join apinr)
          ( finr ∙ rinr)
      ＝ ap map-inv-associative-join linr ∙
          ((ap map-inv-associative-join apinr ∙ finr) ∙ rinr)
        by ap (ap map-inv-associative-join linr ∙_)
          ( inv (assoc (ap map-inv-associative-join apinr) finr rinr))
      ＝ ap map-inv-associative-join linr ∙
          ((ap (map-inv-associative-join ∘ inr-join) p ∙ finr) ∙ rinr)
        by ap
          ( λ q → ap map-inv-associative-join linr ∙ ((q ∙ finr) ∙ rinr))
          ( inv (ap-comp map-inv-associative-join inr-join p))
      ＝ ap map-inv-associative-join linr ∙
          ((finl ∙ ap map-right-associative-join p) ∙ rinr)
        by ap
          ( λ q → ap map-inv-associative-join linr ∙ (q ∙ rinr))
          ( naturality-homotopy compute-inr-map-inv-associative-join p)
      ＝ ap map-inv-associative-join linr ∙
          (finl ∙ (ap map-right-associative-join p ∙ rinr))
        by ap (ap map-inv-associative-join linr ∙_)
          ( assoc finl (ap map-right-associative-join p) rinr)
      ＝ ap map-inv-associative-join linr ∙
          (finl ∙ (rinl ∙ glueOuter))
        by ap (λ q → ap map-inv-associative-join linr ∙ (finl ∙ q))
          ( compute-glue-map-right-associative-join (b , c))
      ＝ ap map-inv-associative-join linr ∙
          ((finl ∙ rinl) ∙ glueOuter)
        by ap (ap map-inv-associative-join linr ∙_)
          ( inv (assoc finl rinl glueOuter))
      ＝ (ap map-inv-associative-join linr ∙ (finl ∙ rinl)) ∙ glueOuter
        by inv
          ( assoc
            ( ap map-inv-associative-join linr)
            ( finl ∙ rinl)
            ( glueOuter))
      ＝ ((ap map-inv-associative-join linr ∙ finl) ∙ rinl) ∙ glueOuter
        by ap (_∙ glueOuter)
          ( inv (assoc (ap map-inv-associative-join linr) finl rinl))
      ＝ ((ap map-inv-associative-join linr ∙ finl) ∙ rinl) ∙
          ap id glueOuter
        by ap
          ( λ q → ((ap map-inv-associative-join linr ∙ finl) ∙ rinl) ∙ q)
          ( inv (ap-id glueOuter))
      ＝ compute-map-inv-map-left-associative-join (inr-join b) ∙
          ap id glueOuter
        by ap (_∙ ap id glueOuter)
          ( inv
            ( compute-inr-dependent-cogap-join
              ( dependent-cocone-map-inv-map-left-associative-join)
              ( b)))
    where
    p = glue-join (b , c)
    coh = coherence-map-associative-join (inr-join b) c
    linr = compute-inr-map-left-associative-join b
    finl = compute-inr-map-inv-associative-join (inl-join b)
    finr = compute-inr-map-inv-associative-join (inr-join c)
    rinl = compute-inl-map-right-associative-join b
    rinr = compute-inr-map-right-associative-join c
    apinr = ap inr-join p
    glueOuter = glue-join (inr-join b , c)

  compute-inl-map-associative-map-inv-associative-join :
    (a : A) →
    map-associative-join (map-inv-associative-join (inl-join a)) ＝
    inl-join a
  compute-inl-map-associative-map-inv-associative-join a =
    ap map-associative-join (compute-inl-map-inv-associative-join a) ∙
    compute-inl-map-associative-join (inl-join a) ∙
    compute-inl-map-left-associative-join a

  compute-inr-map-associative-map-inv-associative-join :
    (y : B * C) →
    map-associative-join (map-inv-associative-join (inr-join y)) ＝
    inr-join y
  compute-inr-map-associative-map-inv-associative-join y =
    ap map-associative-join (compute-inr-map-inv-associative-join y) ∙
    compute-map-associative-map-right-associative-join y

  triangle-family-map-associative-coherence-map-inv-associative-join :
    (a : A) (y : B * C) → UU (l1 ⊔ l2 ⊔ l3)
  triangle-family-map-associative-coherence-map-inv-associative-join a y =
    ap map-associative-join (coherence-map-inv-associative-join a y) ∙
    compute-map-associative-map-right-associative-join y ＝
    ( compute-inl-map-associative-join (inl-join a) ∙
      compute-inl-map-left-associative-join a) ∙
    ap id (glue-join (a , y))

  compute-inl-triangle-map-associative-coherence-map-inv-associative-join :
    (a : A) (b : B) →
    triangle-family-map-associative-coherence-map-inv-associative-join
      a (inl-join b)
  compute-inl-triangle-map-associative-coherence-map-inv-associative-join a b =
    equational-reasoning
      ap map-associative-join coh ∙ H
      ＝ ap map-associative-join (apinl ∙ inv rinl) ∙ H
        by ap (λ q → ap map-associative-join q ∙ H)
          ( compute-inl-dependent-cogap-join
            ( dependent-cocone-right-map-associative-join a)
            ( b))
      ＝ ap map-associative-join (apinl ∙ inv rinl) ∙
          ((Q ∙ ainl) ∙ linr)
        by ap (ap map-associative-join (apinl ∙ inv rinl) ∙_)
          ( compute-inl-dependent-cogap-join
            ( dependent-cocone-map-associative-map-right-associative-join)
            ( b))
      ＝ (P ∙ ap map-associative-join (inv rinl)) ∙
          ((Q ∙ ainl) ∙ linr)
        by ap (_∙ ((Q ∙ ainl) ∙ linr))
          ( ap-concat map-associative-join apinl (inv rinl))
      ＝ (P ∙ inv Q) ∙ ((Q ∙ ainl) ∙ linr)
        by ap (λ q → (P ∙ q) ∙ ((Q ∙ ainl) ∙ linr))
          ( ap-inv map-associative-join rinl)
      ＝ P ∙ (inv Q ∙ ((Q ∙ ainl) ∙ linr))
        by assoc P (inv Q) ((Q ∙ ainl) ∙ linr)
      ＝ P ∙ ((inv Q ∙ (Q ∙ ainl)) ∙ linr)
        by ap (P ∙_) (inv (assoc (inv Q) (Q ∙ ainl) linr))
      ＝ P ∙ (((inv Q ∙ Q) ∙ ainl) ∙ linr)
        by ap (λ q → P ∙ (q ∙ linr)) (inv (assoc (inv Q) Q ainl))
      ＝ P ∙ ((refl ∙ ainl) ∙ linr)
        by ap (λ q → P ∙ ((q ∙ ainl) ∙ linr)) (left-inv Q)
      ＝ P ∙ (ainl ∙ linr)
        by ap (P ∙_) (ap (_∙ linr) left-unit)
      ＝ (P ∙ ainl) ∙ linr
        by inv (assoc P ainl linr)
      ＝ (ap (map-associative-join ∘ inl-join) glueAB ∙ ainl) ∙ linr
        by ap (λ q → (q ∙ ainl) ∙ linr)
          ( inv (ap-comp map-associative-join inl-join glueAB))
      ＝ (finl ∙ ap map-left-associative-join glueAB) ∙ linr
        by ap (_∙ linr)
          ( naturality-homotopy compute-inl-map-associative-join glueAB)
      ＝ finl ∙ (ap map-left-associative-join glueAB ∙ linr)
        by assoc finl (ap map-left-associative-join glueAB) linr
      ＝ finl ∙ (linl ∙ glueOuter)
        by ap (finl ∙_) (compute-glue-map-left-associative-join (a , b))
      ＝ finl ∙ (linl ∙ ap id glueOuter)
        by ap (λ q → finl ∙ (linl ∙ q)) (inv (ap-id glueOuter))
      ＝ (finl ∙ linl) ∙ ap id glueOuter
        by inv (assoc finl linl (ap id glueOuter))
    where
    coh = coherence-map-inv-associative-join a (inl-join b)
    H = compute-map-associative-map-right-associative-join (inl-join b)
    rinl = compute-inl-map-right-associative-join b
    ainl = compute-inl-map-associative-join (inr-join b)
    linr = compute-inr-map-left-associative-join b
    finl = compute-inl-map-associative-join (inl-join a)
    linl = compute-inl-map-left-associative-join a
    glueAB = glue-join (a , b)
    glueOuter = glue-join (a , inl-join b)
    apinl = ap inl-join glueAB
    P = ap map-associative-join apinl
    Q = ap map-associative-join rinl

  compute-inr-triangle-map-associative-coherence-map-inv-associative-join :
    (a : A) (c : C) →
    triangle-family-map-associative-coherence-map-inv-associative-join
      a (inr-join c)
  compute-inr-triangle-map-associative-coherence-map-inv-associative-join a c =
    equational-reasoning
      ap map-associative-join coh ∙ H
      ＝ ap map-associative-join (glueAC ∙ inv rinr) ∙ H
        by ap (λ q → ap map-associative-join q ∙ H)
          ( compute-inr-dependent-cogap-join
            ( dependent-cocone-right-map-associative-join a)
            ( c))
      ＝ ap map-associative-join (glueAC ∙ inv rinr) ∙ (Q ∙ finr)
        by ap (ap map-associative-join (glueAC ∙ inv rinr) ∙_)
          ( compute-inr-dependent-cogap-join
            ( dependent-cocone-map-associative-map-right-associative-join)
            ( c))
      ＝ (P ∙ ap map-associative-join (inv rinr)) ∙ (Q ∙ finr)
        by ap (_∙ (Q ∙ finr))
          ( ap-concat map-associative-join glueAC (inv rinr))
      ＝ (P ∙ inv Q) ∙ (Q ∙ finr)
        by ap (λ q → (P ∙ q) ∙ (Q ∙ finr))
          ( ap-inv map-associative-join rinr)
      ＝ P ∙ (inv Q ∙ (Q ∙ finr))
        by assoc P (inv Q) (Q ∙ finr)
      ＝ P ∙ ((inv Q ∙ Q) ∙ finr)
        by ap (P ∙_) (inv (assoc (inv Q) Q finr))
      ＝ P ∙ (refl ∙ finr)
        by ap (λ q → P ∙ (q ∙ finr)) (left-inv Q)
      ＝ P ∙ finr
        by ap (P ∙_) left-unit
      ＝ finl ∙ coherence-map-associative-join (inl-join a) c
        by compute-glue-map-associative-join (inl-join a , c)
      ＝ finl ∙ (linl ∙ glueOuter)
        by ap (finl ∙_) (compute-inl-coherence-map-associative-join a c)
      ＝ finl ∙ (linl ∙ ap id glueOuter)
        by ap (λ q → finl ∙ (linl ∙ q)) (inv (ap-id glueOuter))
      ＝ (finl ∙ linl) ∙ ap id glueOuter
        by inv (assoc finl linl (ap id glueOuter))
    where
    coh = coherence-map-inv-associative-join a (inr-join c)
    H = compute-map-associative-map-right-associative-join (inr-join c)
    rinr = compute-inr-map-right-associative-join c
    finr = compute-inr-map-associative-join c
    finl = compute-inl-map-associative-join (inl-join a)
    linl = compute-inl-map-left-associative-join a
    glueAC = glue-join (inl-join a , c)
    glueOuter = glue-join (a , inr-join c)
    P = ap map-associative-join glueAC
    Q = ap map-associative-join rinr

```
