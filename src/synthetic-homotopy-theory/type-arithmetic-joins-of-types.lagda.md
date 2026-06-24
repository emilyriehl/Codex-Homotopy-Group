# Type arithmetic for joins of types

```agda
module synthetic-homotopy-theory.type-arithmetic-joins-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-identifications
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.dependent-identifications
open import foundation.constant-type-families
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-extensionality-axiom
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-dependent-function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-dependent-function-types
open import foundation.transport-along-homotopies
open import foundation.transport-along-identifications
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
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
naturality-homotopy H p = inv (nat-htpy H p)

naturality-constant-homotopy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {x : B} {j : A → B} (H : (a : A) → x ＝ j a)
  {a a' : A} (p : a ＝ a') →
  H a ∙ ap j p ＝ H a'
naturality-constant-homotopy {x = x} H p =
  inv (naturality-homotopy H p) ∙
  ap (_∙ H _) (ap-const x p) ∙
  left-unit

postcompose-naturality-constant-homotopy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {x : B} {j : A → B} (h : B → C) (H : (a : A) → x ＝ j a)
  {a a' : A} (p : a ＝ a') →
  naturality-constant-homotopy (λ y → ap h (H y)) p ＝
  ap (ap h (H a) ∙_) (ap-comp h j p) ∙
  inv (ap-concat h (H a) (ap j p)) ∙
  ap (ap h) (naturality-constant-homotopy H p)
postcompose-naturality-constant-homotopy {j = j} h H {a} refl
  with H a
... | refl = refl

coherence-twist-twist-identification :
  {l1 : Level} {X : UU l1} {x y z : X}
  (p : x ＝ y) (q : y ＝ z) (r : x ＝ z) →
  (s : p ∙ q ＝ r) →
  tr
    ( λ h → h ∙ q ＝ r)
    ( inv-inv p)
    ( inv
      ( left-transpose-eq-concat
        ( inv p)
        ( r)
        ( q)
        ( inv (left-transpose-eq-concat p q r s)))) ＝
  s
coherence-twist-twist-identification refl q r s = inv-inv s

compute-dependent-identification-eq-value-function-naturality :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f g : X → Y}
  (H : f ~ g) {x y : X} (p : x ＝ y) →
  map-compute-dependent-identification-eq-value-function
    ( f)
    ( g)
    ( p)
    ( H x)
    ( H y)
    ( naturality-homotopy H p) ＝
  apd H p
compute-dependent-identification-eq-value-function-naturality
  H {x} {y} p =
  ap
    ( map-equiv
      ( compute-dependent-identification-eq-value-function
        _ _
        p
        ( H x)
        ( H y)))
    ( inv (nat-htpy-apd-htpy _ _ H p)) ∙
  is-section-map-inv-equiv
    ( compute-dependent-identification-eq-value-function
      _ _
      p
      ( H x)
      ( H y))
    ( apd H p)

apd-concat :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {x y z : A} (p : x ＝ y) (q : y ＝ z) →
  apd f (p ∙ q) ＝
  concat-dependent-identification B p q (apd f p) (apd f q)
apd-concat f refl q = refl

map-compute-dependent-identification-dependent-function-type-fixed-domain :
  {l1 l2 l3 : Level} {X : UU l1} {D : UU l2}
  (P : X → D → UU l3) {x y : X} →
  (p : x ＝ y) (h : (d : D) → P x d) (k : (d : D) → P y d) →
  ((d : D) → tr (λ z → P z d) p (h d) ＝ k d) →
  dependent-identification (λ z → (d : D) → P z d) p h k
map-compute-dependent-identification-dependent-function-type-fixed-domain
  P refl h k H =
  eq-htpy H

map-compute-dependent-identification-dependent-function-type-three-fixed-domains :
  {l1 l2 l3 l4 l5 : Level}
  {X : UU l1} {D : UU l2} {E : UU l3} {F : UU l4}
  (P : X → D → E → F → UU l5) {x y : X} →
  (p : x ＝ y)
  (h : (d : D) (e : E) (f : F) → P x d e f)
  (k : (d : D) (e : E) (f : F) → P y d e f) →
  ( (d : D) (e : E) (f : F) →
    tr (λ z → P z d e f) p (h d e f) ＝ k d e f) →
  dependent-identification
    ( λ z → (d : D) (e : E) (f : F) → P z d e f)
    ( p)
    ( h)
    ( k)
map-compute-dependent-identification-dependent-function-type-three-fixed-domains
  P p h k H =
  map-compute-dependent-identification-dependent-function-type-fixed-domain
    ( λ z d → (e : _) (f : _) → P z d e f)
    ( p)
    ( h)
    ( k)
    ( λ d →
      map-compute-dependent-identification-dependent-function-type-fixed-domain
        ( λ z e → (f : _) → P z d e f)
        ( p)
        ( h d)
        ( k d)
        ( λ e →
          map-compute-dependent-identification-dependent-function-type-fixed-domain
            ( λ z f → P z d e f)
            ( p)
            ( h d e)
            ( k d e)
            ( H d e)))

right-whisker-concat-dependent-identification :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {b b' : B} (r : b ＝ b') →
  {x y : A} (p : x ＝ y) {q : f x ＝ b} {q' : f y ＝ b} →
  dependent-identification (λ z → f z ＝ b) p q q' →
  dependent-identification (λ z → f z ＝ b') p (q ∙ r) (q' ∙ r)
right-whisker-concat-dependent-identification r refl H =
  ap (_∙ r) H

concat-dependent-identification-eq-value :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g h : A → B} {x y : A} (p : x ＝ y) →
  {H : f x ＝ g x} {H' : f y ＝ g y}
  {K : g x ＝ h x} {K' : g y ＝ h y} →
  dependent-identification (eq-value-function f g) p H H' →
  dependent-identification (eq-value-function g h) p K K' →
  dependent-identification
    ( eq-value-function f h)
    ( p)
    ( H ∙ K)
    ( H' ∙ K')
concat-dependent-identification-eq-value refl L M =
  ap-binary _∙_ L M

concat-dependent-identification-eq-value-function :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g h : A → B} (H : f ~ g) (K : g ~ h) →
  {x y : A} (p : x ＝ y) →
  dependent-identification (eq-value-function f g) p (H x) (H y) →
  dependent-identification (eq-value-function g h) p (K x) (K y) →
  dependent-identification
    ( eq-value-function f h)
    ( p)
    ( H x ∙ K x)
    ( H y ∙ K y)
concat-dependent-identification-eq-value-function H K p L M =
  concat-dependent-identification-eq-value p L M

apd-right-whisker-concat-dependent-identification :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {b b' : B} (H : (x : A) → f x ＝ b)
  (r : b ＝ b') {x y : A} (p : x ＝ y) →
  apd (λ z → H z ∙ r) p ＝
  right-whisker-concat-dependent-identification r p (apd H p)
apd-right-whisker-concat-dependent-identification H r refl = refl

coherence-right-whisker-concat-dependent-identification :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {b b' : B} (r : b ＝ b')
  (H : (x : A) → f x ＝ b) {x y : A} (p : x ＝ y)
  {u : f x ＝ b} {v : f y ＝ b}
  (L : H x ＝ u) (K : H y ＝ v)
  (M : dependent-identification (λ z → f z ＝ b) p u v) →
  apd H p ∙ K ＝ ap (tr (λ z → f z ＝ b) p) L ∙ M →
  right-whisker-concat-dependent-identification r p (apd H p) ∙
  ap (_∙ r) K ＝
  ap (tr (λ z → f z ＝ b') p) (ap (_∙ r) L) ∙
  right-whisker-concat-dependent-identification r p M
coherence-right-whisker-concat-dependent-identification r H refl refl refl M C =
  ap (ap (_∙ r)) C

pasting-dependent-identification-square :
  {l1 l2 : Level} {A : UU l1} {P : A → UU l2}
  {x y : A} (p : x ＝ y)
  {u v w : P x} {u' v' w' : P y}
  (L : dependent-identification P p u u')
  (M : dependent-identification P p v v')
  (R : dependent-identification P p w w')
  (α : u ＝ v) (β : u' ＝ v')
  (γ : v ＝ w) (δ : v' ＝ w') →
  L ∙ β ＝ ap (tr P p) α ∙ M →
  M ∙ δ ＝ ap (tr P p) γ ∙ R →
  L ∙ (β ∙ δ) ＝ ap (tr P p) (α ∙ γ) ∙ R
pasting-dependent-identification-square p L M R α β γ δ S T =
  equational-reasoning
    L ∙ (β ∙ δ)
    ＝ (L ∙ β) ∙ δ
      by inv (assoc L β δ)
    ＝ (ap (tr _ p) α ∙ M) ∙ δ
      by ap (_∙ δ) S
    ＝ ap (tr _ p) α ∙ (M ∙ δ)
      by assoc (ap (tr _ p) α) M δ
    ＝ ap (tr _ p) α ∙ (ap (tr _ p) γ ∙ R)
      by ap (ap (tr _ p) α ∙_) T
    ＝ (ap (tr _ p) α ∙ ap (tr _ p) γ) ∙ R
      by inv (assoc (ap (tr _ p) α) (ap (tr _ p) γ) R)
    ＝ ap (tr _ p) (α ∙ γ) ∙ R
      by ap (_∙ R) (inv (ap-concat (tr _ p) α γ))

coherence-concat-dependent-identification-eq-value :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g h : A → B} (H : f ~ g) (K : g ~ h) →
  {x y : A} (p : x ＝ y)
  {H₀ : f x ＝ g x} {H₁ : f y ＝ g y}
  {K₀ : g x ＝ h x} {K₁ : g y ＝ h y}
  (α₀ : H x ＝ H₀) (α₁ : H y ＝ H₁)
  (β₀ : K x ＝ K₀) (β₁ : K y ＝ K₁)
  (L : dependent-identification (eq-value-function f g) p H₀ H₁)
  (M : dependent-identification (eq-value-function g h) p K₀ K₁) →
  apd H p ∙ α₁ ＝
  ap (tr (eq-value-function f g) p) α₀ ∙ L →
  apd K p ∙ β₁ ＝
  ap (tr (eq-value-function g h) p) β₀ ∙ M →
  concat-dependent-identification-eq-value-function H K p (apd H p) (apd K p) ∙
  ap-binary _∙_ α₁ β₁ ＝
  ap (tr (eq-value-function f h) p) (ap-binary _∙_ α₀ β₀) ∙
  concat-dependent-identification-eq-value p L M
coherence-concat-dependent-identification-eq-value
  H K refl refl refl refl refl L M refl refl =
  refl

apd-concat-dependent-identification-eq-value-function :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g h : A → B} (H : f ~ g) (K : g ~ h) →
  {x y : A} (p : x ＝ y) →
  apd (λ z → H z ∙ K z) p ＝
  concat-dependent-identification-eq-value-function H K p (apd H p) (apd K p)
apd-concat-dependent-identification-eq-value-function H K refl = refl

compute-ap-map-commutative-product-eq-pair-Σ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {x x' : A} (p : x ＝ x') (y : B) →
  ap (map-commutative-product {A = A} {B = B})
    ( eq-pair-Σ
      { A = A}
      { B = λ _ → B}
      { s = x , y}
      { t = x' , y}
      ( p)
      ( tr-constant-type-family p y)) ＝
  eq-pair-Σ
    { A = B}
    { B = λ _ → A}
    { s = y , x}
    { t = y , x'}
    ( refl)
    ( p)
compute-ap-map-commutative-product-eq-pair-Σ refl y = refl

triangle-eq-pair-Σ-constant-type-family :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {x x' : A} (p : x ＝ x') (y : B) →
  eq-pair-Σ
    { A = A}
    { B = λ _ → B}
    { s = x , y}
    { t = x' , y}
    ( p)
    ( tr-constant-type-family p y) ＝
  ( eq-pair-Σ
    { A = A}
    { B = λ _ → B}
    { s = x , y}
    { t = x' , tr (λ _ → B) p y}
    ( p)
    ( refl) ∙
    eq-pair-Σ
    { A = A}
    { B = λ _ → B}
    { s = x' , tr (λ _ → B) p y}
    { t = x' , y}
    ( refl)
    ( tr-constant-type-family p y))
triangle-eq-pair-Σ-constant-type-family refl y = refl

compute-ap-map-Σ-map-base-eq-pair-Σ-refl :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : A → B) {x : A} {y y' : C} (q : y ＝ y') →
  ap (map-Σ-map-base f (λ _ → C))
    ( eq-pair-Σ
      { A = A}
      { B = λ _ → C}
      { s = x , y}
      { t = x , y'}
      ( refl)
      ( q)) ＝
  eq-pair-Σ
    { A = B}
    { B = λ _ → C}
    { s = f x , y}
    { t = f x , y'}
    ( refl)
    ( q)
compute-ap-map-Σ-map-base-eq-pair-Σ-refl f refl = refl
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

  triangle-eq-pair-Σ-product-join :
    {x x' : A * B} (p : x ＝ x') (c : C) →
    eq-pair-Σ
      { A = A * B}
      { B = λ _ → C}
      { s = x , c}
      { t = x' , c}
      ( p)
      ( tr-constant-type-family {A = A * B} {B = C} p c) ＝
    ( eq-pair-Σ
      { A = A * B}
      { B = λ _ → C}
      { s = x , c}
      { t = x' , tr (λ _ → C) p c}
      ( p)
      ( refl) ∙
      eq-pair-Σ
      { A = A * B}
      { B = λ _ → C}
      { s = x' , tr (λ _ → C) p c}
      { t = x' , c}
      ( refl)
      ( tr-constant-type-family {A = A * B} {B = C} p c))
  triangle-eq-pair-Σ-product-join refl c = refl

  compute-glue-cocone-product-join :
    coherence-square-cocone
      ( left-map-span-product-join)
      ( right-map-span-product-join)
      ( cocone-product-join) ~
    ( λ (t , c) →
      eq-pair-Σ
        { A = A * B}
        { B = λ _ → C}
        ( glue-join t)
        ( tr-constant-type-family
          { A = A * B}
          { B = C}
          ( glue-join t)
          ( c)))
  compute-glue-cocone-product-join (t , c) =
    ( ap
      ( λ q →
        eq-pair-Σ
          { A = A * B}
          { B = λ _ → C}
          { s = inl-join (pr1 t) , c}
          { t = inr-join (pr2 t) , tr (λ _ → C) (glue-join t) c}
          ( glue-join t)
          ( refl) ∙
        q)
      ( compute-ap-map-Σ-map-base-eq-pair-Σ-refl
        ( inr-join {A = A} {B = B})
        ( tr-constant-type-family
          { A = A * B}
          { B = C}
          ( glue-join t)
          ( c)))) ∙
    ( inv (triangle-eq-pair-Σ-product-join (glue-join t) c))

```

### Left products preserve join pushouts

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  left-map-span-left-product-join : A × (B × C) → A × B
  pr1 (left-map-span-left-product-join (a , b , c)) = a
  pr2 (left-map-span-left-product-join (a , b , c)) = b

  right-map-span-left-product-join : A × (B × C) → A × C
  pr1 (right-map-span-left-product-join (a , b , c)) = a
  pr2 (right-map-span-left-product-join (a , b , c)) = c

  coherence-left-map-span-left-product-join :
    coherence-square-maps
      ( map-commutative-product)
      ( left-map-span-left-product-join)
      ( left-map-span-product-join {A = B} {B = C} {C = A})
      ( map-commutative-product)
  coherence-left-map-span-left-product-join (a , b , c) = refl

  coherence-right-map-span-left-product-join :
    coherence-square-maps
      ( right-map-span-left-product-join)
      ( map-commutative-product)
      ( map-commutative-product)
      ( right-map-span-product-join {A = B} {B = C} {C = A})
  coherence-right-map-span-left-product-join (a , b , c) = refl

  universal-property-pushout-left-product-join-data :
    {l : Level} →
    Σ ( cocone
        ( left-map-span-left-product-join)
        ( right-map-span-left-product-join)
        ( (B * C) × A))
      ( universal-property-pushout-Level l
        ( left-map-span-left-product-join)
        ( right-map-span-left-product-join))
  universal-property-pushout-left-product-join-data =
    universal-property-pushout-extension-by-equivalences
      ( left-map-span-product-join {A = B} {B = C} {C = A})
      ( right-map-span-product-join {A = B} {B = C} {C = A})
      ( left-map-span-left-product-join)
      ( right-map-span-left-product-join)
      ( map-commutative-product)
      ( map-commutative-product)
      ( map-commutative-product)
      ( cocone-product-join {A = B} {B = C} {C = A})
      ( universal-property-pushout-cocone-product-join
        { A = B}
        { B = C}
        { C = A})
      ( coherence-left-map-span-left-product-join)
      ( coherence-right-map-span-left-product-join)
      ( is-equiv-map-commutative-product)
      ( is-equiv-map-commutative-product)
      ( is-equiv-map-commutative-product)

  cocone-left-product-join :
    cocone
      ( left-map-span-left-product-join)
      ( right-map-span-left-product-join)
      ( (B * C) × A)
  cocone-left-product-join =
    pr1 (universal-property-pushout-left-product-join-data {l = lzero})

  universal-property-pushout-cocone-left-product-join :
    universal-property-pushout
      ( left-map-span-left-product-join)
      ( right-map-span-left-product-join)
      ( cocone-left-product-join)
  universal-property-pushout-cocone-left-product-join =
    pr2 universal-property-pushout-left-product-join-data

  compute-glue-cocone-left-product-join :
    coherence-square-cocone
      ( left-map-span-left-product-join)
      ( right-map-span-left-product-join)
      ( cocone-left-product-join) ~
    ( λ (a , b , c) →
      eq-pair-Σ
        { A = B * C}
        { B = λ _ → A}
        ( glue-join (b , c))
        ( tr-constant-type-family
          { A = B * C}
          { B = A}
          ( glue-join (b , c))
          ( a)))
  compute-glue-cocone-left-product-join (a , b , c) =
    ( ap
      ( _∙ refl)
      ( compute-glue-cocone-product-join
        { A = B}
        { B = C}
        { C = A}
        ( (b , c) , a))) ∙
    right-unit

  cocone-left-product-join' :
    cocone
      ( left-map-span-left-product-join)
      ( right-map-span-left-product-join)
      ( A × (B * C))
  cocone-left-product-join' =
    cocone-map
      ( left-map-span-left-product-join)
      ( right-map-span-left-product-join)
      ( cocone-left-product-join)
      ( map-commutative-product)

  universal-property-pushout-cocone-left-product-join' :
    universal-property-pushout
      ( left-map-span-left-product-join)
      ( right-map-span-left-product-join)
      ( cocone-left-product-join')
  universal-property-pushout-cocone-left-product-join' =
    up-pushout-up-pushout-is-equiv
      ( left-map-span-left-product-join)
      ( right-map-span-left-product-join)
      ( cocone-left-product-join)
      ( cocone-left-product-join')
      ( map-commutative-product)
      ( refl-htpy-cocone
        ( left-map-span-left-product-join)
        ( right-map-span-left-product-join)
        ( cocone-left-product-join'))
      ( is-equiv-map-commutative-product)
      ( universal-property-pushout-cocone-left-product-join)

  compute-horizontal-map-cocone-left-product-join' :
    horizontal-map-cocone
      ( left-map-span-left-product-join)
      ( right-map-span-left-product-join)
      ( cocone-left-product-join') ~
    map-product id inl-join
  compute-horizontal-map-cocone-left-product-join' = refl-htpy

  compute-vertical-map-cocone-left-product-join' :
    vertical-map-cocone
      ( left-map-span-left-product-join)
      ( right-map-span-left-product-join)
      ( cocone-left-product-join') ~
    map-product id inr-join
  compute-vertical-map-cocone-left-product-join' = refl-htpy

  compute-glue-cocone-left-product-join' :
    coherence-square-cocone
      ( left-map-span-left-product-join)
      ( right-map-span-left-product-join)
      ( cocone-left-product-join') ~
    ( λ t →
      eq-pair-Σ
        { A = A}
        { B = λ _ → B * C}
        ( refl)
        ( glue-join (pr1 (pr2 t) , pr2 (pr2 t))))
  compute-glue-cocone-left-product-join' (a , b , c) =
    ( ap
      ( ap (map-commutative-product {A = B * C} {B = A}))
      ( compute-glue-cocone-left-product-join (a , b , c))) ∙
    compute-ap-map-commutative-product-eq-pair-Σ
      { A = B * C}
      { B = A}
      ( glue-join (b , c))
      ( a)
```

### Triple join recursion data

```agda
record tri-join-rec-data
  {l1 l2 l3 l4 : Level}
  (A : UU l1) (B : UU l2) (C : UU l3) (X : UU l4) :
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  constructor make-tri-join-rec-data
  field
    point-1-tri-join-rec-data : A → X
    point-2-tri-join-rec-data : B → X
    point-3-tri-join-rec-data : C → X
    path-12-tri-join-rec-data :
      (a : A) (b : B) →
      point-1-tri-join-rec-data a ＝ point-2-tri-join-rec-data b
    path-13-tri-join-rec-data :
      (a : A) (c : C) →
      point-1-tri-join-rec-data a ＝ point-3-tri-join-rec-data c
    path-23-tri-join-rec-data :
      (b : B) (c : C) →
      point-2-tri-join-rec-data b ＝ point-3-tri-join-rec-data c
    coherence-triangle-tri-join-rec-data :
      (a : A) (b : B) (c : C) →
      path-12-tri-join-rec-data a b ∙
      path-23-tri-join-rec-data b c ＝
      path-13-tri-join-rec-data a c

open tri-join-rec-data public

map-tri-join-rec-data :
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} →
  (X → Y) → tri-join-rec-data A B C X → tri-join-rec-data A B C Y
map-tri-join-rec-data f d =
  make-tri-join-rec-data
    ( f ∘ point-1-tri-join-rec-data d)
    ( f ∘ point-2-tri-join-rec-data d)
    ( f ∘ point-3-tri-join-rec-data d)
    ( λ a b → ap f (path-12-tri-join-rec-data d a b))
    ( λ a c → ap f (path-13-tri-join-rec-data d a c))
    ( λ b c → ap f (path-23-tri-join-rec-data d b c))
    ( λ a b c →
      inv
        ( ap-concat
          ( f)
          ( path-12-tri-join-rec-data d a b)
          ( path-23-tri-join-rec-data d b c)) ∙
      ap
        ( ap f)
        ( coherence-triangle-tri-join-rec-data d a b c))

twist-tri-join-rec-data :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} →
  tri-join-rec-data A B C X → tri-join-rec-data B A C X
twist-tri-join-rec-data d =
  make-tri-join-rec-data
    ( point-2-tri-join-rec-data d)
    ( point-1-tri-join-rec-data d)
    ( point-3-tri-join-rec-data d)
    ( λ b a → inv (path-12-tri-join-rec-data d a b))
    ( path-23-tri-join-rec-data d)
    ( path-13-tri-join-rec-data d)
    ( λ b a c →
      inv
        ( left-transpose-eq-concat
          ( path-12-tri-join-rec-data d a b)
          ( path-23-tri-join-rec-data d b c)
          ( path-13-tri-join-rec-data d a c)
          ( coherence-triangle-tri-join-rec-data d a b c)))

precomp-tri-join-rec-data :
  {l1 l2 l3 l1' l2' l3' l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {X : UU l4} →
  tri-join-rec-data A' B' C' X →
  (A → A') → (B → B') → (C → C') →
  tri-join-rec-data A B C X
precomp-tri-join-rec-data d f g h =
  make-tri-join-rec-data
    ( point-1-tri-join-rec-data d ∘ f)
    ( point-2-tri-join-rec-data d ∘ g)
    ( point-3-tri-join-rec-data d ∘ h)
    ( λ a b → path-12-tri-join-rec-data d (f a) (g b))
    ( λ a c → path-13-tri-join-rec-data d (f a) (h c))
    ( λ b c → path-23-tri-join-rec-data d (g b) (h c))
    ( λ a b c → coherence-triangle-tri-join-rec-data d (f a) (g b) (h c))

path-12-twist-twist-tri-join-rec-data :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (d : tri-join-rec-data A B C X) →
  path-12-tri-join-rec-data
    ( twist-tri-join-rec-data (twist-tri-join-rec-data d)) ＝
  path-12-tri-join-rec-data d
path-12-twist-twist-tri-join-rec-data d =
  eq-htpy
    ( λ a →
      eq-htpy
        ( λ b → inv-inv (path-12-tri-join-rec-data d a b)))

path-13-twist-twist-tri-join-rec-data :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (d : tri-join-rec-data A B C X) →
  path-13-tri-join-rec-data
    ( twist-tri-join-rec-data (twist-tri-join-rec-data d)) ＝
  path-13-tri-join-rec-data d
path-13-twist-twist-tri-join-rec-data d = refl

path-23-twist-twist-tri-join-rec-data :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (d : tri-join-rec-data A B C X) →
  path-23-tri-join-rec-data
    ( twist-tri-join-rec-data (twist-tri-join-rec-data d)) ＝
  path-23-tri-join-rec-data d
path-23-twist-twist-tri-join-rec-data d = refl

eq-tri-join-rec-data-path-12 :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  {i : A → X} {j : B → X} {k : C → X}
  {H H' : (a : A) (b : B) → i a ＝ j b}
  {L : (a : A) (c : C) → i a ＝ k c}
  {K : (b : B) (c : C) → j b ＝ k c}
  {M : (a : A) (b : B) (c : C) → H a b ∙ K b c ＝ L a c}
  {M' : (a : A) (b : B) (c : C) → H' a b ∙ K b c ＝ L a c} →
  (p : H ＝ H') →
  dependent-identification
    ( λ R →
      (a : A) (b : B) (c : C) → R a b ∙ K b c ＝ L a c)
    ( p)
    ( M)
    ( M') →
  make-tri-join-rec-data i j k H L K M ＝
  make-tri-join-rec-data i j k H' L K M'
eq-tri-join-rec-data-path-12 refl refl = refl

coherence-twist-twist-tri-join-rec-data :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (d : tri-join-rec-data A B C X) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
coherence-twist-twist-tri-join-rec-data {A = A} {B = B} {C = C} d =
  dependent-identification
    ( λ H →
      (a : A) (b : B) (c : C) →
      H a b ∙ path-23-tri-join-rec-data d b c ＝
      path-13-tri-join-rec-data d a c)
    ( path-12-twist-twist-tri-join-rec-data d)
    ( coherence-triangle-tri-join-rec-data
      ( twist-tri-join-rec-data (twist-tri-join-rec-data d)))
    ( coherence-triangle-tri-join-rec-data d)

pointwise-coherence-twist-twist-tri-join-rec-data :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (d : tri-join-rec-data A B C X) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
pointwise-coherence-twist-twist-tri-join-rec-data d =
  (a : _) (b : _) (c : _) →
  tr
    ( λ H →
      H a b ∙ path-23-tri-join-rec-data d b c ＝
      path-13-tri-join-rec-data d a c)
    ( path-12-twist-twist-tri-join-rec-data d)
    ( coherence-triangle-tri-join-rec-data
      ( twist-tri-join-rec-data (twist-tri-join-rec-data d))
      a b c) ＝
  coherence-triangle-tri-join-rec-data d a b c

coherence-twist-twist-tri-join-rec-data-pointwise :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (d : tri-join-rec-data A B C X) →
  pointwise-coherence-twist-twist-tri-join-rec-data d →
  coherence-twist-twist-tri-join-rec-data d
coherence-twist-twist-tri-join-rec-data-pointwise d =
  map-compute-dependent-identification-dependent-function-type-three-fixed-domains
    ( λ H a b c →
      H a b ∙ path-23-tri-join-rec-data d b c ＝
      path-13-tri-join-rec-data d a c)
    ( path-12-twist-twist-tri-join-rec-data d)
    ( coherence-triangle-tri-join-rec-data
      ( twist-tri-join-rec-data (twist-tri-join-rec-data d)))
    ( coherence-triangle-tri-join-rec-data d)

eq-twist-twist-tri-join-rec-data :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (d : tri-join-rec-data A B C X) →
  coherence-twist-twist-tri-join-rec-data d →
  twist-tri-join-rec-data (twist-tri-join-rec-data d) ＝ d
eq-twist-twist-tri-join-rec-data d =
  eq-tri-join-rec-data-path-12
    ( path-12-twist-twist-tri-join-rec-data d)
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

  canonical-tri-join-rec-data :
    tri-join-rec-data A B C (A * (B * C))
  canonical-tri-join-rec-data =
    make-tri-join-rec-data
      ( inl-join)
      ( inr-join ∘ inl-join)
      ( inr-join ∘ inr-join)
      ( λ a b → glue-join (a , inl-join b))
      ( λ a c → glue-join (a , inr-join c))
      ( λ b c → ap inr-join (glue-join (b , c)))
      ( naturality-glue-left-join)

  tri-join-rec-data-cocone-A-join-BC :
    {l4 : Level} {X : UU l4} →
    cocone
      ( λ (t : A × (B * C)) → pr1 t)
      ( λ (t : A × (B * C)) → pr2 t)
      ( X) →
    tri-join-rec-data A B C X
  tri-join-rec-data-cocone-A-join-BC d =
    make-tri-join-rec-data
      ( horizontal-map-cocone pr1 pr2 d)
      ( vertical-map-cocone pr1 pr2 d ∘ inl-join)
      ( vertical-map-cocone pr1 pr2 d ∘ inr-join)
      ( λ a b → coherence-square-cocone pr1 pr2 d (a , inl-join b))
      ( λ a c → coherence-square-cocone pr1 pr2 d (a , inr-join c))
      ( λ b c → ap (vertical-map-cocone pr1 pr2 d) (glue-join (b , c)))
      ( λ a b c →
        naturality-constant-homotopy
          ( λ y → coherence-square-cocone pr1 pr2 d (a , y))
          ( glue-join (b , c)))

  tr-dependent-function-type-fixed-domain :
    {l4 l5 l6 : Level} {X : UU l4} {D : UU l5}
    (P : X → D → UU l6) {x y : X} →
    (p : x ＝ y) (h : (d : D) → P x d) (d : D) →
    tr (λ z → (d' : D) → P z d') p h d ＝
    tr (λ z → P z d) p (h d)
  tr-dependent-function-type-fixed-domain P refl h d = refl

  map-inv-compute-dependent-identification-dependent-function-type-fixed-domain :
    {l4 l5 l6 : Level} {X : UU l4} {D : UU l5}
    (P : X → D → UU l6) {x y : X} →
    (p : x ＝ y) (h : (d : D) → P x d) (k : (d : D) → P y d) →
    dependent-identification (λ z → (d : D) → P z d) p h k →
    (d : D) →
    tr (λ z → P z d) p (h d) ＝ k d
  map-inv-compute-dependent-identification-dependent-function-type-fixed-domain
    P refl h k q d =
    ap (ev-point d) q

  compute-tr-ap-concat-constant :
    {l4 l5 l6 : Level} {X : UU l4} {Y : UU l5} {Z : UU l6}
    (m : Y → Z) (g : X → Y) {y : Y} {z : Z} →
    (r : m y ＝ z) {x x' : X} (p : x ＝ x') →
    (q : g x ＝ y) →
    tr (λ u → m (g u) ＝ z) p (ap m q ∙ r) ＝
    ap m (tr (λ u → g u ＝ y) p q) ∙ r
  compute-tr-ap-concat-constant m g r refl q = refl

  compute-tr-Id-left-function :
    {l4 l5 : Level} {X : UU l4} {Y : UU l5}
    (f : X → Y) {y : Y} {x x' : X} (p : x ＝ x') →
    (q : f x ＝ y) →
    tr (λ u → f u ＝ y) p q ＝ inv (ap f p) ∙ q
  compute-tr-Id-left-function f refl q = refl

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

  is-equiv-map-associative-join-universal-property-pushout :
    universal-property-pushout pr1 pr2 cocone-associative-join →
    is-equiv map-associative-join
  is-equiv-map-associative-join-universal-property-pushout up-assoc =
    is-equiv-up-pushout-up-pushout
      ( pr1)
      ( pr2)
      ( cocone-join)
      ( cocone-associative-join)
      ( map-associative-join)
      ( ( compute-inl-map-associative-join) ,
        ( ( compute-inr-map-associative-join) ,
          ( compute-glue-map-associative-join)))
      ( up-join)
      ( up-assoc)

  is-equiv-cogap-join :
    {l4 : Level} (X : UU l4) →
    is-equiv (cogap-join {A = A} {B = B} X)
  is-equiv-cogap-join X =
    is-equiv-is-invertible
      ( cocone-map pr1 pr2 cocone-join)
      ( is-retraction-cogap pr1 pr2)
      ( is-section-cogap pr1 pr2)

  is-equiv-cocone-map-join :
    {l4 : Level} (X : UU l4) →
    is-equiv (cocone-map pr1 pr2 {Y = X} (cocone-join {A = A} {B = B}))
  is-equiv-cocone-map-join X =
    is-equiv-is-invertible
      ( cogap-join X)
      ( is-section-cogap pr1 pr2)
      ( is-retraction-cogap pr1 pr2)

  is-equiv-dependent-cogap-join :
    {l4 : Level} {P : A * B → UU l4} →
    is-equiv (dependent-cogap-join {A = A} {B = B} {P = P})
  is-equiv-dependent-cogap-join {P = P} =
    is-equiv-is-invertible
      ( dependent-cocone-map pr1 pr2 cocone-join P)
      ( is-retraction-dependent-cogap pr1 pr2)
      ( is-section-dependent-cogap pr1 pr2)

  is-equiv-dependent-cocone-map-join :
    {l4 : Level} {P : A * B → UU l4} →
    is-equiv
      ( dependent-cocone-map pr1 pr2 (cocone-join {A = A} {B = B}) P)
  is-equiv-dependent-cocone-map-join {P = P} =
    is-equiv-is-invertible
      ( dependent-cogap-join)
      ( is-section-dependent-cogap pr1 pr2)
      ( is-retraction-dependent-cogap pr1 pr2)

  is-equiv-cogap-join-BC :
    {l4 : Level} (X : UU l4) →
    is-equiv (cogap-join {A = B} {B = C} X)
  is-equiv-cogap-join-BC X =
    is-equiv-is-invertible
      ( cocone-map pr1 pr2 cocone-join)
      ( is-retraction-cogap pr1 pr2)
      ( is-section-cogap pr1 pr2)

  is-equiv-cocone-map-join-BC :
    {l4 : Level} (X : UU l4) →
    is-equiv (cocone-map pr1 pr2 {Y = X} (cocone-join {A = B} {B = C}))
  is-equiv-cocone-map-join-BC X =
    is-equiv-is-invertible
      ( cogap-join X)
      ( is-section-cogap pr1 pr2)
      ( is-retraction-cogap pr1 pr2)

  is-equiv-cocone-map-standard-join :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'} →
    (X : UU l4) →
    is-equiv
      ( cocone-map pr1 pr2 {Y = X}
        ( cocone-join {A = A'} {B = B'}))
  is-equiv-cocone-map-standard-join X =
    is-equiv-is-invertible
      ( cogap-join X)
      ( is-section-cogap pr1 pr2)
      ( is-retraction-cogap pr1 pr2)

  is-equiv-dependent-cogap-join-BC :
    {l4 : Level} {P : B * C → UU l4} →
    is-equiv (dependent-cogap-join {A = B} {B = C} {P = P})
  is-equiv-dependent-cogap-join-BC {P = P} =
    is-equiv-is-invertible
      ( dependent-cocone-map pr1 pr2 cocone-join P)
      ( is-retraction-dependent-cogap pr1 pr2)
      ( is-section-dependent-cogap pr1 pr2)

  is-equiv-dependent-cocone-map-join-BC :
    {l4 : Level} {P : B * C → UU l4} →
    is-equiv
      ( dependent-cocone-map pr1 pr2 (cocone-join {A = B} {B = C}) P)
  is-equiv-dependent-cocone-map-join-BC {P = P} =
    is-equiv-is-invertible
      ( dependent-cogap-join)
      ( is-section-dependent-cogap pr1 pr2)
      ( is-retraction-dependent-cogap pr1 pr2)

  is-equiv-dependent-cocone-map-standard-join :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {P : A' * B' → UU l4} →
    is-equiv
      ( dependent-cocone-map pr1 pr2
        ( cocone-join {A = A'} {B = B'}) P)
  is-equiv-dependent-cocone-map-standard-join =
    is-equiv-is-invertible
      ( dependent-cogap-join)
      ( is-section-dependent-cogap pr1 pr2)
      ( is-retraction-dependent-cogap pr1 pr2)

  right-transpose-compute-glue-cogap-join :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X) →
    (a : A') (b : B') →
    inv (compute-inl-cogap-join d a) ∙
    ap (cogap-join X d) (glue-join (a , b)) ＝
    coherence-square-cocone pr1 pr2 d (a , b) ∙
    inv (compute-inr-cogap-join d b)
  right-transpose-compute-glue-cogap-join {A' = A'} {B' = B'} d a b =
    equational-reasoning
      inv linl ∙ apF
      ＝ (inv linl ∙ apF) ∙ refl
        by inv right-unit
      ＝ (inv linl ∙ apF) ∙ (rinr ∙ inv rinr)
        by ap ((inv linl ∙ apF) ∙_) (inv (right-inv rinr))
      ＝ ((inv linl ∙ apF) ∙ rinr) ∙ inv rinr
        by inv (assoc (inv linl ∙ apF) rinr (inv rinr))
      ＝ (inv linl ∙ (apF ∙ rinr)) ∙ inv rinr
        by ap (_∙ inv rinr) (assoc (inv linl) apF rinr)
      ＝ (inv linl ∙ (linl ∙ H (a , b))) ∙ inv rinr
        by ap
          ( λ q → (inv linl ∙ q) ∙ inv rinr)
          ( compute-glue-F (a , b))
      ＝ ((inv linl ∙ linl) ∙ H (a , b)) ∙ inv rinr
        by ap (_∙ inv rinr) (inv (assoc (inv linl) linl (H (a , b))))
      ＝ (refl ∙ H (a , b)) ∙ inv rinr
        by ap (λ q → (q ∙ H (a , b)) ∙ inv rinr) (left-inv linl)
      ＝ H (a , b) ∙ inv rinr
        by ap (_∙ inv rinr) left-unit
    where
    F : A' * B' → _
    F = cogap-join _ d

    H = coherence-square-cocone pr1 pr2 d

    linl = compute-inl-cogap-join d a
    rinr = compute-inr-cogap-join d b
    apF = ap F (glue-join (a , b))

    compute-glue-F :
      statement-coherence-htpy-cocone pr1 pr2
        ( cocone-map pr1 pr2 cocone-join F)
        ( d)
        ( compute-inl-cogap-join d)
        ( compute-inr-cogap-join d)
    compute-glue-F = compute-glue-cogap-join d

  path-inl-htpy-cogap-join-cocone-map :
    {l1' l2' l4 l5 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4} {Y : UU l5}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (h : X → Y) (a : A') →
    cogap-join Y (cocone-map pr1 pr2 d h) (inl-join a) ＝
    h (cogap-join X d (inl-join a))
  path-inl-htpy-cogap-join-cocone-map d h a =
    compute-inl-cogap-join (cocone-map pr1 pr2 d h) a ∙
    inv (ap h (compute-inl-cogap-join d a))

  path-inr-htpy-cogap-join-cocone-map :
    {l1' l2' l4 l5 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4} {Y : UU l5}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (h : X → Y) (b : B') →
    cogap-join Y (cocone-map pr1 pr2 d h) (inr-join b) ＝
    h (cogap-join X d (inr-join b))
  path-inr-htpy-cogap-join-cocone-map d h b =
    compute-inr-cogap-join (cocone-map pr1 pr2 d h) b ∙
    inv (ap h (compute-inr-cogap-join d b))

  coherence-square-htpy-cogap-join-cocone-map :
    {l1' l2' l4 l5 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4} {Y : UU l5}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (h : X → Y) (a : A') (b : B') →
    coherence-square-identifications
      ( path-inl-htpy-cogap-join-cocone-map d h a)
      ( ap
        ( cogap-join Y (cocone-map pr1 pr2 d h))
        ( glue-join (a , b)))
      ( ap (h ∘ cogap-join X d) (glue-join (a , b)))
      ( path-inr-htpy-cogap-join-cocone-map d h b)
  coherence-square-htpy-cogap-join-cocone-map
    {A' = A'} {B' = B'} d h a b =
    equational-reasoning
      ap F' p ∙ (rinr' ∙ inv (ap h rinr))
      ＝ (ap F' p ∙ rinr') ∙ inv (ap h rinr)
        by inv (assoc (ap F' p) rinr' (inv (ap h rinr)))
      ＝ (linl' ∙ ap h H) ∙ inv (ap h rinr)
        by ap (_∙ inv (ap h rinr)) (compute-glue-F' (a , b))
      ＝ linl' ∙ (ap h H ∙ inv (ap h rinr))
        by assoc linl' (ap h H) (inv (ap h rinr))
      ＝ linl' ∙ (ap h H ∙ ap h (inv rinr))
        by ap (λ q → linl' ∙ (ap h H ∙ q)) (inv (ap-inv h rinr))
      ＝ linl' ∙ ap h (H ∙ inv rinr)
        by ap (linl' ∙_) (inv (ap-concat h H (inv rinr)))
      ＝ linl' ∙ ap h (inv linl ∙ ap F p)
        by ap (λ q → linl' ∙ ap h q) (inv right-transpose-glue-F)
      ＝ linl' ∙ (ap h (inv linl) ∙ ap h (ap F p))
        by ap (linl' ∙_) (ap-concat h (inv linl) (ap F p))
      ＝ linl' ∙ (inv (ap h linl) ∙ ap h (ap F p))
        by ap (λ q → linl' ∙ (q ∙ ap h (ap F p))) (ap-inv h linl)
      ＝ (linl' ∙ inv (ap h linl)) ∙ ap h (ap F p)
        by inv (assoc linl' (inv (ap h linl)) (ap h (ap F p)))
      ＝ (linl' ∙ inv (ap h linl)) ∙ ap (h ∘ F) p
        by ap ((linl' ∙ inv (ap h linl)) ∙_) (inv (ap-comp h F p))
    where
    F : A' * B' → _
    F = cogap-join _ d

    F' : A' * B' → _
    F' = cogap-join _ (cocone-map pr1 pr2 d h)

    p = glue-join (a , b)

    H = coherence-square-cocone pr1 pr2 d (a , b)

    linl = compute-inl-cogap-join d a
    rinr = compute-inr-cogap-join d b
    linl' = compute-inl-cogap-join (cocone-map pr1 pr2 d h) a
    rinr' = compute-inr-cogap-join (cocone-map pr1 pr2 d h) b

    compute-glue-F' :
      statement-coherence-htpy-cocone pr1 pr2
        ( cocone-map pr1 pr2 cocone-join F')
        ( cocone-map pr1 pr2 d h)
        ( compute-inl-cogap-join (cocone-map pr1 pr2 d h))
        ( compute-inr-cogap-join (cocone-map pr1 pr2 d h))
    compute-glue-F' =
      compute-glue-cogap-join (cocone-map pr1 pr2 d h)

    right-transpose-glue-F :
      inv linl ∙ ap F p ＝ H ∙ inv rinr
    right-transpose-glue-F =
      right-transpose-compute-glue-cogap-join d a b

  coherence-htpy-cogap-join-cocone-map :
    {l1' l2' l4 l5 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4} {Y : UU l5}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (h : X → Y) (a : A') (b : B') →
    dependent-identification
      ( λ z →
        cogap-join Y (cocone-map pr1 pr2 d h) z ＝
        h (cogap-join X d z))
      ( glue-join (a , b))
      ( path-inl-htpy-cogap-join-cocone-map d h a)
      ( path-inr-htpy-cogap-join-cocone-map d h b)
  coherence-htpy-cogap-join-cocone-map
    {A' = A'} {B' = B'} d h a b =
    map-compute-dependent-identification-eq-value-function
      ( F')
      ( h ∘ F)
      ( p)
      ( path-inl-htpy-cogap-join-cocone-map d h a)
      ( path-inr-htpy-cogap-join-cocone-map d h b)
      ( coherence-square-htpy-cogap-join-cocone-map d h a b)
    where
    F : A' * B' → _
    F = cogap-join _ d

    F' : A' * B' → _
    F' = cogap-join _ (cocone-map pr1 pr2 d h)

    p = glue-join (a , b)

  dependent-cocone-htpy-cogap-join-cocone-map :
    {l1' l2' l4 l5 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4} {Y : UU l5}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (h : X → Y) →
    dependent-cocone pr1 pr2 cocone-join
      ( λ z →
        cogap-join Y (cocone-map pr1 pr2 d h) z ＝
        h (cogap-join X d z))
  pr1 (dependent-cocone-htpy-cogap-join-cocone-map d h) =
    path-inl-htpy-cogap-join-cocone-map d h
  pr1 (pr2 (dependent-cocone-htpy-cogap-join-cocone-map d h)) =
    path-inr-htpy-cogap-join-cocone-map d h
  pr2 (pr2 (dependent-cocone-htpy-cogap-join-cocone-map d h)) (a , b) =
    coherence-htpy-cogap-join-cocone-map d h a b

  htpy-cogap-join-cocone-map-compute :
    {l1' l2' l4 l5 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4} {Y : UU l5}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (h : X → Y) →
    cogap-join Y (cocone-map pr1 pr2 d h) ~ h ∘ cogap-join X d
  htpy-cogap-join-cocone-map-compute d h =
    dependent-cogap-join (dependent-cocone-htpy-cogap-join-cocone-map d h)

  htpy-cogap-join-cocone-map :
    {l1' l2' l4 l5 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4} {Y : UU l5}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (h : X → Y) →
    cogap-join Y (cocone-map pr1 pr2 d h) ~ h ∘ cogap-join X d
  htpy-cogap-join-cocone-map {A' = A'} {B' = B'} {X = X} {Y = Y} d h =
    htpy-eq
      ( map-inv-is-equiv
        ( is-emb-is-equiv
          ( is-equiv-cocone-map-standard-join Y)
          ( cogap-join Y (cocone-map pr1 pr2 d h))
          ( h ∘ cogap-join X d))
        ( eq-cocone-maps))
    where
    eq-cocone-map-left :
      cocone-map pr1 pr2 (cocone-join {A = A'} {B = B'})
        ( cogap-join Y (cocone-map pr1 pr2 d h)) ＝
      cocone-map pr1 pr2 d h
    eq-cocone-map-left =
      is-section-cogap pr1 pr2 (cocone-map pr1 pr2 d h)

    eq-cocone-map-right :
      cocone-map pr1 pr2 (cocone-join {A = A'} {B = B'})
        ( h ∘ cogap-join X d) ＝
      cocone-map pr1 pr2 d h
    eq-cocone-map-right =
      cocone-map-comp pr1 pr2
        ( cocone-join {A = A'} {B = B'})
        ( cogap-join X d)
        ( h) ∙
      ap (λ e → cocone-map pr1 pr2 e h)
        ( is-section-cogap pr1 pr2 d)

    eq-cocone-maps :
      cocone-map pr1 pr2 (cocone-join {A = A'} {B = B'})
        ( cogap-join Y (cocone-map pr1 pr2 d h)) ＝
      cocone-map pr1 pr2 (cocone-join {A = A'} {B = B'})
        ( h ∘ cogap-join X d)
    eq-cocone-maps =
      eq-cocone-map-left ∙ inv eq-cocone-map-right

  cogap-join-constant-data :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4} →
    cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X →
    X → UU (l1' ⊔ l2' ⊔ l4)
  cogap-join-constant-data d z =
    Σ ( (b : _) → vertical-map-cocone pr1 pr2 d b ＝ z)
      ( λ K →
        Σ ( (a : _) → horizontal-map-cocone pr1 pr2 d a ＝ z)
          ( λ L →
            (a : _) (b : _) →
            coherence-square-cocone pr1 pr2 d (a , b) ∙ K b ＝ L a))

  coherence-square-cogap-join-constant-data :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4} →
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X)
    (K : (b : B') → vertical-map-cocone pr1 pr2 d b ＝ z)
    (L : (a : A') → horizontal-map-cocone pr1 pr2 d a ＝ z) →
    (a : A') (b : B') →
    coherence-square-cocone pr1 pr2 d (a , b) ∙ K b ＝ L a →
    coherence-square-identifications
      ( compute-inl-cogap-join d a ∙ L a)
      ( ap (cogap-join X d) (glue-join (a , b)))
      ( ap (λ _ → z) (glue-join (a , b)))
      ( compute-inr-cogap-join d b ∙ K b)
  coherence-square-cogap-join-constant-data
    { A' = A'}
    { B' = B'}
    d z K L a b M =
    concat Pleft final (concat' middle Pright (ap (concat linl z) M))
    where
    F : A' * B' → _
    F = cogap-join _ d

    H = coherence-square-cocone pr1 pr2 d

    p = glue-join (a , b)
    linl = compute-inl-cogap-join d a
    rinr = compute-inr-cogap-join d b
    apF = ap F p

    start = apF ∙ (rinr ∙ K b)
    middle = linl ∙ (H (a , b) ∙ K b)
    final = (linl ∙ L a) ∙ ap (λ _ → z) p

    compute-glue-F :
      statement-coherence-htpy-cocone pr1 pr2
        ( cocone-map pr1 pr2 cocone-join F)
        ( d)
        ( compute-inl-cogap-join d)
        ( compute-inr-cogap-join d)
    compute-glue-F = compute-glue-cogap-join d

    Pleft : start ＝ middle
    Pleft =
      inv (assoc apF rinr (K b)) ∙
      ap (_∙ K b) (compute-glue-F (a , b)) ∙
      assoc linl (H (a , b)) (K b)

    Pright : linl ∙ L a ＝ final
    Pright =
      inv right-unit ∙
      ap ((linl ∙ L a) ∙_) (inv (ap-const z p))

  is-equiv-coherence-square-cogap-join-constant-data :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X)
    (K : (b : B') → vertical-map-cocone pr1 pr2 d b ＝ z)
    (L : (a : A') → horizontal-map-cocone pr1 pr2 d a ＝ z)
    (a : A') (b : B') →
    is-equiv (coherence-square-cogap-join-constant-data d z K L a b)
  is-equiv-coherence-square-cogap-join-constant-data
    { A' = A'}
    { B' = B'}
    d z K L a b =
    is-equiv-comp
      ( concat Pleft final)
      ( concat' middle Pright ∘ ap (concat linl z))
      ( is-equiv-comp
        ( concat' middle Pright)
        ( ap (concat linl z))
        ( is-emb-is-equiv
          ( is-equiv-concat linl z)
          ( H (a , b) ∙ K b)
          ( L a))
        ( is-equiv-concat' middle Pright))
      ( is-equiv-concat Pleft final)
    where
    F : A' * B' → _
    F = cogap-join _ d

    H = coherence-square-cocone pr1 pr2 d

    p = glue-join (a , b)
    linl = compute-inl-cogap-join d a
    rinr = compute-inr-cogap-join d b
    apF = ap F p

    start = apF ∙ (rinr ∙ K b)
    middle = linl ∙ (H (a , b) ∙ K b)
    final = (linl ∙ L a) ∙ ap (λ _ → z) p

    compute-glue-F :
      statement-coherence-htpy-cocone pr1 pr2
        ( cocone-map pr1 pr2 cocone-join F)
        ( d)
        ( compute-inl-cogap-join d)
        ( compute-inr-cogap-join d)
    compute-glue-F = compute-glue-cogap-join d

    Pleft : start ＝ middle
    Pleft =
      inv (assoc apF rinr (K b)) ∙
      ap (_∙ K b) (compute-glue-F (a , b)) ∙
      assoc linl (H (a , b)) (K b)

    Pright : linl ∙ L a ＝ final
    Pright =
      inv right-unit ∙
      ap ((linl ∙ L a) ∙_) (inv (ap-const z p))

  module _
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X)
    (K : (b : B') → vertical-map-cocone pr1 pr2 d b ＝ z)
    (L : (a : A') → horizontal-map-cocone pr1 pr2 d a ＝ z)
    (a : A') (b : B')
    (M : coherence-square-cocone pr1 pr2 d (a , b) ∙ K b ＝ L a)
    where

    private
      F : A' * B' → _
      F = cogap-join _ d

      H = coherence-square-cocone pr1 pr2 d

      p = glue-join (a , b)
      linl = compute-inl-cogap-join d a
      rinr = compute-inr-cogap-join d b
      apF = ap F p

      middle = linl ∙ (H (a , b) ∙ K b)
      final = (linl ∙ L a) ∙ ap (λ _ → z) p
      apM = ap (concat linl z) M

      compute-glue-F :
        statement-coherence-htpy-cocone pr1 pr2
          ( cocone-map pr1 pr2 cocone-join F)
          ( d)
          ( compute-inl-cogap-join d)
          ( compute-inr-cogap-join d)
      compute-glue-F = compute-glue-cogap-join d

      Pleft : apF ∙ (rinr ∙ K b) ＝ middle
      Pleft =
        inv (assoc apF rinr (K b)) ∙
        ap (_∙ K b) (compute-glue-F (a , b)) ∙
        assoc linl (H (a , b)) (K b)

      Pright : linl ∙ L a ＝ final
      Pright =
        inv right-unit ∙
        ap ((linl ∙ L a) ∙_) (inv (ap-const z p))

    stripped-coherence-square-cogap-join-constant-data :
      ((inv Pleft ∙
        coherence-square-cogap-join-constant-data d z K L a b M) ∙
        inv Pright) ＝
      ap (concat linl z) M
    stripped-coherence-square-cogap-join-constant-data =
      equational-reasoning
        (inv Pleft ∙ (Pleft ∙ (apM ∙ Pright))) ∙ inv Pright
        ＝ ((inv Pleft ∙ Pleft) ∙ (apM ∙ Pright)) ∙ inv Pright
          by ap (_∙ inv Pright)
            ( inv (assoc (inv Pleft) Pleft (apM ∙ Pright)))
        ＝ (refl ∙ (apM ∙ Pright)) ∙ inv Pright
          by ap (λ q → (q ∙ (apM ∙ Pright)) ∙ inv Pright)
            ( left-inv Pleft)
        ＝ (apM ∙ Pright) ∙ inv Pright
          by ap (_∙ inv Pright) left-unit
        ＝ apM ∙ (Pright ∙ inv Pright)
          by assoc apM Pright (inv Pright)
        ＝ apM ∙ refl
          by ap (apM ∙_) (right-inv Pright)
        ＝ apM
          by right-unit

  horizontal-first-cogap-join-constant-data :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4} →
    cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X →
    X → UU (l1' ⊔ l2' ⊔ l4)
  horizontal-first-cogap-join-constant-data d z =
    Σ ( (a : _) → horizontal-map-cocone pr1 pr2 d a ＝ z)
      ( λ L →
        Σ ( (b : _) → vertical-map-cocone pr1 pr2 d b ＝ z)
          ( λ K →
            (a : _) (b : _) →
            coherence-square-cocone pr1 pr2 d (a , b) ∙ K b ＝ L a))

  horizontal-first-cogap-join-constant-data-cogap-join-constant-data :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X) →
    cogap-join-constant-data d z →
    horizontal-first-cogap-join-constant-data d z
  horizontal-first-cogap-join-constant-data-cogap-join-constant-data
    d z (K , L , M) =
    (L , K , M)

  is-equiv-horizontal-first-cogap-join-constant-data-cogap-join-constant-data :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X) →
    is-equiv
      ( horizontal-first-cogap-join-constant-data-cogap-join-constant-data
        d z)
  is-equiv-horizontal-first-cogap-join-constant-data-cogap-join-constant-data
    d z =
    is-equiv-map-left-swap-Σ

  dependent-cocone-horizontal-first-cogap-join-constant-data :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4} →
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X) →
    horizontal-first-cogap-join-constant-data d z →
    dependent-cocone pr1 pr2 (cocone-join {A = A'} {B = B'})
      ( λ x → cogap-join X d x ＝ z)
  pr1
    ( dependent-cocone-horizontal-first-cogap-join-constant-data
      d z (L , K , M)) a =
    compute-inl-cogap-join d a ∙ L a
  pr1
    ( pr2
      ( dependent-cocone-horizontal-first-cogap-join-constant-data
        d z (L , K , M))) b =
    compute-inr-cogap-join d b ∙ K b
  pr2
    ( pr2
      ( dependent-cocone-horizontal-first-cogap-join-constant-data
        { A' = A'}
        { B' = B'}
        d z (L , K , M)))
    ( a , b) =
    map-compute-dependent-identification-eq-value-function
      ( F)
      ( λ _ → z)
      ( glue-join (a , b))
      ( compute-inl-cogap-join d a ∙ L a)
      ( compute-inr-cogap-join d b ∙ K b)
      ( coherence-square-cogap-join-constant-data d z K L a b (M a b))
    where
    F : A' * B' → _
    F = cogap-join _ d

  is-equiv-dependent-cocone-horizontal-first-cogap-join-constant-data :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X) →
    is-equiv
      ( dependent-cocone-horizontal-first-cogap-join-constant-data
        { A' = A'}
        { B' = B'}
        d z)
  is-equiv-dependent-cocone-horizontal-first-cogap-join-constant-data
    { A' = A'}
    { B' = B'}
    d z =
    is-equiv-htpy
      ( map-Σ D f g)
      ( λ (L , K , M) →
        eq-htpy-dependent-cocone pr1 pr2 cocone-join
          ( λ x → F x ＝ z)
          ( dependent-cocone-horizontal-first-cogap-join-constant-data
            d z (L , K , M))
          ( map-Σ D f g (L , K , M))
          ( refl-htpy ,
            refl-htpy ,
            λ (a , b) →
              right-unit ∙
              inv
                ( htpy-eq
                  ( htpy-eq
                    ( is-section-map-inv-equiv equiv-ev-pair
                      ( coherence-curried L K M))
                    ( a))
                  ( b)) ∙
              inv left-unit))
      ( is-equiv-map-Σ D is-equiv-f is-equiv-g)
    where
    F : A' * B' → _
    F = cogap-join _ d

    f :
      ( (a : A') → horizontal-map-cocone pr1 pr2 d a ＝ z) →
      ( (a : A') → F (inl-join a) ＝ z)
    f L a = compute-inl-cogap-join d a ∙ L a

    D :
      ( (a : A') → F (inl-join a) ＝ z) →
      UU _
    D α =
      Σ ( (b : B') → F (inr-join b) ＝ z)
        ( λ β →
          (t : A' × B') →
          dependent-identification
            ( λ x → F x ＝ z)
            ( glue-join t)
            ( α (pr1 t))
            ( β (pr2 t)))

    E :
      (L : (a : A') → horizontal-map-cocone pr1 pr2 d a ＝ z) →
      ( (b : B') → F (inr-join b) ＝ z) →
      UU _
    E L β =
      (t : A' × B') →
      dependent-identification
        ( λ x → F x ＝ z)
        ( glue-join t)
        ( compute-inl-cogap-join d (pr1 t) ∙ L (pr1 t))
        ( β (pr2 t))

    g :
      (L : (a : A') → horizontal-map-cocone pr1 pr2 d a ＝ z) →
      Σ ( (b : B') → vertical-map-cocone pr1 pr2 d b ＝ z)
        ( λ K →
          (a : A') (b : B') →
          coherence-square-cocone pr1 pr2 d (a , b) ∙ K b ＝ L a) →
      D (f L)
    pr1 (g L (K , M)) b = compute-inr-cogap-join d b ∙ K b
    pr2 (g L (K , M)) =
      map-inv-equiv equiv-ev-pair
        ( λ a b →
          map-compute-dependent-identification-eq-value-function
            ( F)
            ( λ _ → z)
            ( glue-join (a , b))
            ( compute-inl-cogap-join d a ∙ L a)
            ( compute-inr-cogap-join d b ∙ K b)
            ( coherence-square-cogap-join-constant-data d z K L a b (M a b)))

    coherence-curried :
      (L : (a : A') → horizontal-map-cocone pr1 pr2 d a ＝ z)
      (K : (b : B') → vertical-map-cocone pr1 pr2 d b ＝ z)
      (M :
        (a : A') (b : B') →
        coherence-square-cocone pr1 pr2 d (a , b) ∙ K b ＝ L a) →
      (a : A') (b : B') →
      dependent-identification
        ( λ x → F x ＝ z)
        ( glue-join (a , b))
        ( compute-inl-cogap-join d a ∙ L a)
        ( compute-inr-cogap-join d b ∙ K b)
    coherence-curried L K M a b =
      map-compute-dependent-identification-eq-value-function
        ( F)
        ( λ _ → z)
        ( glue-join (a , b))
        ( compute-inl-cogap-join d a ∙ L a)
        ( compute-inr-cogap-join d b ∙ K b)
        ( coherence-square-cogap-join-constant-data d z K L a b (M a b))

    is-equiv-f : is-equiv f
    is-equiv-f =
      is-equiv-map-Π-is-fiberwise-equiv
        ( λ a → is-equiv-concat (compute-inl-cogap-join d a) z)

    coherence-map :
      (L : (a : A') → horizontal-map-cocone pr1 pr2 d a ＝ z)
      (K : (b : B') → vertical-map-cocone pr1 pr2 d b ＝ z) →
      ( (a : A') (b : B') →
        coherence-square-cocone pr1 pr2 d (a , b) ∙ K b ＝ L a) →
      (t : A' × B') →
      dependent-identification
        ( λ x → F x ＝ z)
        ( glue-join t)
        ( compute-inl-cogap-join d (pr1 t) ∙ L (pr1 t))
        ( compute-inr-cogap-join d (pr2 t) ∙ K (pr2 t))
    coherence-map L K M =
      map-inv-equiv equiv-ev-pair
        ( λ a b →
          map-compute-dependent-identification-eq-value-function
            ( F)
            ( λ _ → z)
            ( glue-join (a , b))
            ( compute-inl-cogap-join d a ∙ L a)
            ( compute-inr-cogap-join d b ∙ K b)
            ( coherence-square-cogap-join-constant-data d z K L a b (M a b)))

    is-equiv-coherence-map :
      (L : (a : A') → horizontal-map-cocone pr1 pr2 d a ＝ z)
      (K : (b : B') → vertical-map-cocone pr1 pr2 d b ＝ z) →
      is-equiv (coherence-map L K)
    is-equiv-coherence-map L K =
      is-equiv-comp
        ( map-inv-equiv equiv-ev-pair)
        ( λ M a b →
          map-compute-dependent-identification-eq-value-function
            ( F)
            ( λ _ → z)
            ( glue-join (a , b))
            ( compute-inl-cogap-join d a ∙ L a)
            ( compute-inr-cogap-join d b ∙ K b)
            ( coherence-square-cogap-join-constant-data
              d z K L a b (M a b)))
        ( is-equiv-map-Π-is-fiberwise-equiv
          ( λ a →
            is-equiv-map-Π-is-fiberwise-equiv
              ( λ b →
                is-equiv-comp
                  ( map-compute-dependent-identification-eq-value-function
                    ( F)
                    ( λ _ → z)
                    ( glue-join (a , b))
                    ( compute-inl-cogap-join d a ∙ L a)
                    ( compute-inr-cogap-join d b ∙ K b))
                  ( coherence-square-cogap-join-constant-data d z K L a b)
                  ( is-equiv-coherence-square-cogap-join-constant-data
                    d z K L a b)
                  ( is-equiv-map-compute-dependent-identification-eq-value-function
                    ( F)
                    ( λ _ → z)
                    ( glue-join (a , b))
                    ( compute-inl-cogap-join d a ∙ L a)
                    ( compute-inr-cogap-join d b ∙ K b)))))
        ( is-equiv-map-inv-equiv equiv-ev-pair)

    is-equiv-g :
      (L : (a : A') → horizontal-map-cocone pr1 pr2 d a ＝ z) →
      is-equiv (g L)
    is-equiv-g L =
      is-equiv-map-Σ (E L)
        ( is-equiv-map-Π-is-fiberwise-equiv
          ( λ b → is-equiv-concat (compute-inr-cogap-join d b) z))
        ( is-equiv-coherence-map L)

  dependent-cocone-cogap-join-constant :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4} →
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X) →
    (K : (b : B') → vertical-map-cocone pr1 pr2 d b ＝ z) →
    (L : (a : A') → horizontal-map-cocone pr1 pr2 d a ＝ z) →
    ( (a : A') (b : B') →
      coherence-square-cocone pr1 pr2 d (a , b) ∙ K b ＝ L a) →
    dependent-cocone pr1 pr2 (cocone-join {A = A'} {B = B'})
      ( λ x → cogap-join X d x ＝ z)
  pr1 (dependent-cocone-cogap-join-constant d z K L M) a =
    compute-inl-cogap-join d a ∙ L a
  pr1 (pr2 (dependent-cocone-cogap-join-constant d z K L M)) b =
    compute-inr-cogap-join d b ∙ K b
  pr2
    ( pr2
      ( dependent-cocone-cogap-join-constant
        { A' = A'}
        { B' = B'}
        d z K L M))
    ( a , b) =
    map-compute-dependent-identification-eq-value-function
      ( F)
      ( λ _ → z)
      ( p)
      ( compute-inl-F a ∙ L a)
      ( compute-inr-F b ∙ K b)
      ( coherence-square-cogap-join-constant-data d z K L a b (M a b))
    where
    F : A' * B' → _
    F = cogap-join _ d

    p = glue-join (a , b)

    compute-inl-F : F ∘ inl-join ~ horizontal-map-cocone pr1 pr2 d
    compute-inl-F = compute-inl-cogap-join d

    compute-inr-F : F ∘ inr-join ~ vertical-map-cocone pr1 pr2 d
    compute-inr-F = compute-inr-cogap-join d

  dependent-cocone-cogap-join-constant-data :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X) →
    cogap-join-constant-data d z →
    dependent-cocone pr1 pr2 (cocone-join {A = A'} {B = B'})
      ( λ x → cogap-join X d x ＝ z)
  dependent-cocone-cogap-join-constant-data d z (K , L , M) =
    dependent-cocone-cogap-join-constant d z K L M

  is-equiv-dependent-cocone-cogap-join-constant-data :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X) →
    is-equiv (dependent-cocone-cogap-join-constant-data d z)
  is-equiv-dependent-cocone-cogap-join-constant-data d z =
    is-equiv-htpy
      ( dependent-cocone-horizontal-first-cogap-join-constant-data d z ∘
        horizontal-first-cogap-join-constant-data-cogap-join-constant-data
          d z)
      ( refl-htpy)
      ( is-equiv-comp
        ( dependent-cocone-horizontal-first-cogap-join-constant-data d z)
        ( horizontal-first-cogap-join-constant-data-cogap-join-constant-data
          d z)
        ( is-equiv-horizontal-first-cogap-join-constant-data-cogap-join-constant-data
          d z)
        ( is-equiv-dependent-cocone-horizontal-first-cogap-join-constant-data
          d z))

  equiv-dependent-cocone-cogap-join-constant-data :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X) →
    cogap-join-constant-data d z ≃
    dependent-cocone pr1 pr2 (cocone-join {A = A'} {B = B'})
      ( λ x → cogap-join X d x ＝ z)
  pr1 (equiv-dependent-cocone-cogap-join-constant-data d z) =
    dependent-cocone-cogap-join-constant-data d z
  pr2 (equiv-dependent-cocone-cogap-join-constant-data d z) =
    is-equiv-dependent-cocone-cogap-join-constant-data d z

  is-equiv-map-Π-dependent-cocone-cogap-join-constant-data :
    {l1' l2' l3' l4 : Level}
    {A' : UU l1'} {B' : UU l2'} {C' : UU l3'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (k : C' → X) →
    is-equiv
      ( λ (R : (c : C') → cogap-join-constant-data d (k c)) c →
        dependent-cocone-cogap-join-constant-data d (k c) (R c))
  is-equiv-map-Π-dependent-cocone-cogap-join-constant-data d k =
    is-equiv-map-Π-is-fiberwise-equiv
      ( λ c → is-equiv-dependent-cocone-cogap-join-constant-data d (k c))

  cogap-join-constant-data-dependent-cocone :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X) →
    dependent-cocone pr1 pr2 (cocone-join {A = A'} {B = B'})
      ( λ x → cogap-join X d x ＝ z) →
    cogap-join-constant-data d z
  pr1 (cogap-join-constant-data-dependent-cocone d z E) b =
    inv (compute-inr-cogap-join d b) ∙ pr1 (pr2 E) b
  pr1 (pr2 (cogap-join-constant-data-dependent-cocone d z E)) a =
    inv (compute-inl-cogap-join d a) ∙ pr1 E a
  pr2
    ( pr2
      ( cogap-join-constant-data-dependent-cocone
        { A' = A'}
        { B' = B'}
        d z E))
    a b =
    equational-reasoning
      H (a , b) ∙ (inv rinr ∙ β)
      ＝ (H (a , b) ∙ inv rinr) ∙ β
        by inv (assoc (H (a , b)) (inv rinr) β)
      ＝ (inv linl ∙ apF) ∙ β
        by ap (_∙ β) (inv (right-transpose-compute-glue-cogap-join d a b))
      ＝ inv linl ∙ (apF ∙ β)
        by assoc (inv linl) apF β
      ＝ inv linl ∙ (α ∙ ap (λ _ → z) p)
        by ap (inv linl ∙_) coh-E
      ＝ (inv linl ∙ α) ∙ ap (λ _ → z) p
        by inv (assoc (inv linl) α (ap (λ _ → z) p))
      ＝ (inv linl ∙ α) ∙ refl
        by ap ((inv linl ∙ α) ∙_) (ap-const z p)
      ＝ inv linl ∙ α
        by right-unit
    where
    F : A' * B' → _
    F = cogap-join _ d

    H = coherence-square-cocone pr1 pr2 d

    p = glue-join (a , b)
    linl = compute-inl-cogap-join d a
    rinr = compute-inr-cogap-join d b
    apF = ap F p
    α = pr1 E a
    β = pr1 (pr2 E) b

    coh-E :
      ap F p ∙ β ＝ α ∙ ap (λ _ → z) p
    coh-E =
      map-inv-compute-dependent-identification-eq-value-function
        ( F)
        ( λ _ → z)
        ( p)
        ( α)
        ( β)
        ( pr2 (pr2 E) (a , b))

  horizontal-htpy-section-cogap-join-constant-data-dependent-cocone :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X)
    (E :
      dependent-cocone pr1 pr2 (cocone-join {A = A'} {B = B'})
        ( λ x → cogap-join X d x ＝ z)) →
    pr1
      ( dependent-cocone-cogap-join-constant-data d z
        ( cogap-join-constant-data-dependent-cocone d z E)) ~
    pr1 E
  horizontal-htpy-section-cogap-join-constant-data-dependent-cocone d z E a =
    is-section-inv-concat (compute-inl-cogap-join d a) (pr1 E a)

  vertical-htpy-section-cogap-join-constant-data-dependent-cocone :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X)
    (E :
      dependent-cocone pr1 pr2 (cocone-join {A = A'} {B = B'})
        ( λ x → cogap-join X d x ＝ z)) →
    pr1
      ( pr2
        ( dependent-cocone-cogap-join-constant-data d z
          ( cogap-join-constant-data-dependent-cocone d z E))) ~
    pr1 (pr2 E)
  vertical-htpy-section-cogap-join-constant-data-dependent-cocone d z E b =
    is-section-inv-concat (compute-inr-cogap-join d b) (pr1 (pr2 E) b)

  vertical-htpy-retraction-cogap-join-constant-data-dependent-cocone :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X)
    (R : cogap-join-constant-data d z) →
    pr1
      ( cogap-join-constant-data-dependent-cocone d z
        ( dependent-cocone-cogap-join-constant-data d z R)) ~
    pr1 R
  vertical-htpy-retraction-cogap-join-constant-data-dependent-cocone
    d z (K , L , M) b =
    is-retraction-inv-concat (compute-inr-cogap-join d b) (K b)

  horizontal-htpy-retraction-cogap-join-constant-data-dependent-cocone :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X)
    (R : cogap-join-constant-data d z) →
    pr1
      ( pr2
        ( cogap-join-constant-data-dependent-cocone d z
          ( dependent-cocone-cogap-join-constant-data d z R))) ~
    pr1 (pr2 R)
  horizontal-htpy-retraction-cogap-join-constant-data-dependent-cocone
    d z (K , L , M) a =
    is-retraction-inv-concat (compute-inl-cogap-join d a) (L a)

  constant-cogap-join-data :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4} →
    cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X →
    X → UU (l1' ⊔ l2' ⊔ l4)
  constant-cogap-join-data d z =
    Σ ( (a : _) → z ＝ horizontal-map-cocone pr1 pr2 d a)
      ( λ H →
        Σ ( (b : _) → z ＝ vertical-map-cocone pr1 pr2 d b)
          ( λ L →
            (a : _) (b : _) →
            H a ∙ coherence-square-cocone pr1 pr2 d (a , b) ＝ L b))

  constant-cogap-join-data-cocone-map-dependent-function :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (j : A' * B' → X) (z : X) →
    ((x : A' * B') → z ＝ j x) →
    constant-cogap-join-data
      ( cocone-map
        { S = A' × B'}
        { A = A'}
        { B = B'}
        pr1 pr2
        { X = A' * B'}
        { Y = X}
        ( cocone-join {A = A'} {B = B'}) j)
      ( z)
  pr1
    ( constant-cogap-join-data-cocone-map-dependent-function
      { A' = A'}
      { B' = B'}
      j z H) a =
    H (inl-join {A = A'} {B = B'} a)
  pr1
    ( pr2
      ( constant-cogap-join-data-cocone-map-dependent-function
        { A' = A'}
        { B' = B'}
        j z H)) b =
    H (inr-join {A = A'} {B = B'} b)
  pr2
    ( pr2
      ( constant-cogap-join-data-cocone-map-dependent-function
        { A' = A'}
        { B' = B'}
        j z H))
    a b =
    equational-reasoning
      H (inl-join {A = A'} {B = B'} a) ∙ ap j p
      ＝ ap (λ _ → z) p ∙ H (inr-join {A = A'} {B = B'} b)
        by inv (naturality-homotopy H p)
      ＝ refl ∙ H (inr-join {A = A'} {B = B'} b)
        by ap (_∙ H (inr-join {A = A'} {B = B'} b)) (ap-const z p)
      ＝ H (inr-join {A = A'} {B = B'} b)
        by left-unit
    where
    p = glue-join {A = A'} {B = B'} (a , b)

  coherence-constant-cogap-join-data-dependent-cocone-cocone-map :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (j : A' * B' → X) (z : X)
    (H : (a : A') → z ＝ j (inl-join a))
    (L : (b : B') → z ＝ j (inr-join b)) →
    (a : A') (b : B') →
    dependent-identification
      ( λ x → z ＝ j x)
      ( glue-join (a , b))
      ( H a)
      ( L b) →
    H a ∙ ap j (glue-join (a , b)) ＝ L b
  coherence-constant-cogap-join-data-dependent-cocone-cocone-map
    j z H L a b M =
    inv coh-M ∙
    ( ap (λ q → q ∙ L b) (ap-const z p) ∙
      left-unit)
    where
    p = glue-join (a , b)

    coh-M :
      ap (λ _ → z) p ∙ L b ＝ H a ∙ ap j p
    coh-M =
      map-inv-compute-dependent-identification-eq-value-function
        ( λ _ → z)
        ( j)
        ( p)
        ( H a)
        ( L b)
        ( M)

  is-equiv-coherence-constant-cogap-join-data-dependent-cocone-cocone-map :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (j : A' * B' → X) (z : X)
    (H : (a : A') → z ＝ j (inl-join a))
    (L : (b : B') → z ＝ j (inr-join b))
    (a : A') (b : B') →
    is-equiv
      ( coherence-constant-cogap-join-data-dependent-cocone-cocone-map
        j z H L a b)
  is-equiv-coherence-constant-cogap-join-data-dependent-cocone-cocone-map
    j z H L a b =
    is-equiv-comp
      ( concat' (H a ∙ ap j p) simplify-left)
      ( inv ∘
        map-inv-compute-dependent-identification-eq-value-function
          ( λ _ → z)
          ( j)
          ( p)
          ( H a)
          ( L b))
      ( is-equiv-comp
        ( inv)
        ( map-inv-compute-dependent-identification-eq-value-function
          ( λ _ → z)
          ( j)
          ( p)
          ( H a)
          ( L b))
        ( is-equiv-map-inv-equiv
          ( compute-dependent-identification-eq-value-function
            ( λ _ → z)
            ( j)
            ( p)
            ( H a)
            ( L b)))
        ( is-equiv-inv
          ( ap (λ _ → z) p ∙ L b)
          ( H a ∙ ap j p)))
      ( is-equiv-concat' (H a ∙ ap j p) simplify-left)
    where
    p = glue-join (a , b)

    simplify-left : ap (λ _ → z) p ∙ L b ＝ L b
    simplify-left =
      ap (λ q → q ∙ L b) (ap-const z p) ∙
      left-unit

  constant-cogap-join-data-dependent-cocone-cocone-map :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (j : A' * B' → X) (z : X) →
    dependent-cocone pr1 pr2 (cocone-join {A = A'} {B = B'})
      ( λ x → z ＝ j x) →
    constant-cogap-join-data
      ( cocone-map
        { S = A' × B'}
        { A = A'}
        { B = B'}
        pr1 pr2
        { X = A' * B'}
        { Y = X}
        ( cocone-join {A = A'} {B = B'}) j)
      ( z)
  pr1 (constant-cogap-join-data-dependent-cocone-cocone-map j z E) =
    pr1 E
  pr1 (pr2 (constant-cogap-join-data-dependent-cocone-cocone-map j z E)) =
    pr1 (pr2 E)
  pr2
    ( pr2 (constant-cogap-join-data-dependent-cocone-cocone-map j z E))
    a b =
    coherence-constant-cogap-join-data-dependent-cocone-cocone-map
      j z
      ( pr1 E)
      ( pr1 (pr2 E))
      ( a)
      ( b)
      ( pr2 (pr2 E) (a , b))

  is-equiv-constant-cogap-join-data-dependent-cocone-cocone-map :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (j : A' * B' → X) (z : X) →
    is-equiv (constant-cogap-join-data-dependent-cocone-cocone-map j z)
  is-equiv-constant-cogap-join-data-dependent-cocone-cocone-map
    { A' = A'}
    { B' = B'}
    j z =
    is-equiv-map-Σ D is-equiv-id is-equiv-g
    where
    D :
      ((a : A') → z ＝ j (inl-join a)) →
      UU _
    D H =
      Σ ( (b : B') → z ＝ j (inr-join b))
        ( λ L →
          (a : A') (b : B') →
          H a ∙ ap j (glue-join (a , b)) ＝ L b)

    E :
      ((a : A') → z ＝ j (inl-join a)) →
      ((b : B') → z ＝ j (inr-join b)) →
      UU _
    E H L =
      (t : A' × B') →
      dependent-identification
        ( λ x → z ＝ j x)
        ( glue-join t)
        ( H (pr1 t))
        ( L (pr2 t))

    coherence-map :
      (H : (a : A') → z ＝ j (inl-join a))
      (L : (b : B') → z ＝ j (inr-join b)) →
      E H L →
      (a : A') (b : B') →
      H a ∙ ap j (glue-join (a , b)) ＝ L b
    coherence-map H L M a b =
      coherence-constant-cogap-join-data-dependent-cocone-cocone-map
        j z H L a b (M (a , b))

    is-equiv-coherence-map :
      (H : (a : A') → z ＝ j (inl-join a))
      (L : (b : B') → z ＝ j (inr-join b)) →
      is-equiv (coherence-map H L)
    is-equiv-coherence-map H L =
      is-equiv-comp
        ( λ M a b →
          coherence-constant-cogap-join-data-dependent-cocone-cocone-map
            j z H L a b (M a b))
        ( map-equiv equiv-ev-pair)
        ( is-equiv-map-equiv equiv-ev-pair)
        ( is-equiv-map-Π-is-fiberwise-equiv
          ( λ a →
            is-equiv-map-Π-is-fiberwise-equiv
              ( λ b →
                is-equiv-coherence-constant-cogap-join-data-dependent-cocone-cocone-map
                  j z H L a b)))

    g :
      (H : (a : A') → z ＝ j (inl-join a)) →
      Σ ( (b : B') → z ＝ j (inr-join b))
        ( λ L → E H L) →
      D H
    pr1 (g H (L , M)) = L
    pr2 (g H (L , M)) = coherence-map H L M

    is-equiv-g :
      (H : (a : A') → z ＝ j (inl-join a)) →
      is-equiv (g H)
    is-equiv-g H =
      is-equiv-map-Σ (λ L → (a : A') (b : B') →
        H a ∙ ap j (glue-join (a , b)) ＝ L b)
        ( is-equiv-id)
        ( is-equiv-coherence-map H)

  constant-cogap-join-data-dependent-cocone-map-dependent-function :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (j : A' * B' → X) (z : X) →
    ((x : A' * B') → z ＝ j x) →
    constant-cogap-join-data
      ( cocone-map
        { S = A' × B'}
        { A = A'}
        { B = B'}
        pr1 pr2
        { X = A' * B'}
        { Y = X}
        ( cocone-join {A = A'} {B = B'}) j)
      ( z)
  constant-cogap-join-data-dependent-cocone-map-dependent-function
    { A' = A'}
    { B' = B'}
    j z H =
    constant-cogap-join-data-dependent-cocone-cocone-map j z
      ( dependent-cocone-map pr1 pr2
        ( cocone-join {A = A'} {B = B'})
        ( λ x → z ＝ j x)
        ( H))

  is-equiv-constant-cogap-join-data-dependent-cocone-map-dependent-function :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (j : A' * B' → X) (z : X) →
    is-equiv
      ( constant-cogap-join-data-dependent-cocone-map-dependent-function
        j z)
  is-equiv-constant-cogap-join-data-dependent-cocone-map-dependent-function
    { A' = A'}
    { B' = B'}
    j z =
    is-equiv-comp
      ( constant-cogap-join-data-dependent-cocone-cocone-map j z)
      ( dependent-cocone-map pr1 pr2
        ( cocone-join {A = A'} {B = B'})
        ( λ x → z ＝ j x))
      ( is-equiv-dependent-cocone-map-standard-join)
      ( is-equiv-constant-cogap-join-data-dependent-cocone-cocone-map j z)

  htpy-constant-cogap-join-data-dependent-cocone-map-dependent-function :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (j : A' * B' → X) (z : X) →
    constant-cogap-join-data-dependent-cocone-map-dependent-function j z ~
    constant-cogap-join-data-cocone-map-dependent-function j z
  htpy-constant-cogap-join-data-dependent-cocone-map-dependent-function
    { A' = A'}
    { B' = B'}
    j z H =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( eq-htpy
          ( λ a →
            eq-htpy
              ( λ b →
                inv
                  ( assoc
                    ( inv (coh {a} {b}))
                    ( simplify-left a b)
                    ( left-unit)) ∙
                ap
                  ( λ q →
                    ( inv q ∙ simplify-left a b) ∙ left-unit)
                  ( nat-htpy-apd-htpy (λ _ → z) j H (p a b))))))
    where
    p : (a : A') (b : B') → inl-join a ＝ inr-join b
    p a b = glue-join (a , b)

    simplify-left :
      (a : A') (b : B') →
      ap (λ _ → z) (p a b) ∙ H (inr-join b) ＝
      refl ∙ H (inr-join b)
    simplify-left a b =
      ap (λ r → r ∙ H (inr-join b)) (ap-const z (p a b))

    coh :
      {a : A'} {b : B'} →
      ap (λ _ → z) (p a b) ∙ H (inr-join b) ＝
      H (inl-join a) ∙ ap j (p a b)
    coh {a} {b} =
      map-inv-compute-dependent-identification-eq-value-function
        ( λ _ → z)
        ( j)
        ( p a b)
        ( H (inl-join a))
        ( H (inr-join b))
        ( apd H (p a b))

  is-equiv-constant-cogap-join-data-cocone-map-dependent-function :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (j : A' * B' → X) (z : X) →
    is-equiv (constant-cogap-join-data-cocone-map-dependent-function j z)
  is-equiv-constant-cogap-join-data-cocone-map-dependent-function j z =
    is-equiv-htpy'
      ( constant-cogap-join-data-dependent-cocone-map-dependent-function j z)
      ( htpy-constant-cogap-join-data-dependent-cocone-map-dependent-function
        j z)
      ( is-equiv-constant-cogap-join-data-dependent-cocone-map-dependent-function
        j z)

  coherence-square-constant-cogap-join-data :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4} →
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X)
    (H : (a : A') → z ＝ horizontal-map-cocone pr1 pr2 d a)
    (L : (b : B') → z ＝ vertical-map-cocone pr1 pr2 d b) →
    (a : A') (b : B') →
    H a ∙ coherence-square-cocone pr1 pr2 d (a , b) ＝ L b →
    coherence-square-identifications
      ( H a ∙ inv (compute-inl-cogap-join d a))
      ( ap (λ _ → z) (glue-join (a , b)))
      ( ap (cogap-join X d) (glue-join (a , b)))
      ( L b ∙ inv (compute-inr-cogap-join d b))
  coherence-square-constant-cogap-join-data
    { A' = A'}
    { B' = B'}
    d z H L a b M =
    concat Pleft final
      ( concat' middle Pright (ap (concat' z (inv rinr)) (inv M)))
    where
    F : A' * B' → _
    F = cogap-join _ d

    H' = coherence-square-cocone pr1 pr2 d

    p = glue-join (a , b)
    linl = compute-inl-cogap-join d a
    rinr = compute-inr-cogap-join d b
    apF = ap F p

    start = ap (λ _ → z) p ∙ (L b ∙ inv rinr)
    middle = L b ∙ inv rinr
    final = (H a ∙ inv linl) ∙ apF

    Pleft : start ＝ middle
    Pleft =
      ap (_∙ (L b ∙ inv rinr)) (ap-const z p) ∙
      left-unit

    Pright : (H a ∙ H' (a , b)) ∙ inv rinr ＝ final
    Pright =
      assoc (H a) (H' (a , b)) (inv rinr) ∙
      ap
        ( H a ∙_)
        ( inv (right-transpose-compute-glue-cogap-join d a b)) ∙
      inv (assoc (H a) (inv linl) apF)

  is-equiv-coherence-square-constant-cogap-join-data :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X)
    (H : (a : A') → z ＝ horizontal-map-cocone pr1 pr2 d a)
    (L : (b : B') → z ＝ vertical-map-cocone pr1 pr2 d b)
    (a : A') (b : B') →
    is-equiv (coherence-square-constant-cogap-join-data d z H L a b)
  is-equiv-coherence-square-constant-cogap-join-data
    { A' = A'}
    { B' = B'}
    d z H L a b =
    is-equiv-comp
      ( concat Pleft final)
      ( concat' middle Pright ∘ ap (concat' z (inv rinr)) ∘ inv)
      ( is-equiv-comp
        ( concat' middle Pright)
        ( ap (concat' z (inv rinr)) ∘ inv)
        ( is-equiv-comp
          ( ap (concat' z (inv rinr)))
          ( inv)
          ( is-equiv-inv (H a ∙ H' (a , b)) (L b))
          ( is-emb-is-equiv
            ( is-equiv-concat' z (inv rinr))
            ( L b)
            ( H a ∙ H' (a , b))))
        ( is-equiv-concat' middle Pright))
      ( is-equiv-concat Pleft final)
    where
    F : A' * B' → _
    F = cogap-join _ d

    H' = coherence-square-cocone pr1 pr2 d

    p = glue-join (a , b)
    linl = compute-inl-cogap-join d a
    rinr = compute-inr-cogap-join d b
    apF = ap F p

    start = ap (λ _ → z) p ∙ (L b ∙ inv rinr)
    middle = L b ∙ inv rinr
    final = (H a ∙ inv linl) ∙ apF

    Pleft : start ＝ middle
    Pleft =
      ap (_∙ (L b ∙ inv rinr)) (ap-const z p) ∙
      left-unit

    Pright : (H a ∙ H' (a , b)) ∙ inv rinr ＝ final
    Pright =
      assoc (H a) (H' (a , b)) (inv rinr) ∙
      ap
        ( H a ∙_)
        ( inv (right-transpose-compute-glue-cogap-join d a b)) ∙
      inv (assoc (H a) (inv linl) apF)

  dependent-cocone-constant-cogap-join :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4} →
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X) →
    (H : (a : A') → z ＝ horizontal-map-cocone pr1 pr2 d a) →
    (L : (b : B') → z ＝ vertical-map-cocone pr1 pr2 d b) →
    ( (a : A') (b : B') →
      H a ∙ coherence-square-cocone pr1 pr2 d (a , b) ＝ L b) →
    dependent-cocone pr1 pr2 (cocone-join {A = A'} {B = B'})
      ( λ x → z ＝ cogap-join X d x)
  pr1 (dependent-cocone-constant-cogap-join d z H L M) a =
    H a ∙ inv (compute-inl-cogap-join d a)
  pr1 (pr2 (dependent-cocone-constant-cogap-join d z H L M)) b =
    L b ∙ inv (compute-inr-cogap-join d b)
  pr2
    ( pr2
      ( dependent-cocone-constant-cogap-join
        { A' = A'}
        { B' = B'}
        d z H L M))
    ( a , b) =
    map-compute-dependent-identification-eq-value-function
      ( λ _ → z)
      ( F)
      ( p)
      ( H a ∙ inv (compute-inl-F a))
      ( L b ∙ inv (compute-inr-F b))
      ( coherence-square-constant-cogap-join-data d z H L a b (M a b))
    where
    F : A' * B' → _
    F = cogap-join _ d

    p = glue-join (a , b)

    compute-inl-F : F ∘ inl-join ~ horizontal-map-cocone pr1 pr2 d
    compute-inl-F = compute-inl-cogap-join d

    compute-inr-F : F ∘ inr-join ~ vertical-map-cocone pr1 pr2 d
    compute-inr-F = compute-inr-cogap-join d

  dependent-cocone-constant-cogap-join-data :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X) →
    constant-cogap-join-data d z →
    dependent-cocone pr1 pr2 (cocone-join {A = A'} {B = B'})
      ( λ x → z ＝ cogap-join X d x)
  dependent-cocone-constant-cogap-join-data d z (H , L , M) =
    dependent-cocone-constant-cogap-join d z H L M

  is-equiv-dependent-cocone-constant-cogap-join-data :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X) →
    is-equiv (dependent-cocone-constant-cogap-join-data d z)
  is-equiv-dependent-cocone-constant-cogap-join-data
    { A' = A'}
    { B' = B'}
    d z =
    is-equiv-htpy
      ( map-Σ D f g)
      ( λ (H , L , M) →
        eq-htpy-dependent-cocone pr1 pr2 cocone-join
          ( λ x → z ＝ F x)
          ( dependent-cocone-constant-cogap-join-data d z (H , L , M))
          ( map-Σ D f g (H , L , M))
          ( refl-htpy ,
            refl-htpy ,
            λ (a , b) →
              right-unit ∙
              inv
                ( htpy-eq
                  ( htpy-eq
                    ( is-section-map-inv-equiv equiv-ev-pair
                      ( coherence-curried H L M))
                    ( a))
                  ( b)) ∙
              inv left-unit))
      ( is-equiv-map-Σ D is-equiv-f is-equiv-g)
    where
    F : A' * B' → _
    F = cogap-join _ d

    f :
      ( (a : A') → z ＝ horizontal-map-cocone pr1 pr2 d a) →
      ( (a : A') → z ＝ F (inl-join a))
    f H a = H a ∙ inv (compute-inl-cogap-join d a)

    D :
      ( (a : A') → z ＝ F (inl-join a)) →
      UU _
    D α =
      Σ ( (b : B') → z ＝ F (inr-join b))
        ( λ β →
          (t : A' × B') →
          dependent-identification
            ( λ x → z ＝ F x)
            ( glue-join t)
            ( α (pr1 t))
            ( β (pr2 t)))

    E :
      (H : (a : A') → z ＝ horizontal-map-cocone pr1 pr2 d a) →
      ( (b : B') → z ＝ F (inr-join b)) →
      UU _
    E H β =
      (t : A' × B') →
      dependent-identification
        ( λ x → z ＝ F x)
        ( glue-join t)
        ( H (pr1 t) ∙ inv (compute-inl-cogap-join d (pr1 t)))
        ( β (pr2 t))

    g :
      (H : (a : A') → z ＝ horizontal-map-cocone pr1 pr2 d a) →
      Σ ( (b : B') → z ＝ vertical-map-cocone pr1 pr2 d b)
        ( λ L →
          (a : A') (b : B') →
          H a ∙ coherence-square-cocone pr1 pr2 d (a , b) ＝ L b) →
      D (f H)
    pr1 (g H (L , M)) b = L b ∙ inv (compute-inr-cogap-join d b)
    pr2 (g H (L , M)) =
      map-inv-equiv equiv-ev-pair
        ( λ a b →
          map-compute-dependent-identification-eq-value-function
            ( λ _ → z)
            ( F)
            ( glue-join (a , b))
            ( H a ∙ inv (compute-inl-cogap-join d a))
            ( L b ∙ inv (compute-inr-cogap-join d b))
            ( coherence-square-constant-cogap-join-data d z H L a b (M a b)))

    coherence-curried :
      (H : (a : A') → z ＝ horizontal-map-cocone pr1 pr2 d a)
      (L : (b : B') → z ＝ vertical-map-cocone pr1 pr2 d b)
      (M :
        (a : A') (b : B') →
        H a ∙ coherence-square-cocone pr1 pr2 d (a , b) ＝ L b) →
      (a : A') (b : B') →
      dependent-identification
        ( λ x → z ＝ F x)
        ( glue-join (a , b))
        ( H a ∙ inv (compute-inl-cogap-join d a))
        ( L b ∙ inv (compute-inr-cogap-join d b))
    coherence-curried H L M a b =
      map-compute-dependent-identification-eq-value-function
        ( λ _ → z)
        ( F)
        ( glue-join (a , b))
        ( H a ∙ inv (compute-inl-cogap-join d a))
        ( L b ∙ inv (compute-inr-cogap-join d b))
        ( coherence-square-constant-cogap-join-data d z H L a b (M a b))

    is-equiv-f : is-equiv f
    is-equiv-f =
      is-equiv-map-Π-is-fiberwise-equiv
        ( λ a →
          is-equiv-concat' z (inv (compute-inl-cogap-join d a)))

    coherence-map :
      (H : (a : A') → z ＝ horizontal-map-cocone pr1 pr2 d a)
      (L : (b : B') → z ＝ vertical-map-cocone pr1 pr2 d b) →
      ( (a : A') (b : B') →
        H a ∙ coherence-square-cocone pr1 pr2 d (a , b) ＝ L b) →
      (t : A' × B') →
      dependent-identification
        ( λ x → z ＝ F x)
        ( glue-join t)
        ( H (pr1 t) ∙ inv (compute-inl-cogap-join d (pr1 t)))
        ( L (pr2 t) ∙ inv (compute-inr-cogap-join d (pr2 t)))
    coherence-map H L M =
      map-inv-equiv equiv-ev-pair
        ( λ a b →
          map-compute-dependent-identification-eq-value-function
            ( λ _ → z)
            ( F)
            ( glue-join (a , b))
            ( H a ∙ inv (compute-inl-cogap-join d a))
            ( L b ∙ inv (compute-inr-cogap-join d b))
            ( coherence-square-constant-cogap-join-data d z H L a b (M a b)))

    is-equiv-coherence-map :
      (H : (a : A') → z ＝ horizontal-map-cocone pr1 pr2 d a)
      (L : (b : B') → z ＝ vertical-map-cocone pr1 pr2 d b) →
      is-equiv (coherence-map H L)
    is-equiv-coherence-map H L =
      is-equiv-comp
        ( map-inv-equiv equiv-ev-pair)
        ( λ M a b →
          map-compute-dependent-identification-eq-value-function
            ( λ _ → z)
            ( F)
            ( glue-join (a , b))
            ( H a ∙ inv (compute-inl-cogap-join d a))
            ( L b ∙ inv (compute-inr-cogap-join d b))
            ( coherence-square-constant-cogap-join-data d z H L a b (M a b)))
        ( is-equiv-map-Π-is-fiberwise-equiv
          ( λ a →
            is-equiv-map-Π-is-fiberwise-equiv
              ( λ b →
                is-equiv-comp
                  ( map-compute-dependent-identification-eq-value-function
                    ( λ _ → z)
                    ( F)
                    ( glue-join (a , b))
                    ( H a ∙ inv (compute-inl-cogap-join d a))
                    ( L b ∙ inv (compute-inr-cogap-join d b)))
                  ( coherence-square-constant-cogap-join-data d z H L a b)
                  ( is-equiv-coherence-square-constant-cogap-join-data
                    d z H L a b)
                  ( is-equiv-map-compute-dependent-identification-eq-value-function
                    ( λ _ → z)
                    ( F)
                    ( glue-join (a , b))
                    ( H a ∙ inv (compute-inl-cogap-join d a))
                    ( L b ∙ inv (compute-inr-cogap-join d b))))))
        ( is-equiv-map-inv-equiv equiv-ev-pair)

    is-equiv-g :
      (H : (a : A') → z ＝ horizontal-map-cocone pr1 pr2 d a) →
      is-equiv (g H)
    is-equiv-g H =
      is-equiv-map-Σ (E H)
        ( is-equiv-map-Π-is-fiberwise-equiv
          ( λ b →
            is-equiv-concat' z (inv (compute-inr-cogap-join d b))))
        ( is-equiv-coherence-map H)

  equiv-dependent-cocone-constant-cogap-join-data :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X) →
    constant-cogap-join-data d z ≃
    dependent-cocone pr1 pr2 (cocone-join {A = A'} {B = B'})
      ( λ x → z ＝ cogap-join X d x)
  pr1 (equiv-dependent-cocone-constant-cogap-join-data d z) =
    dependent-cocone-constant-cogap-join-data d z
  pr2 (equiv-dependent-cocone-constant-cogap-join-data d z) =
    is-equiv-dependent-cocone-constant-cogap-join-data d z

  is-equiv-map-Π-dependent-cocone-constant-cogap-join-data :
    {l1' l2' l3' l4 : Level}
    {A' : UU l1'} {B' : UU l2'} {C' : UU l3'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (i : C' → X) →
    is-equiv
      ( λ (R : (c : C') → constant-cogap-join-data d (i c)) c →
        dependent-cocone-constant-cogap-join-data d (i c) (R c))
  is-equiv-map-Π-dependent-cocone-constant-cogap-join-data d i =
    is-equiv-map-Π-is-fiberwise-equiv
      ( λ c → is-equiv-dependent-cocone-constant-cogap-join-data d (i c))

  constant-cogap-join-data-dependent-cocone :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X) →
    dependent-cocone pr1 pr2 (cocone-join {A = A'} {B = B'})
      ( λ x → z ＝ cogap-join X d x) →
    constant-cogap-join-data d z
  pr1 (constant-cogap-join-data-dependent-cocone d z E) a =
    pr1 E a ∙ compute-inl-cogap-join d a
  pr1 (pr2 (constant-cogap-join-data-dependent-cocone d z E)) b =
    pr1 (pr2 E) b ∙ compute-inr-cogap-join d b
  pr2
    ( pr2
      ( constant-cogap-join-data-dependent-cocone
        { A' = A'}
        { B' = B'}
        d z E))
    a b =
    equational-reasoning
      (α ∙ linl) ∙ H (a , b)
      ＝ α ∙ (linl ∙ H (a , b))
        by assoc α linl (H (a , b))
      ＝ α ∙ (apF ∙ rinr)
        by ap (α ∙_) (inv (compute-glue-F (a , b)))
      ＝ (α ∙ apF) ∙ rinr
        by inv (assoc α apF rinr)
      ＝ (ap (λ _ → z) p ∙ β) ∙ rinr
        by ap (_∙ rinr) (inv coh-E)
      ＝ (refl ∙ β) ∙ rinr
        by ap (λ q → (q ∙ β) ∙ rinr) (ap-const z p)
      ＝ β ∙ rinr
        by ap (_∙ rinr) left-unit
    where
    F : A' * B' → _
    F = cogap-join _ d

    H = coherence-square-cocone pr1 pr2 d

    p = glue-join (a , b)
    linl = compute-inl-cogap-join d a
    rinr = compute-inr-cogap-join d b
    apF = ap F p
    α = pr1 E a
    β = pr1 (pr2 E) b

    compute-glue-F :
      statement-coherence-htpy-cocone pr1 pr2
        ( cocone-map pr1 pr2 cocone-join F)
        ( d)
        ( compute-inl-cogap-join d)
        ( compute-inr-cogap-join d)
    compute-glue-F = compute-glue-cogap-join d

    coh-E :
      ap (λ _ → z) p ∙ β ＝ α ∙ ap F p
    coh-E =
      map-inv-compute-dependent-identification-eq-value-function
        ( λ _ → z)
        ( F)
        ( p)
        ( α)
        ( β)
        ( pr2 (pr2 E) (a , b))

  horizontal-htpy-section-constant-cogap-join-data-dependent-cocone :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X)
    (E :
      dependent-cocone pr1 pr2 (cocone-join {A = A'} {B = B'})
        ( λ x → z ＝ cogap-join X d x)) →
    pr1
      ( dependent-cocone-constant-cogap-join-data d z
        ( constant-cogap-join-data-dependent-cocone d z E)) ~
    pr1 E
  horizontal-htpy-section-constant-cogap-join-data-dependent-cocone d z E a =
    is-retraction-inv-concat' (compute-inl-cogap-join d a) (pr1 E a)

  vertical-htpy-section-constant-cogap-join-data-dependent-cocone :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X)
    (E :
      dependent-cocone pr1 pr2 (cocone-join {A = A'} {B = B'})
        ( λ x → z ＝ cogap-join X d x)) →
    pr1
      ( pr2
        ( dependent-cocone-constant-cogap-join-data d z
          ( constant-cogap-join-data-dependent-cocone d z E))) ~
    pr1 (pr2 E)
  vertical-htpy-section-constant-cogap-join-data-dependent-cocone d z E b =
    is-retraction-inv-concat' (compute-inr-cogap-join d b) (pr1 (pr2 E) b)

  horizontal-htpy-retraction-constant-cogap-join-data-dependent-cocone :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X)
    (R : constant-cogap-join-data d z) →
    pr1
      ( constant-cogap-join-data-dependent-cocone d z
        ( dependent-cocone-constant-cogap-join-data d z R)) ~
    pr1 R
  horizontal-htpy-retraction-constant-cogap-join-data-dependent-cocone
    d z (H , L , M) a =
    is-section-inv-concat' (compute-inl-cogap-join d a) (H a)

  vertical-htpy-retraction-constant-cogap-join-data-dependent-cocone :
    {l1' l2' l4 : Level} {A' : UU l1'} {B' : UU l2'}
    {X : UU l4}
    (d : cocone {S = A' × B'} {A = A'} {B = B'} pr1 pr2 X)
    (z : X)
    (R : constant-cogap-join-data d z) →
    pr1
      ( pr2
        ( constant-cogap-join-data-dependent-cocone d z
          ( dependent-cocone-constant-cogap-join-data d z R))) ~
    pr1 (pr2 R)
  vertical-htpy-retraction-constant-cogap-join-data-dependent-cocone
    d z (H , L , M) b =
    is-section-inv-concat' (compute-inr-cogap-join d b) (L b)

  cocone-A-join-BC :
    {l4 : Level} → UU l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cocone-A-join-BC X =
    cocone
      { S = A × (B * C)}
      { A = A}
      { B = B * C}
      ( pr1)
      ( pr2)
      ( X)

  cocone-AB-join-C :
    {l4 : Level} → UU l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cocone-AB-join-C X =
    cocone
      { S = (A * B) × C}
      { A = A * B}
      { B = C}
      ( pr1)
      ( pr2)
      ( X)

  cocone-AB-join-C-normal-form :
    {l4 : Level} → UU l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cocone-AB-join-C-normal-form X =
    Σ ( cocone {S = A × B} {A = A} {B = B} pr1 pr2 X)
      ( λ d →
        Σ ( C → X)
          ( λ k →
            (c : C) →
            dependent-cocone pr1 pr2 cocone-join
              ( λ x → cogap-join X d x ＝ k c)))

  cocone-AB-join-C-cocone-AB-join-C-normal-form :
    {l4 : Level} {X : UU l4} →
    cocone-AB-join-C-normal-form X → cocone-AB-join-C X
  pr1 (cocone-AB-join-C-cocone-AB-join-C-normal-form (d , k , K)) =
    cogap-join _ d
  pr1 (pr2 (cocone-AB-join-C-cocone-AB-join-C-normal-form (d , k , K))) =
    k
  pr2
    ( pr2 (cocone-AB-join-C-cocone-AB-join-C-normal-form (d , k , K)))
    =
    map-inv-equiv equiv-ev-pair
      ( λ x c → dependent-cogap-join (K c) x)

  is-equiv-cocone-AB-join-C-cocone-AB-join-C-normal-form-fiber :
    {l4 : Level} {X : UU l4}
    (d : cocone {S = A × B} {A = A} {B = B} pr1 pr2 X)
    (k : C → X) →
    is-equiv
      ( λ (K :
          (c : C) →
          dependent-cocone pr1 pr2 cocone-join
            ( λ x → cogap-join X d x ＝ k c)) →
        map-inv-equiv equiv-ev-pair
          ( λ x c → dependent-cogap-join (K c) x))
  is-equiv-cocone-AB-join-C-cocone-AB-join-C-normal-form-fiber
    d k =
    is-equiv-comp
      ( map-inv-equiv equiv-ev-pair)
      ( λ K x c → dependent-cogap-join (K c) x)
      ( is-equiv-comp
        ( swap-Π)
        ( map-Π (λ c → dependent-cogap-join))
        ( is-equiv-map-Π-is-fiberwise-equiv
          ( λ c → is-equiv-dependent-cogap-join))
        ( is-equiv-swap-Π))
      ( is-equiv-map-inv-equiv equiv-ev-pair)

  is-equiv-cocone-AB-join-C-cocone-AB-join-C-normal-form :
    {l4 : Level} {X : UU l4} →
    is-equiv
      ( cocone-AB-join-C-cocone-AB-join-C-normal-form
        { X = X})
  is-equiv-cocone-AB-join-C-cocone-AB-join-C-normal-form =
    is-equiv-map-Σ
      ( λ F →
        Σ ( C → _)
          ( λ k → (t : (A * B) × C) → F (pr1 t) ＝ k (pr2 t)))
      ( is-equiv-cogap-join _)
      ( λ d →
        is-equiv-map-Σ
          ( λ k →
            (t : (A * B) × C) → cogap-join _ d (pr1 t) ＝ k (pr2 t))
          ( is-equiv-id)
          ( is-equiv-cocone-AB-join-C-cocone-AB-join-C-normal-form-fiber d))

  cocone-A-join-BC-normal-form :
    {l4 : Level} → UU l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cocone-A-join-BC-normal-form X =
    Σ ( A → X)
      ( λ i →
        Σ ( cocone {S = B × C} {A = B} {B = C} pr1 pr2 X)
          ( λ d →
            (a : A) →
            dependent-cocone pr1 pr2 cocone-join
              ( λ y → i a ＝ cogap-join X d y)))

  cocone-A-join-BC-cocone-A-join-BC-normal-form :
    {l4 : Level} {X : UU l4} →
    cocone-A-join-BC-normal-form X → cocone-A-join-BC X
  pr1 (cocone-A-join-BC-cocone-A-join-BC-normal-form (i , d , H)) =
    i
  pr1 (pr2 (cocone-A-join-BC-cocone-A-join-BC-normal-form (i , d , H))) =
    cogap-join _ d
  pr2
    ( pr2 (cocone-A-join-BC-cocone-A-join-BC-normal-form (i , d , H))) =
    map-inv-equiv equiv-ev-pair
      ( λ a y → dependent-cogap-join (H a) y)

  is-equiv-cocone-A-join-BC-cocone-A-join-BC-normal-form-fiber :
    {l4 : Level} {X : UU l4}
    (i : A → X)
    (d : cocone {S = B × C} {A = B} {B = C} pr1 pr2 X) →
    is-equiv
      ( λ (H :
          (a : A) →
          dependent-cocone pr1 pr2 cocone-join
            ( λ y → i a ＝ cogap-join X d y)) →
        map-inv-equiv equiv-ev-pair
          ( λ a y → dependent-cogap-join (H a) y))
  is-equiv-cocone-A-join-BC-cocone-A-join-BC-normal-form-fiber
    i d =
    is-equiv-comp
      ( map-inv-equiv equiv-ev-pair)
      ( λ H a y → dependent-cogap-join (H a) y)
      ( is-equiv-map-Π-is-fiberwise-equiv
        ( λ a → is-equiv-dependent-cogap-join-BC))
      ( is-equiv-map-inv-equiv equiv-ev-pair)

  is-equiv-cocone-A-join-BC-cocone-A-join-BC-normal-form :
    {l4 : Level} {X : UU l4} →
    is-equiv
      ( cocone-A-join-BC-cocone-A-join-BC-normal-form
        { X = X})
  is-equiv-cocone-A-join-BC-cocone-A-join-BC-normal-form =
    is-equiv-map-Σ
      ( λ i →
        Σ ( B * C → _)
          ( λ J → (t : A × (B * C)) → i (pr1 t) ＝ J (pr2 t)))
      ( is-equiv-id)
      ( λ i →
        is-equiv-map-Σ
          ( λ J → (t : A × (B * C)) → i (pr1 t) ＝ J (pr2 t))
          ( is-equiv-cogap-join-BC _)
          ( is-equiv-cocone-A-join-BC-cocone-A-join-BC-normal-form-fiber i))

  cocone-AB-cocone-A-join-BC :
    {l4 : Level} {X : UU l4} →
    cocone-A-join-BC X →
    cocone {S = A × B} {A = A} {B = B} pr1 pr2 X
  pr1 (cocone-AB-cocone-A-join-BC d) =
    horizontal-map-cocone pr1 pr2 d
  pr1 (pr2 (cocone-AB-cocone-A-join-BC d)) =
    vertical-map-cocone pr1 pr2 d ∘ inl-join
  pr2 (pr2 (cocone-AB-cocone-A-join-BC d)) (a , b) =
    coherence-square-cocone pr1 pr2 d (a , inl-join b)

  map-AB-cocone-A-join-BC :
    {l4 : Level} {X : UU l4} →
    cocone-A-join-BC X → A * B → X
  map-AB-cocone-A-join-BC d =
    cogap-join _ (cocone-AB-cocone-A-join-BC d)

  compute-inl-map-AB-cocone-A-join-BC :
    {l4 : Level} {X : UU l4} (d : cocone-A-join-BC X) →
    map-AB-cocone-A-join-BC d ∘ inl-join ~
    horizontal-map-cocone pr1 pr2 d
  compute-inl-map-AB-cocone-A-join-BC d =
    compute-inl-cogap-join (cocone-AB-cocone-A-join-BC d)

  compute-inr-map-AB-cocone-A-join-BC :
    {l4 : Level} {X : UU l4} (d : cocone-A-join-BC X) →
    map-AB-cocone-A-join-BC d ∘ inr-join ~
    vertical-map-cocone pr1 pr2 d ∘ inl-join
  compute-inr-map-AB-cocone-A-join-BC d =
    compute-inr-cogap-join (cocone-AB-cocone-A-join-BC d)

  compute-glue-map-AB-cocone-A-join-BC :
    {l4 : Level} {X : UU l4} (d : cocone-A-join-BC X) →
    statement-coherence-htpy-cocone pr1 pr2
      ( cocone-map pr1 pr2 cocone-join (map-AB-cocone-A-join-BC d))
      ( cocone-AB-cocone-A-join-BC d)
      ( compute-inl-map-AB-cocone-A-join-BC d)
      ( compute-inr-map-AB-cocone-A-join-BC d)
  compute-glue-map-AB-cocone-A-join-BC d =
    compute-glue-cogap-join (cocone-AB-cocone-A-join-BC d)

  naturality-coherence-cocone-A-join-BC :
    {l4 : Level} {X : UU l4} (d : cocone-A-join-BC X)
    (a : A) (b : B) (c : C) →
    coherence-square-cocone pr1 pr2 d (a , inl-join b) ∙
    ap (vertical-map-cocone pr1 pr2 d) (glue-join (b , c)) ＝
    coherence-square-cocone pr1 pr2 d (a , inr-join c)
  naturality-coherence-cocone-A-join-BC d a b c =
    equational-reasoning
      K (a , inl-join b) ∙ ap j p
      ＝ ap (λ _ → i a) p ∙ K (a , inr-join c)
        by inv (naturality-homotopy (λ y → K (a , y)) p)
      ＝ refl ∙ K (a , inr-join c)
        by ap (_∙ K (a , inr-join c)) (ap-const (i a) p)
      ＝ K (a , inr-join c)
        by left-unit
    where
    p = glue-join (b , c)

    i : A → _
    i = horizontal-map-cocone pr1 pr2 d

    j : B * C → _
    j = vertical-map-cocone pr1 pr2 d

    K : coherence-square-maps pr2 pr1 j i
    K = coherence-square-cocone pr1 pr2 d

  path-inl-dependent-cocone-H-cocone-A-join-BC :
    {l4 : Level} {X : UU l4} (d : cocone-A-join-BC X)
    (c : C) (a : A) →
    map-AB-cocone-A-join-BC d (inl-join a) ＝
    vertical-map-cocone pr1 pr2 d (inr-join c)
  path-inl-dependent-cocone-H-cocone-A-join-BC d c a =
    compute-inl-map-AB-cocone-A-join-BC d a ∙
    coherence-square-cocone pr1 pr2 d (a , inr-join c)

  path-inr-dependent-cocone-H-cocone-A-join-BC :
    {l4 : Level} {X : UU l4} (d : cocone-A-join-BC X)
    (c : C) (b : B) →
    map-AB-cocone-A-join-BC d (inr-join b) ＝
    vertical-map-cocone pr1 pr2 d (inr-join c)
  path-inr-dependent-cocone-H-cocone-A-join-BC d c b =
    compute-inr-map-AB-cocone-A-join-BC d b ∙
    ap (vertical-map-cocone pr1 pr2 d) (glue-join (b , c))

  coherence-dependent-cocone-H-cocone-A-join-BC :
    {l4 : Level} {X : UU l4} (d : cocone-A-join-BC X)
    (c : C) (a : A) (b : B) →
    dependent-identification
      ( λ x →
        map-AB-cocone-A-join-BC d x ＝
        vertical-map-cocone pr1 pr2 d (inr-join c))
      ( glue-join (a , b))
      ( path-inl-dependent-cocone-H-cocone-A-join-BC d c a)
      ( path-inr-dependent-cocone-H-cocone-A-join-BC d c b)
  coherence-dependent-cocone-H-cocone-A-join-BC d c a b =
    map-compute-dependent-identification-eq-value-function
      ( map-AB-cocone-A-join-BC d)
      ( λ _ → j (inr-join c))
      ( p)
      ( path-inl-dependent-cocone-H-cocone-A-join-BC d c a)
      ( path-inr-dependent-cocone-H-cocone-A-join-BC d c b)
      ( coherence-square-cogap-join-constant-data
        ( cocone-AB-cocone-A-join-BC d)
        ( j (inr-join c))
        ( λ b → ap j (glue-join (b , c)))
        ( λ a → K (a , inr-join c))
        ( a)
        ( b)
        ( naturality-coherence-cocone-A-join-BC d a b c))
    where
    p = glue-join (a , b)

    j : B * C → _
    j = vertical-map-cocone pr1 pr2 d

    K : coherence-square-maps pr2 pr1 j (horizontal-map-cocone pr1 pr2 d)
    K = coherence-square-cocone pr1 pr2 d

  dependent-cocone-H-cocone-A-join-BC :
    {l4 : Level} {X : UU l4} (d : cocone-A-join-BC X)
    (c : C) →
    dependent-cocone pr1 pr2 cocone-join
      ( λ x →
        map-AB-cocone-A-join-BC d x ＝
        vertical-map-cocone pr1 pr2 d (inr-join c))
  pr1 (dependent-cocone-H-cocone-A-join-BC d c) a =
    path-inl-dependent-cocone-H-cocone-A-join-BC d c a
  pr1 (pr2 (dependent-cocone-H-cocone-A-join-BC d c)) b =
    path-inr-dependent-cocone-H-cocone-A-join-BC d c b
  pr2 (pr2 (dependent-cocone-H-cocone-A-join-BC d c)) (a , b) =
    coherence-dependent-cocone-H-cocone-A-join-BC d c a b

  cocone-AB-join-C-cocone-A-join-BC :
    {l4 : Level} {X : UU l4} →
    cocone-A-join-BC X → cocone-AB-join-C X
  pr1 (cocone-AB-join-C-cocone-A-join-BC d) =
    map-AB-cocone-A-join-BC d
  pr1 (pr2 (cocone-AB-join-C-cocone-A-join-BC d)) =
    vertical-map-cocone pr1 pr2 d ∘ inr-join
  pr2 (pr2 (cocone-AB-join-C-cocone-A-join-BC d)) (x , c) =
    dependent-cogap-join (dependent-cocone-H-cocone-A-join-BC d c) x

  cocone-BC-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} →
    cocone-AB-join-C X →
    cocone {S = B × C} {A = B} {B = C} pr1 pr2 X
  pr1 (cocone-BC-cocone-AB-join-C e) = F ∘ inr-join
    where
    F : A * B → _
    F = horizontal-map-cocone pr1 pr2 e
  pr1 (pr2 (cocone-BC-cocone-AB-join-C e)) =
    vertical-map-cocone pr1 pr2 e
  pr2 (pr2 (cocone-BC-cocone-AB-join-C e)) (b , c) =
    coherence-square-cocone pr1 pr2 e (inr-join b , c)

  map-BC-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} →
    cocone-AB-join-C X → B * C → X
  map-BC-cocone-AB-join-C e =
    cogap-join _ (cocone-BC-cocone-AB-join-C e)

  compute-inl-map-BC-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} (e : cocone-AB-join-C X) →
    map-BC-cocone-AB-join-C e ∘ inl-join ~
    horizontal-map-cocone pr1 pr2 e ∘ inr-join
  compute-inl-map-BC-cocone-AB-join-C e =
    compute-inl-cogap-join (cocone-BC-cocone-AB-join-C e)

  compute-inr-map-BC-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} (e : cocone-AB-join-C X) →
    map-BC-cocone-AB-join-C e ∘ inr-join ~
    vertical-map-cocone pr1 pr2 e
  compute-inr-map-BC-cocone-AB-join-C e =
    compute-inr-cogap-join (cocone-BC-cocone-AB-join-C e)

  compute-glue-map-BC-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} (e : cocone-AB-join-C X) →
    statement-coherence-htpy-cocone pr1 pr2
      ( cocone-map pr1 pr2 cocone-join (map-BC-cocone-AB-join-C e))
      ( cocone-BC-cocone-AB-join-C e)
      ( compute-inl-map-BC-cocone-AB-join-C e)
      ( compute-inr-map-BC-cocone-AB-join-C e)
  compute-glue-map-BC-cocone-AB-join-C e =
    compute-glue-cogap-join (cocone-BC-cocone-AB-join-C e)

  naturality-coherence-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} (e : cocone-AB-join-C X)
    (a : A) (b : B) (c : C) →
    ap (horizontal-map-cocone pr1 pr2 e) (glue-join (a , b)) ∙
    coherence-square-cocone pr1 pr2 e (inr-join b , c) ＝
    coherence-square-cocone pr1 pr2 e (inl-join a , c)
  naturality-coherence-cocone-AB-join-C e a b c =
    equational-reasoning
      ap F p ∙ H (inr-join b , c)
      ＝ H (inl-join a , c) ∙ ap (λ _ → G c) p
        by naturality-homotopy (λ x → H (x , c)) p
      ＝ H (inl-join a , c) ∙ refl
        by ap (H (inl-join a , c) ∙_) (ap-const (G c) p)
      ＝ H (inl-join a , c)
        by right-unit
    where
    p = glue-join (a , b)

    F : A * B → _
    F = horizontal-map-cocone pr1 pr2 e

    G : C → _
    G = vertical-map-cocone pr1 pr2 e

    H = coherence-square-cocone pr1 pr2 e

  right-transpose-compute-glue-map-BC-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} (e : cocone-AB-join-C X)
    (b : B) (c : C) →
    inv (compute-inl-map-BC-cocone-AB-join-C e b) ∙
    ap (map-BC-cocone-AB-join-C e) (glue-join (b , c)) ＝
    coherence-square-cocone pr1 pr2 e (inr-join b , c) ∙
    inv (compute-inr-map-BC-cocone-AB-join-C e c)
  right-transpose-compute-glue-map-BC-cocone-AB-join-C e b c =
    equational-reasoning
      inv linl ∙ apJ
      ＝ (inv linl ∙ apJ) ∙ refl
        by inv right-unit
      ＝ (inv linl ∙ apJ) ∙ (rinr ∙ inv rinr)
        by ap ((inv linl ∙ apJ) ∙_) (inv (right-inv rinr))
      ＝ ((inv linl ∙ apJ) ∙ rinr) ∙ inv rinr
        by inv (assoc (inv linl ∙ apJ) rinr (inv rinr))
      ＝ (inv linl ∙ (apJ ∙ rinr)) ∙ inv rinr
        by ap (_∙ inv rinr) (assoc (inv linl) apJ rinr)
      ＝ (inv linl ∙ (linl ∙ hbc)) ∙ inv rinr
        by ap (λ q → (inv linl ∙ q) ∙ inv rinr)
          ( compute-glue-map-BC-cocone-AB-join-C e (b , c))
      ＝ ((inv linl ∙ linl) ∙ hbc) ∙ inv rinr
        by ap (_∙ inv rinr) (inv (assoc (inv linl) linl hbc))
      ＝ (refl ∙ hbc) ∙ inv rinr
        by ap (λ q → (q ∙ hbc) ∙ inv rinr) (left-inv linl)
      ＝ hbc ∙ inv rinr
        by ap (_∙ inv rinr) left-unit
    where
    linl = compute-inl-map-BC-cocone-AB-join-C e b
    rinr = compute-inr-map-BC-cocone-AB-join-C e c
    apJ = ap (map-BC-cocone-AB-join-C e) (glue-join (b , c))
    hbc = coherence-square-cocone pr1 pr2 e (inr-join b , c)

  path-inl-dependent-cocone-K-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} (e : cocone-AB-join-C X) →
    (a : A) (b : B) →
    horizontal-map-cocone pr1 pr2 e (inl-join a) ＝
    map-BC-cocone-AB-join-C e (inl-join b)
  path-inl-dependent-cocone-K-cocone-AB-join-C e a b =
    ap F (glue-join (a , b)) ∙ inv (compute-inl-map-BC-cocone-AB-join-C e b)
    where
    F : A * B → _
    F = horizontal-map-cocone pr1 pr2 e

  path-inr-dependent-cocone-K-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} (e : cocone-AB-join-C X) →
    (a : A) (c : C) →
    horizontal-map-cocone pr1 pr2 e (inl-join a) ＝
    map-BC-cocone-AB-join-C e (inr-join c)
  path-inr-dependent-cocone-K-cocone-AB-join-C e a c =
    coherence-square-cocone pr1 pr2 e (inl-join a , c) ∙
    inv (compute-inr-map-BC-cocone-AB-join-C e c)

  coherence-dependent-cocone-K-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} (e : cocone-AB-join-C X) →
    (a : A) (b : B) (c : C) →
    dependent-identification
      ( λ y →
        horizontal-map-cocone pr1 pr2 e (inl-join a) ＝
        map-BC-cocone-AB-join-C e y)
      ( glue-join (b , c))
      ( path-inl-dependent-cocone-K-cocone-AB-join-C e a b)
      ( path-inr-dependent-cocone-K-cocone-AB-join-C e a c)
  coherence-dependent-cocone-K-cocone-AB-join-C e a b c =
    map-compute-dependent-identification-eq-value-function
      ( λ _ → F (inl-join a))
      ( map-BC-cocone-AB-join-C e)
      ( p)
      ( path-inl-dependent-cocone-K-cocone-AB-join-C e a b)
      ( path-inr-dependent-cocone-K-cocone-AB-join-C e a c)
      ( coherence-square-constant-cogap-join-data
        ( cocone-BC-cocone-AB-join-C e)
        ( F (inl-join a))
        ( λ b → ap F (glue-join (a , b)))
        ( λ c → H (inl-join a , c))
        ( b)
        ( c)
        ( naturality-coherence-cocone-AB-join-C e a b c))
    where
    p = glue-join (b , c)

    F : A * B → _
    F = horizontal-map-cocone pr1 pr2 e

    H = coherence-square-cocone pr1 pr2 e

  dependent-cocone-K-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} (e : cocone-AB-join-C X)
    (a : A) →
    dependent-cocone pr1 pr2 cocone-join
      ( λ y →
        horizontal-map-cocone pr1 pr2 e (inl-join a) ＝
        map-BC-cocone-AB-join-C e y)
  pr1 (dependent-cocone-K-cocone-AB-join-C e a) b =
    path-inl-dependent-cocone-K-cocone-AB-join-C e a b
  pr1 (pr2 (dependent-cocone-K-cocone-AB-join-C e a)) c =
    path-inr-dependent-cocone-K-cocone-AB-join-C e a c
  pr2 (pr2 (dependent-cocone-K-cocone-AB-join-C e a)) (b , c) =
    coherence-dependent-cocone-K-cocone-AB-join-C e a b c

  cocone-A-join-BC-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} →
    cocone-AB-join-C X → cocone-A-join-BC X
  pr1 (cocone-A-join-BC-cocone-AB-join-C e) =
    horizontal-map-cocone pr1 pr2 e ∘ inl-join
  pr1 (pr2 (cocone-A-join-BC-cocone-AB-join-C e)) =
    map-BC-cocone-AB-join-C e
  pr2 (pr2 (cocone-A-join-BC-cocone-AB-join-C e)) (a , y) =
    dependent-cogap-join (dependent-cocone-K-cocone-AB-join-C e a) y

  associative-cocone-data :
    {l4 : Level} → UU l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  associative-cocone-data X =
    Σ ( A → X)
      ( λ i →
        Σ ( B → X)
          ( λ j →
            Σ ( C → X)
              ( λ k →
                Σ ( (a : A) (b : B) → i a ＝ j b)
                  ( λ H →
                    Σ ( (b : B) (c : C) → j b ＝ k c)
                      ( λ K →
                        Σ ( (a : A) (c : C) → i a ＝ k c)
                          ( λ L →
                            (a : A) (b : B) (c : C) →
                            (H a b ∙ K b c) ＝ L a c))))))

  associative-cocone-data-tri-join-rec-data :
    {l4 : Level} {X : UU l4} →
    tri-join-rec-data A B C X → associative-cocone-data X
  associative-cocone-data-tri-join-rec-data d =
    ( point-1-tri-join-rec-data d ,
      point-2-tri-join-rec-data d ,
      point-3-tri-join-rec-data d ,
      path-12-tri-join-rec-data d ,
      path-23-tri-join-rec-data d ,
      path-13-tri-join-rec-data d ,
      coherence-triangle-tri-join-rec-data d)

  tri-join-rec-data-associative-cocone-data :
    {l4 : Level} {X : UU l4} →
    associative-cocone-data X → tri-join-rec-data A B C X
  tri-join-rec-data-associative-cocone-data (i , j , k , H , K , L , M) =
    make-tri-join-rec-data i j k H L K M

  is-section-associative-cocone-data-tri-join-rec-data :
    {l4 : Level} {X : UU l4} →
    associative-cocone-data-tri-join-rec-data ∘
    tri-join-rec-data-associative-cocone-data {X = X} ~ id
  is-section-associative-cocone-data-tri-join-rec-data
    ( i , j , k , H , K , L , M) =
    refl

  is-retraction-associative-cocone-data-tri-join-rec-data :
    {l4 : Level} {X : UU l4} →
    tri-join-rec-data-associative-cocone-data ∘
    associative-cocone-data-tri-join-rec-data {X = X} ~ id
  is-retraction-associative-cocone-data-tri-join-rec-data d =
    refl

  is-equiv-associative-cocone-data-tri-join-rec-data :
    {l4 : Level} {X : UU l4} →
    is-equiv (associative-cocone-data-tri-join-rec-data {X = X})
  is-equiv-associative-cocone-data-tri-join-rec-data =
    is-equiv-is-invertible
      ( tri-join-rec-data-associative-cocone-data)
      ( is-section-associative-cocone-data-tri-join-rec-data)
      ( is-retraction-associative-cocone-data-tri-join-rec-data)

  equiv-associative-cocone-data-tri-join-rec-data :
    {l4 : Level} {X : UU l4} →
    tri-join-rec-data A B C X ≃ associative-cocone-data X
  pr1 equiv-associative-cocone-data-tri-join-rec-data =
    associative-cocone-data-tri-join-rec-data
  pr2 equiv-associative-cocone-data-tri-join-rec-data =
    is-equiv-associative-cocone-data-tri-join-rec-data

  cocone-AB-join-C-raw-normal-form :
    {l4 : Level} → UU l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cocone-AB-join-C-raw-normal-form X =
    Σ ( cocone {S = A × B} {A = A} {B = B} pr1 pr2 X)
      ( λ d →
        Σ ( C → X)
          ( λ k →
            (c : C) → cogap-join-constant-data d (k c)))

  cocone-AB-join-C-raw-normal-form-associative-cocone-data :
    {l4 : Level} {X : UU l4} →
    associative-cocone-data X → cocone-AB-join-C-raw-normal-form X
  cocone-AB-join-C-raw-normal-form-associative-cocone-data
    ( i , j , k , H , K , L , M) =
    cocone-F ,
    k ,
    λ c → (λ b → K b c) , (λ a → L a c) , (λ a b → M a b c)
    where
    cocone-F : cocone pr1 pr2 _
    pr1 cocone-F = i
    pr1 (pr2 cocone-F) = j
    pr2 (pr2 cocone-F) (a , b) = H a b

  associative-cocone-data-cocone-AB-join-C-raw-normal-form :
    {l4 : Level} {X : UU l4} →
    cocone-AB-join-C-raw-normal-form X → associative-cocone-data X
  associative-cocone-data-cocone-AB-join-C-raw-normal-form (d , k , R) =
    horizontal-map-cocone pr1 pr2 d ,
    vertical-map-cocone pr1 pr2 d ,
    k ,
    (λ a b → coherence-square-cocone pr1 pr2 d (a , b)) ,
    (λ b c → pr1 (R c) b) ,
    (λ a c → pr1 (pr2 (R c)) a) ,
    (λ a b c → pr2 (pr2 (R c)) a b)

  is-equiv-cocone-AB-join-C-raw-normal-form-associative-cocone-data :
    {l4 : Level} {X : UU l4} →
    is-equiv
      ( cocone-AB-join-C-raw-normal-form-associative-cocone-data
        { X = X})
  is-equiv-cocone-AB-join-C-raw-normal-form-associative-cocone-data =
    is-equiv-is-invertible
      ( associative-cocone-data-cocone-AB-join-C-raw-normal-form)
      ( λ (d , k , R) → refl)
      ( λ (i , j , k , H , K , L , M) → refl)

  cocone-AB-join-C-normal-form-cocone-AB-join-C-raw-normal-form :
    {l4 : Level} {X : UU l4} →
    cocone-AB-join-C-raw-normal-form X → cocone-AB-join-C-normal-form X
  cocone-AB-join-C-normal-form-cocone-AB-join-C-raw-normal-form
    ( d , k , R) =
    d ,
    k ,
    λ c → dependent-cocone-cogap-join-constant-data d (k c) (R c)

  is-equiv-cocone-AB-join-C-normal-form-cocone-AB-join-C-raw-normal-form :
    {l4 : Level} {X : UU l4} →
    is-equiv
      ( cocone-AB-join-C-normal-form-cocone-AB-join-C-raw-normal-form
        { X = X})
  is-equiv-cocone-AB-join-C-normal-form-cocone-AB-join-C-raw-normal-form =
    is-equiv-map-Σ
      ( λ d →
        Σ ( C → _)
          ( λ k →
            (c : C) →
            dependent-cocone pr1 pr2 cocone-join
              ( λ x → cogap-join _ d x ＝ k c)))
      ( is-equiv-id)
      ( λ d →
        is-equiv-map-Σ
          ( λ k →
            (c : C) →
            dependent-cocone pr1 pr2 cocone-join
              ( λ x → cogap-join _ d x ＝ k c))
          ( is-equiv-id)
          ( is-equiv-map-Π-dependent-cocone-cogap-join-constant-data d))

  is-equiv-cocone-AB-join-C-normal-form-associative-cocone-data-raw :
    {l4 : Level} {X : UU l4} →
    is-equiv
      ( cocone-AB-join-C-normal-form-cocone-AB-join-C-raw-normal-form ∘
        cocone-AB-join-C-raw-normal-form-associative-cocone-data
        { X = X})
  is-equiv-cocone-AB-join-C-normal-form-associative-cocone-data-raw =
    is-equiv-comp
      ( cocone-AB-join-C-normal-form-cocone-AB-join-C-raw-normal-form)
      ( cocone-AB-join-C-raw-normal-form-associative-cocone-data)
      ( is-equiv-cocone-AB-join-C-raw-normal-form-associative-cocone-data)
      ( is-equiv-cocone-AB-join-C-normal-form-cocone-AB-join-C-raw-normal-form)

  cocone-A-join-BC-raw-normal-form :
    {l4 : Level} → UU l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cocone-A-join-BC-raw-normal-form X =
    Σ ( A → X)
      ( λ i →
        Σ ( cocone {S = B × C} {A = B} {B = C} pr1 pr2 X)
          ( λ d →
            (a : A) → constant-cogap-join-data d (i a)))

  cocone-A-join-BC-raw-normal-form-cocone-A-join-BC :
    {l4 : Level} {X : UU l4} →
    cocone-A-join-BC X → cocone-A-join-BC-raw-normal-form X
  pr1 (cocone-A-join-BC-raw-normal-form-cocone-A-join-BC d) =
    horizontal-map-cocone pr1 pr2 d
  pr1 (pr2 (cocone-A-join-BC-raw-normal-form-cocone-A-join-BC d)) =
    cocone-map pr1 pr2 cocone-join (vertical-map-cocone pr1 pr2 d)
  pr2 (pr2 (cocone-A-join-BC-raw-normal-form-cocone-A-join-BC d)) a =
    constant-cogap-join-data-cocone-map-dependent-function
      ( vertical-map-cocone pr1 pr2 d)
      ( horizontal-map-cocone pr1 pr2 d a)
      ( λ y → coherence-square-cocone pr1 pr2 d (a , y))

  is-equiv-cocone-A-join-BC-raw-normal-form-cocone-A-join-BC-fiber :
    {l4 : Level} {X : UU l4}
    (i : A → X) (j : B * C → X) →
    is-equiv
      ( λ (H : (t : A × (B * C)) → i (pr1 t) ＝ j (pr2 t)) a →
        constant-cogap-join-data-cocone-map-dependent-function
          ( j)
          ( i a)
          ( λ y → H (a , y)))
  is-equiv-cocone-A-join-BC-raw-normal-form-cocone-A-join-BC-fiber
    i j =
    is-equiv-comp
      ( λ H a →
        constant-cogap-join-data-cocone-map-dependent-function
          ( j)
          ( i a)
          ( H a))
      ( map-equiv equiv-ev-pair)
      ( is-equiv-map-equiv equiv-ev-pair)
      ( is-equiv-map-Π-is-fiberwise-equiv
        ( λ a →
          is-equiv-constant-cogap-join-data-cocone-map-dependent-function
            ( j)
            ( i a)))

  is-equiv-cocone-A-join-BC-raw-normal-form-cocone-A-join-BC :
    {l4 : Level} {X : UU l4} →
    is-equiv
      ( cocone-A-join-BC-raw-normal-form-cocone-A-join-BC
        { X = X})
  is-equiv-cocone-A-join-BC-raw-normal-form-cocone-A-join-BC =
    is-equiv-map-Σ
      ( λ i →
        Σ ( cocone {S = B × C} {A = B} {B = C} pr1 pr2 _)
          ( λ d →
            (a : A) → constant-cogap-join-data d (i a)))
      ( is-equiv-id)
      ( λ i →
        is-equiv-map-Σ
          ( λ d →
            (a : A) → constant-cogap-join-data d (i a))
          ( is-equiv-cocone-map-join-BC _)
          ( λ j →
            is-equiv-cocone-A-join-BC-raw-normal-form-cocone-A-join-BC-fiber
              i j))

  cocone-A-join-BC-raw-normal-form-associative-cocone-data :
    {l4 : Level} {X : UU l4} →
    associative-cocone-data X → cocone-A-join-BC-raw-normal-form X
  cocone-A-join-BC-raw-normal-form-associative-cocone-data
    ( i , j , k , H , K , L , M) =
    i ,
    cocone-J ,
    λ a → (λ b → H a b) , (λ c → L a c) , (λ b c → M a b c)
    where
    cocone-J : cocone pr1 pr2 _
    pr1 cocone-J = j
    pr1 (pr2 cocone-J) = k
    pr2 (pr2 cocone-J) (b , c) = K b c

  associative-cocone-data-cocone-A-join-BC-raw-normal-form :
    {l4 : Level} {X : UU l4} →
    cocone-A-join-BC-raw-normal-form X → associative-cocone-data X
  associative-cocone-data-cocone-A-join-BC-raw-normal-form (i , d , R) =
    i ,
    horizontal-map-cocone pr1 pr2 d ,
    vertical-map-cocone pr1 pr2 d ,
    (λ a b → pr1 (R a) b) ,
    (λ b c → coherence-square-cocone pr1 pr2 d (b , c)) ,
    (λ a c → pr1 (pr2 (R a)) c) ,
    (λ a b c → pr2 (pr2 (R a)) b c)

  is-equiv-cocone-A-join-BC-raw-normal-form-associative-cocone-data :
    {l4 : Level} {X : UU l4} →
    is-equiv
      ( cocone-A-join-BC-raw-normal-form-associative-cocone-data
        { X = X})
  is-equiv-cocone-A-join-BC-raw-normal-form-associative-cocone-data =
    is-equiv-is-invertible
      ( associative-cocone-data-cocone-A-join-BC-raw-normal-form)
      ( λ (i , d , R) → refl)
      ( λ (i , j , k , H , K , L , M) → refl)

  is-equiv-associative-cocone-data-cocone-A-join-BC-raw-normal-form :
    {l4 : Level} {X : UU l4} →
    is-equiv
      ( associative-cocone-data-cocone-A-join-BC-raw-normal-form
        { X = X})
  is-equiv-associative-cocone-data-cocone-A-join-BC-raw-normal-form =
    is-equiv-is-invertible
      ( cocone-A-join-BC-raw-normal-form-associative-cocone-data)
      ( λ (i , j , k , H , K , L , M) → refl)
      ( λ (i , d , R) → refl)

  cocone-A-join-BC-normal-form-cocone-A-join-BC-raw-normal-form :
    {l4 : Level} {X : UU l4} →
    cocone-A-join-BC-raw-normal-form X → cocone-A-join-BC-normal-form X
  cocone-A-join-BC-normal-form-cocone-A-join-BC-raw-normal-form
    ( i , d , R) =
    i ,
    d ,
    λ a → dependent-cocone-constant-cogap-join-data d (i a) (R a)

  is-equiv-cocone-A-join-BC-normal-form-cocone-A-join-BC-raw-normal-form :
    {l4 : Level} {X : UU l4} →
    is-equiv
      ( cocone-A-join-BC-normal-form-cocone-A-join-BC-raw-normal-form
        { X = X})
  is-equiv-cocone-A-join-BC-normal-form-cocone-A-join-BC-raw-normal-form =
    is-equiv-map-Σ
      ( λ i →
        Σ ( cocone {S = B × C} {A = B} {B = C} pr1 pr2 _)
          ( λ d →
            (a : A) →
            dependent-cocone pr1 pr2 cocone-join
              ( λ y → i a ＝ cogap-join _ d y)))
      ( is-equiv-id)
      ( λ i →
        is-equiv-map-Σ
          ( λ d →
            (a : A) →
            dependent-cocone pr1 pr2 cocone-join
              ( λ y → i a ＝ cogap-join _ d y))
          ( is-equiv-id)
          ( λ d →
            is-equiv-map-Π-dependent-cocone-constant-cogap-join-data d i))

  is-equiv-cocone-A-join-BC-normal-form-associative-cocone-data-raw :
    {l4 : Level} {X : UU l4} →
    is-equiv
      ( cocone-A-join-BC-normal-form-cocone-A-join-BC-raw-normal-form ∘
        cocone-A-join-BC-raw-normal-form-associative-cocone-data
        { X = X})
  is-equiv-cocone-A-join-BC-normal-form-associative-cocone-data-raw =
    is-equiv-comp
      ( cocone-A-join-BC-normal-form-cocone-A-join-BC-raw-normal-form)
      ( cocone-A-join-BC-raw-normal-form-associative-cocone-data)
      ( is-equiv-cocone-A-join-BC-raw-normal-form-associative-cocone-data)
      ( is-equiv-cocone-A-join-BC-normal-form-cocone-A-join-BC-raw-normal-form)

  cocone-AB-join-C-associative-cocone-data-raw :
    {l4 : Level} {X : UU l4} →
    associative-cocone-data X → cocone-AB-join-C X
  cocone-AB-join-C-associative-cocone-data-raw =
    cocone-AB-join-C-cocone-AB-join-C-normal-form ∘
    cocone-AB-join-C-normal-form-cocone-AB-join-C-raw-normal-form ∘
    cocone-AB-join-C-raw-normal-form-associative-cocone-data

  is-equiv-cocone-AB-join-C-associative-cocone-data-raw :
    {l4 : Level} {X : UU l4} →
    is-equiv (cocone-AB-join-C-associative-cocone-data-raw {X = X})
  is-equiv-cocone-AB-join-C-associative-cocone-data-raw =
    is-equiv-comp
      ( cocone-AB-join-C-cocone-AB-join-C-normal-form)
      ( cocone-AB-join-C-normal-form-cocone-AB-join-C-raw-normal-form ∘
        cocone-AB-join-C-raw-normal-form-associative-cocone-data)
      ( is-equiv-cocone-AB-join-C-normal-form-associative-cocone-data-raw)
      ( is-equiv-cocone-AB-join-C-cocone-AB-join-C-normal-form)

  cocone-A-join-BC-associative-cocone-data-raw :
    {l4 : Level} {X : UU l4} →
    associative-cocone-data X → cocone-A-join-BC X
  cocone-A-join-BC-associative-cocone-data-raw =
    cocone-A-join-BC-cocone-A-join-BC-normal-form ∘
    cocone-A-join-BC-normal-form-cocone-A-join-BC-raw-normal-form ∘
    cocone-A-join-BC-raw-normal-form-associative-cocone-data

  is-equiv-cocone-A-join-BC-associative-cocone-data-raw :
    {l4 : Level} {X : UU l4} →
    is-equiv (cocone-A-join-BC-associative-cocone-data-raw {X = X})
  is-equiv-cocone-A-join-BC-associative-cocone-data-raw =
    is-equiv-comp
      ( cocone-A-join-BC-cocone-A-join-BC-normal-form)
      ( cocone-A-join-BC-normal-form-cocone-A-join-BC-raw-normal-form ∘
        cocone-A-join-BC-raw-normal-form-associative-cocone-data)
      ( is-equiv-cocone-A-join-BC-normal-form-associative-cocone-data-raw)
      ( is-equiv-cocone-A-join-BC-cocone-A-join-BC-normal-form)

  associative-cocone-data-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} →
    cocone-AB-join-C X → associative-cocone-data X
  pr1 (associative-cocone-data-cocone-AB-join-C e) = F ∘ inl-join
    where
    F : A * B → _
    F = horizontal-map-cocone pr1 pr2 e
  pr1 (pr2 (associative-cocone-data-cocone-AB-join-C e)) =
    F ∘ inr-join
    where
    F : A * B → _
    F = horizontal-map-cocone pr1 pr2 e
  pr1 (pr2 (pr2 (associative-cocone-data-cocone-AB-join-C e))) = G
    where
    G : C → _
    G = vertical-map-cocone pr1 pr2 e
  pr1 (pr2 (pr2 (pr2 (associative-cocone-data-cocone-AB-join-C e)))) =
    λ a b → ap F (glue-join (a , b))
    where
    F : A * B → _
    F = horizontal-map-cocone pr1 pr2 e
  pr1 (pr2 (pr2 (pr2 (pr2 (associative-cocone-data-cocone-AB-join-C e))))) =
    λ b c → H (inr-join b , c)
    where
    H = coherence-square-cocone pr1 pr2 e

    F : A * B → _
    F = horizontal-map-cocone pr1 pr2 e

    G : C → _
    G = vertical-map-cocone pr1 pr2 e
  pr1
    ( pr2
      ( pr2
        ( pr2
          ( pr2
            ( pr2 (associative-cocone-data-cocone-AB-join-C e)))))) =
    λ a c → H (inl-join a , c)
    where
    H = coherence-square-cocone pr1 pr2 e

    F : A * B → _
    F = horizontal-map-cocone pr1 pr2 e

    G : C → _
    G = vertical-map-cocone pr1 pr2 e
  pr2
    ( pr2
      ( pr2
        ( pr2
          ( pr2
            ( pr2 (associative-cocone-data-cocone-AB-join-C e)))))) a b c =
    equational-reasoning
      ap F p ∙ H (inr-join b , c)
      ＝ H (inl-join a , c) ∙ ap (λ _ → G c) p
        by naturality-homotopy (λ x → H (x , c)) p
      ＝ H (inl-join a , c) ∙ refl
        by ap (H (inl-join a , c) ∙_) (ap-const (G c) p)
      ＝ H (inl-join a , c)
        by right-unit
    where
    p = glue-join (a , b)

    F : A * B → _
    F = horizontal-map-cocone pr1 pr2 e

    G : C → _
    G = vertical-map-cocone pr1 pr2 e

    H : coherence-square-maps pr2 pr1 G F
    H = coherence-square-cocone pr1 pr2 e

  cocone-AB-join-C-normal-form-associative-cocone-data :
    {l4 : Level} {X : UU l4} →
    associative-cocone-data X → cocone-AB-join-C-normal-form X
  pr1
    ( cocone-AB-join-C-normal-form-associative-cocone-data
      ( i , j , k , H , K , L , M)) =
    cocone-F
    where
    cocone-F : cocone pr1 pr2 _
    pr1 cocone-F = i
    pr1 (pr2 cocone-F) = j
    pr2 (pr2 cocone-F) (a , b) = H a b
  pr1
    ( pr2
      ( cocone-AB-join-C-normal-form-associative-cocone-data
        ( i , j , k , H , K , L , M))) =
    k
  pr2
    ( pr2
      ( cocone-AB-join-C-normal-form-associative-cocone-data
        ( i , j , k , H , K , L , M))) =
    dependent-cocone-L
    where
    cocone-F : cocone pr1 pr2 _
    pr1 cocone-F = i
    pr1 (pr2 cocone-F) = j
    pr2 (pr2 cocone-F) (a , b) = H a b

    F : A * B → _
    F = cogap-join _ cocone-F

    compute-inl-F : F ∘ inl-join ~ i
    compute-inl-F = compute-inl-cogap-join cocone-F

    compute-inr-F : F ∘ inr-join ~ j
    compute-inr-F = compute-inr-cogap-join cocone-F

    compute-glue-F :
      statement-coherence-htpy-cocone pr1 pr2
        ( cocone-map pr1 pr2 cocone-join F)
        ( cocone-F)
        ( compute-inl-F)
        ( compute-inr-F)
    compute-glue-F = compute-glue-cogap-join cocone-F

    path-L-inl :
      (a : A) (c : C) → F (inl-join a) ＝ k c
    path-L-inl a c =
      compute-inl-F a ∙ L a c

    path-L-inr :
      (b : B) (c : C) → F (inr-join b) ＝ k c
    path-L-inr b c =
      compute-inr-F b ∙ K b c

    coherence-L :
      (c : C) (a : A) (b : B) →
      dependent-identification
        ( λ x → F x ＝ k c)
        ( glue-join (a , b))
        ( path-L-inl a c)
        ( path-L-inr b c)
    coherence-L c a b =
      map-compute-dependent-identification-eq-value-function
        ( F)
        ( λ _ → k c)
        ( p)
        ( path-L-inl a c)
        ( path-L-inr b c)
        ( coherence-square-cogap-join-constant-data
          ( cocone-F)
          ( k c)
          ( λ b → K b c)
          ( λ a → L a c)
          ( a)
          ( b)
          ( M a b c))
      where
      p = glue-join (a , b)

    dependent-cocone-L :
      (c : C) →
      dependent-cocone pr1 pr2 cocone-join
        ( λ x → F x ＝ k c)
    pr1 (dependent-cocone-L c) a = path-L-inl a c
    pr1 (pr2 (dependent-cocone-L c)) b = path-L-inr b c
    pr2 (pr2 (dependent-cocone-L c)) (a , b) = coherence-L c a b

  associative-cocone-data-cocone-AB-join-C-normal-form :
    {l4 : Level} {X : UU l4} →
    cocone-AB-join-C-normal-form X → associative-cocone-data X
  pr1
    ( associative-cocone-data-cocone-AB-join-C-normal-form
      ( d , k , K)) =
    horizontal-map-cocone pr1 pr2 d
  pr1
    ( pr2
      ( associative-cocone-data-cocone-AB-join-C-normal-form
        ( d , k , K))) =
    vertical-map-cocone pr1 pr2 d
  pr1
    ( pr2
      ( pr2
        ( associative-cocone-data-cocone-AB-join-C-normal-form
          ( d , k , K)))) =
    k
  pr1
    ( pr2
      ( pr2
        ( pr2
          ( associative-cocone-data-cocone-AB-join-C-normal-form
            ( d , k , K))))) =
    λ a b → coherence-square-cocone pr1 pr2 d (a , b)
  pr1
    ( pr2
      ( pr2
        ( pr2
          ( pr2
            ( associative-cocone-data-cocone-AB-join-C-normal-form
              ( d , k , K)))))) =
    λ b c → pr1 (raw c) b
    where
    raw :
      (c : C) → cogap-join-constant-data d (k c)
    raw c =
      cogap-join-constant-data-dependent-cocone d (k c) (K c)
  pr1
    ( pr2
      ( pr2
        ( pr2
          ( pr2
            ( pr2
              ( associative-cocone-data-cocone-AB-join-C-normal-form
                ( d , k , K))))))) =
    λ a c → pr1 (pr2 (raw c)) a
    where
    raw :
      (c : C) → cogap-join-constant-data d (k c)
    raw c =
      cogap-join-constant-data-dependent-cocone d (k c) (K c)
  pr2
    ( pr2
      ( pr2
        ( pr2
          ( pr2
            ( pr2
              ( associative-cocone-data-cocone-AB-join-C-normal-form
                ( d , k , K))))))) a b c =
    pr2 (pr2 (raw c)) a b
    where
    raw :
      (c : C) → cogap-join-constant-data d (k c)
    raw c =
      cogap-join-constant-data-dependent-cocone d (k c) (K c)

  cocone-AB-join-C-associative-cocone-data :
    {l4 : Level} {X : UU l4} →
    associative-cocone-data X → cocone-AB-join-C X
  cocone-AB-join-C-associative-cocone-data =
    cocone-AB-join-C-cocone-AB-join-C-normal-form ∘
    cocone-AB-join-C-normal-form-associative-cocone-data

  is-equiv-cocone-AB-join-C-associative-cocone-data-is-equiv-normal-form :
    {l4 : Level} {X : UU l4} →
    is-equiv
      ( cocone-AB-join-C-normal-form-associative-cocone-data
        { X = X}) →
    is-equiv (cocone-AB-join-C-associative-cocone-data {X = X})
  is-equiv-cocone-AB-join-C-associative-cocone-data-is-equiv-normal-form H =
    is-equiv-comp
      ( cocone-AB-join-C-cocone-AB-join-C-normal-form)
      ( cocone-AB-join-C-normal-form-associative-cocone-data)
      ( H)
      ( is-equiv-cocone-AB-join-C-cocone-AB-join-C-normal-form)

  is-equiv-cocone-AB-join-C-normal-form-associative-cocone-data :
    {l4 : Level} {X : UU l4} →
    is-equiv
      ( cocone-AB-join-C-normal-form-associative-cocone-data
        { X = X})
  is-equiv-cocone-AB-join-C-normal-form-associative-cocone-data =
    is-equiv-htpy
      ( cocone-AB-join-C-normal-form-cocone-AB-join-C-raw-normal-form ∘
        cocone-AB-join-C-raw-normal-form-associative-cocone-data)
      ( refl-htpy)
      ( is-equiv-cocone-AB-join-C-normal-form-associative-cocone-data-raw)

  is-equiv-cocone-AB-join-C-associative-cocone-data :
    {l4 : Level} {X : UU l4} →
    is-equiv (cocone-AB-join-C-associative-cocone-data {X = X})
  is-equiv-cocone-AB-join-C-associative-cocone-data =
    is-equiv-cocone-AB-join-C-associative-cocone-data-is-equiv-normal-form
      ( is-equiv-cocone-AB-join-C-normal-form-associative-cocone-data)

  associative-cocone-data-cocone-A-join-BC :
    {l4 : Level} {X : UU l4} →
    cocone-A-join-BC X → associative-cocone-data X
  pr1 (associative-cocone-data-cocone-A-join-BC d) = i
    where
    i : A → _
    i = horizontal-map-cocone pr1 pr2 d
  pr1 (pr2 (associative-cocone-data-cocone-A-join-BC d)) =
    j ∘ inl-join
    where
    j : B * C → _
    j = vertical-map-cocone pr1 pr2 d
  pr1 (pr2 (pr2 (associative-cocone-data-cocone-A-join-BC d))) =
    j ∘ inr-join
    where
    j : B * C → _
    j = vertical-map-cocone pr1 pr2 d
  pr1 (pr2 (pr2 (pr2 (associative-cocone-data-cocone-A-join-BC d)))) =
    λ a b → H (a , inl-join b)
    where
    H = coherence-square-cocone pr1 pr2 d
  pr1 (pr2 (pr2 (pr2 (pr2 (associative-cocone-data-cocone-A-join-BC d))))) =
    λ b c → ap j (glue-join (b , c))
    where
    j : B * C → _
    j = vertical-map-cocone pr1 pr2 d
  pr1
    ( pr2
      ( pr2
        ( pr2
          ( pr2
            ( pr2 (associative-cocone-data-cocone-A-join-BC d)))))) =
    λ a c → H (a , inr-join c)
    where
    H = coherence-square-cocone pr1 pr2 d
  pr2
    ( pr2
      ( pr2
        ( pr2
          ( pr2
            ( pr2 (associative-cocone-data-cocone-A-join-BC d)))))) a b c =
    equational-reasoning
      H (a , inl-join b) ∙ ap j p
      ＝ ap (λ _ → i a) p ∙ H (a , inr-join c)
        by inv (naturality-homotopy (λ y → H (a , y)) p)
      ＝ refl ∙ H (a , inr-join c)
        by ap (_∙ H (a , inr-join c)) (ap-const (i a) p)
      ＝ H (a , inr-join c)
        by left-unit
    where
    p = glue-join (b , c)

    i : A → _
    i = horizontal-map-cocone pr1 pr2 d

    j : B * C → _
    j = vertical-map-cocone pr1 pr2 d

    H = coherence-square-cocone pr1 pr2 d

  is-equiv-associative-cocone-data-cocone-A-join-BC :
    {l4 : Level} {X : UU l4} →
    is-equiv (associative-cocone-data-cocone-A-join-BC {X = X})
  is-equiv-associative-cocone-data-cocone-A-join-BC =
    is-equiv-htpy
      ( associative-cocone-data-cocone-A-join-BC-raw-normal-form ∘
        cocone-A-join-BC-raw-normal-form-cocone-A-join-BC)
      ( refl-htpy)
      ( is-equiv-comp
        ( associative-cocone-data-cocone-A-join-BC-raw-normal-form)
        ( cocone-A-join-BC-raw-normal-form-cocone-A-join-BC)
        ( is-equiv-cocone-A-join-BC-raw-normal-form-cocone-A-join-BC)
        ( is-equiv-associative-cocone-data-cocone-A-join-BC-raw-normal-form))

  cocone-A-join-BC-normal-form-associative-cocone-data :
    {l4 : Level} {X : UU l4} →
    associative-cocone-data X → cocone-A-join-BC-normal-form X
  pr1
    ( cocone-A-join-BC-normal-form-associative-cocone-data
      ( i , j , k , H , K , L , M)) =
    i
  pr1
    ( pr2
      ( cocone-A-join-BC-normal-form-associative-cocone-data
        ( i , j , k , H , K , L , M))) =
    cocone-J
    where
    cocone-J : cocone pr1 pr2 _
    pr1 cocone-J = j
    pr1 (pr2 cocone-J) = k
    pr2 (pr2 cocone-J) (b , c) = K b c
  pr2
    ( pr2
      ( cocone-A-join-BC-normal-form-associative-cocone-data
        ( i , j , k , H , K , L , M))) =
    dependent-cocone-H
    where
    cocone-J : cocone pr1 pr2 _
    pr1 cocone-J = j
    pr1 (pr2 cocone-J) = k
    pr2 (pr2 cocone-J) (b , c) = K b c

    J : B * C → _
    J = cogap-join _ cocone-J

    compute-inl-J : J ∘ inl-join ~ j
    compute-inl-J = compute-inl-cogap-join cocone-J

    compute-inr-J : J ∘ inr-join ~ k
    compute-inr-J = compute-inr-cogap-join cocone-J

    compute-glue-J :
      statement-coherence-htpy-cocone pr1 pr2
        ( cocone-map pr1 pr2 cocone-join J)
        ( cocone-J)
        ( compute-inl-J)
        ( compute-inr-J)
    compute-glue-J = compute-glue-cogap-join cocone-J

    path-H-inl :
      (a : A) (b : B) → i a ＝ J (inl-join b)
    path-H-inl a b =
      H a b ∙ inv (compute-inl-J b)

    path-H-inr :
      (a : A) (c : C) → i a ＝ J (inr-join c)
    path-H-inr a c =
      L a c ∙ inv (compute-inr-J c)

    right-transpose-compute-glue-J :
      (b : B) (c : C) →
      inv (compute-inl-J b) ∙ ap J (glue-join (b , c)) ＝
      K b c ∙ inv (compute-inr-J c)
    right-transpose-compute-glue-J b c =
      equational-reasoning
        inv linl ∙ apJ
        ＝ (inv linl ∙ apJ) ∙ refl
          by inv right-unit
        ＝ (inv linl ∙ apJ) ∙ (rinr ∙ inv rinr)
          by ap ((inv linl ∙ apJ) ∙_) (inv (right-inv rinr))
        ＝ ((inv linl ∙ apJ) ∙ rinr) ∙ inv rinr
          by inv (assoc (inv linl ∙ apJ) rinr (inv rinr))
        ＝ (inv linl ∙ (apJ ∙ rinr)) ∙ inv rinr
          by ap (_∙ inv rinr) (assoc (inv linl) apJ rinr)
        ＝ (inv linl ∙ (linl ∙ K b c)) ∙ inv rinr
          by ap (λ q → (inv linl ∙ q) ∙ inv rinr) (compute-glue-J (b , c))
        ＝ ((inv linl ∙ linl) ∙ K b c) ∙ inv rinr
          by ap (_∙ inv rinr) (inv (assoc (inv linl) linl (K b c)))
        ＝ (refl ∙ K b c) ∙ inv rinr
          by ap (λ q → (q ∙ K b c) ∙ inv rinr) (left-inv linl)
        ＝ K b c ∙ inv rinr
          by ap (_∙ inv rinr) left-unit
      where
      linl = compute-inl-J b
      rinr = compute-inr-J c
      apJ = ap J (glue-join (b , c))

    coherence-H :
      (a : A) (b : B) (c : C) →
      dependent-identification
        ( λ y → i a ＝ J y)
        ( glue-join (b , c))
        ( path-H-inl a b)
        ( path-H-inr a c)
    coherence-H a b c =
      map-compute-dependent-identification-eq-value-function
        ( λ _ → i a)
        ( J)
        ( p)
        ( path-H-inl a b)
        ( path-H-inr a c)
        ( coherence-square-constant-cogap-join-data
          ( cocone-J)
          ( i a)
          ( H a)
          ( L a)
          ( b)
          ( c)
          ( M a b c))
      where
      p = glue-join (b , c)

    dependent-cocone-H :
      (a : A) →
      dependent-cocone pr1 pr2 cocone-join
        ( λ y → i a ＝ J y)
    pr1 (dependent-cocone-H a) b = path-H-inl a b
    pr1 (pr2 (dependent-cocone-H a)) c = path-H-inr a c
    pr2 (pr2 (dependent-cocone-H a)) (b , c) = coherence-H a b c

  associative-cocone-data-cocone-A-join-BC-normal-form :
    {l4 : Level} {X : UU l4} →
    cocone-A-join-BC-normal-form X → associative-cocone-data X
  pr1
    ( associative-cocone-data-cocone-A-join-BC-normal-form
      ( i , d , H)) =
    i
  pr1
    ( pr2
      ( associative-cocone-data-cocone-A-join-BC-normal-form
        ( i , d , H))) =
    horizontal-map-cocone pr1 pr2 d
  pr1
    ( pr2
      ( pr2
        ( associative-cocone-data-cocone-A-join-BC-normal-form
          ( i , d , H)))) =
    vertical-map-cocone pr1 pr2 d
  pr1
    ( pr2
      ( pr2
        ( pr2
          ( associative-cocone-data-cocone-A-join-BC-normal-form
            ( i , d , H))))) =
    λ a b → pr1 (raw a) b
    where
    raw :
      (a : A) → constant-cogap-join-data d (i a)
    raw a =
      constant-cogap-join-data-dependent-cocone d (i a) (H a)
  pr1
    ( pr2
      ( pr2
        ( pr2
          ( pr2
            ( associative-cocone-data-cocone-A-join-BC-normal-form
              ( i , d , H)))))) =
    λ b c → coherence-square-cocone pr1 pr2 d (b , c)
  pr1
    ( pr2
      ( pr2
        ( pr2
          ( pr2
            ( pr2
              ( associative-cocone-data-cocone-A-join-BC-normal-form
                ( i , d , H))))))) =
    λ a c → pr1 (pr2 (raw a)) c
    where
    raw :
      (a : A) → constant-cogap-join-data d (i a)
    raw a =
      constant-cogap-join-data-dependent-cocone d (i a) (H a)
  pr2
    ( pr2
      ( pr2
        ( pr2
          ( pr2
            ( pr2
              ( associative-cocone-data-cocone-A-join-BC-normal-form
                ( i , d , H))))))) a b c =
    pr2 (pr2 (raw a)) b c
    where
    raw :
      (a : A) → constant-cogap-join-data d (i a)
    raw a =
      constant-cogap-join-data-dependent-cocone d (i a) (H a)

  cocone-A-join-BC-associative-cocone-data :
    {l4 : Level} {X : UU l4} →
    associative-cocone-data X → cocone-A-join-BC X
  cocone-A-join-BC-associative-cocone-data =
    cocone-A-join-BC-cocone-A-join-BC-normal-form ∘
    cocone-A-join-BC-normal-form-associative-cocone-data

  is-equiv-cocone-A-join-BC-associative-cocone-data-is-equiv-normal-form :
    {l4 : Level} {X : UU l4} →
    is-equiv
      ( cocone-A-join-BC-normal-form-associative-cocone-data
        { X = X}) →
    is-equiv (cocone-A-join-BC-associative-cocone-data {X = X})
  is-equiv-cocone-A-join-BC-associative-cocone-data-is-equiv-normal-form H =
    is-equiv-comp
      ( cocone-A-join-BC-cocone-A-join-BC-normal-form)
      ( cocone-A-join-BC-normal-form-associative-cocone-data)
      ( H)
      ( is-equiv-cocone-A-join-BC-cocone-A-join-BC-normal-form)

  is-equiv-cocone-A-join-BC-normal-form-associative-cocone-data :
    {l4 : Level} {X : UU l4} →
    is-equiv
      ( cocone-A-join-BC-normal-form-associative-cocone-data
        { X = X})
  is-equiv-cocone-A-join-BC-normal-form-associative-cocone-data =
    is-equiv-htpy
      ( cocone-A-join-BC-normal-form-cocone-A-join-BC-raw-normal-form ∘
        cocone-A-join-BC-raw-normal-form-associative-cocone-data)
      ( refl-htpy)
      ( is-equiv-cocone-A-join-BC-normal-form-associative-cocone-data-raw)

  is-equiv-cocone-A-join-BC-associative-cocone-data :
    {l4 : Level} {X : UU l4} →
    is-equiv (cocone-A-join-BC-associative-cocone-data {X = X})
  is-equiv-cocone-A-join-BC-associative-cocone-data =
    is-equiv-cocone-A-join-BC-associative-cocone-data-is-equiv-normal-form
      ( is-equiv-cocone-A-join-BC-normal-form-associative-cocone-data)

  tri-join-rec-data-cocone-A-join-BC-normal-form :
    {l4 : Level} {X : UU l4} →
    cocone-A-join-BC X → tri-join-rec-data A B C X
  tri-join-rec-data-cocone-A-join-BC-normal-form =
    tri-join-rec-data-associative-cocone-data ∘
    associative-cocone-data-cocone-A-join-BC

  is-equiv-tri-join-rec-data-cocone-A-join-BC-normal-form :
    {l4 : Level} {X : UU l4} →
    is-equiv (tri-join-rec-data-cocone-A-join-BC-normal-form {X = X})
  is-equiv-tri-join-rec-data-cocone-A-join-BC-normal-form =
    is-equiv-comp
      ( tri-join-rec-data-associative-cocone-data)
      ( associative-cocone-data-cocone-A-join-BC)
      ( is-equiv-associative-cocone-data-cocone-A-join-BC)
      ( is-equiv-map-inv-equiv
        ( equiv-associative-cocone-data-tri-join-rec-data))

  equiv-tri-join-rec-data-cocone-A-join-BC-normal-form :
    {l4 : Level} {X : UU l4} →
    cocone-A-join-BC X ≃ tri-join-rec-data A B C X
  pr1 equiv-tri-join-rec-data-cocone-A-join-BC-normal-form =
    tri-join-rec-data-cocone-A-join-BC-normal-form
  pr2 equiv-tri-join-rec-data-cocone-A-join-BC-normal-form =
    is-equiv-tri-join-rec-data-cocone-A-join-BC-normal-form

  tri-join-rec-data-map-A-join-BC :
    {l4 : Level} {X : UU l4} →
    (A * (B * C) → X) → tri-join-rec-data A B C X
  tri-join-rec-data-map-A-join-BC =
    tri-join-rec-data-cocone-A-join-BC-normal-form ∘
    cocone-map pr1 pr2 (cocone-join {A = A} {B = B * C})

  is-equiv-tri-join-rec-data-map-A-join-BC :
    {l4 : Level} {X : UU l4} →
    is-equiv (tri-join-rec-data-map-A-join-BC {X = X})
  is-equiv-tri-join-rec-data-map-A-join-BC {X = X} =
    is-equiv-comp
      ( tri-join-rec-data-cocone-A-join-BC-normal-form)
      ( cocone-map pr1 pr2 (cocone-join {A = A} {B = B * C}))
      ( is-equiv-cocone-map-standard-join X)
      ( is-equiv-tri-join-rec-data-cocone-A-join-BC-normal-form)

  equiv-tri-join-rec-data-map-A-join-BC :
    {l4 : Level} {X : UU l4} →
    (A * (B * C) → X) ≃ tri-join-rec-data A B C X
  pr1 equiv-tri-join-rec-data-map-A-join-BC =
    tri-join-rec-data-map-A-join-BC
  pr2 equiv-tri-join-rec-data-map-A-join-BC =
    is-equiv-tri-join-rec-data-map-A-join-BC

  rec-tri-join :
    {l4 : Level} {X : UU l4} →
    tri-join-rec-data A B C X → A * (B * C) → X
  rec-tri-join =
    map-inv-equiv equiv-tri-join-rec-data-map-A-join-BC

  is-section-rec-tri-join :
    {l4 : Level} {X : UU l4} →
    tri-join-rec-data-map-A-join-BC ∘ rec-tri-join {X = X} ~ id
  is-section-rec-tri-join =
    is-section-map-inv-equiv equiv-tri-join-rec-data-map-A-join-BC

  is-retraction-rec-tri-join :
    {l4 : Level} {X : UU l4} →
    rec-tri-join ∘ tri-join-rec-data-map-A-join-BC {X = X} ~ id
  is-retraction-rec-tri-join =
    is-retraction-map-inv-equiv equiv-tri-join-rec-data-map-A-join-BC

  naturality-glue-left-join-swapped :
    (b : B) (a : A) (c : C) →
    glue-join (b , inl-join a) ∙
    ap inr-join (glue-join (a , c)) ＝
    glue-join (b , inr-join c)
  naturality-glue-left-join-swapped b a c =
    inv
      ( map-inv-compute-dependent-identification-eq-value-function
        ( λ _ → inl-join {A = B} {B = A * C} b)
        ( inr-join)
        ( glue-join (a , c))
        ( glue-join (b , inl-join a))
        ( glue-join (b , inr-join c))
        ( apd (λ y → glue-join (b , y)) (glue-join (a , c)))) ∙
    ap
      ( λ p → p ∙ glue-join (b , inr-join c))
      ( ap-const
        ( inl-join {A = B} {B = A * C} b)
        ( glue-join (a , c)))

  canonical-swapped-tri-join-rec-data :
    tri-join-rec-data B A C (B * (A * C))
  canonical-swapped-tri-join-rec-data =
    make-tri-join-rec-data
      ( inl-join)
      ( inr-join ∘ inl-join)
      ( inr-join ∘ inr-join)
      ( λ b a → glue-join (b , inl-join a))
      ( λ b c → glue-join (b , inr-join c))
      ( λ a c → ap inr-join (glue-join (a , c)))
      ( naturality-glue-left-join-swapped)

  map-twist-tri-join :
    A * (B * C) → B * (A * C)
  map-twist-tri-join =
    rec-tri-join
      ( twist-tri-join-rec-data
        ( canonical-swapped-tri-join-rec-data))

  compute-tri-join-rec-data-map-twist-tri-join :
    tri-join-rec-data-map-A-join-BC map-twist-tri-join ＝
    twist-tri-join-rec-data canonical-swapped-tri-join-rec-data
  compute-tri-join-rec-data-map-twist-tri-join =
    is-section-rec-tri-join
      ( twist-tri-join-rec-data canonical-swapped-tri-join-rec-data)

  triangle-cocone-AB-join-C-cocone-A-join-BC-associative-cocone-data :
    {l4 : Level} {X : UU l4} (d : cocone-A-join-BC X) →
    cocone-AB-join-C-associative-cocone-data
      ( associative-cocone-data-cocone-A-join-BC d) ＝
    cocone-AB-join-C-cocone-A-join-BC d
  triangle-cocone-AB-join-C-cocone-A-join-BC-associative-cocone-data d =
    eq-htpy-cocone pr1 pr2 _ _
      ( refl-htpy ,
        refl-htpy ,
        λ (x , c) →
          right-unit ∙
          htpy-eq
            ( htpy-eq
              ( is-section-map-inv-equiv equiv-ev-pair H')
              ( x))
            ( c) ∙
          inv left-unit)
    where
    H' :
      (x : A * B) (c : C) →
      map-AB-cocone-A-join-BC d x ＝
      vertical-map-cocone pr1 pr2 d (inr-join c)
    H' x c =
      dependent-cogap-join
        ( pr2
          ( pr2
            ( cocone-AB-join-C-normal-form-associative-cocone-data
              ( associative-cocone-data-cocone-A-join-BC d)))
          c)
        ( x)

    H :
      (x : A * B) (c : C) →
      map-AB-cocone-A-join-BC d x ＝
      vertical-map-cocone pr1 pr2 d (inr-join c)
    H x c =
      dependent-cogap-join (dependent-cocone-H-cocone-A-join-BC d c) x

  triangle-cocone-A-join-BC-cocone-AB-join-C-associative-cocone-data :
    {l4 : Level} {X : UU l4} (e : cocone-AB-join-C X) →
    cocone-A-join-BC-associative-cocone-data
      ( associative-cocone-data-cocone-AB-join-C e) ＝
    cocone-A-join-BC-cocone-AB-join-C e
  triangle-cocone-A-join-BC-cocone-AB-join-C-associative-cocone-data e =
    eq-htpy-cocone pr1 pr2 _ _
      ( refl-htpy ,
        refl-htpy ,
        λ (a , y) →
          right-unit ∙
          htpy-eq
            ( htpy-eq
              ( is-section-map-inv-equiv equiv-ev-pair H)
              ( a))
            ( y) ∙
          inv left-unit)
    where
    H :
      (a : A) (y : B * C) →
      horizontal-map-cocone pr1 pr2 e (inl-join a) ＝
      map-BC-cocone-AB-join-C e y
    H a y =
      dependent-cogap-join (dependent-cocone-K-cocone-AB-join-C e a) y

  is-equiv-cocone-AB-join-C-cocone-A-join-BC-is-equiv-associative-cocone-data :
    {l4 : Level} {X : UU l4} →
    is-equiv (associative-cocone-data-cocone-A-join-BC {X = X}) →
    is-equiv (cocone-AB-join-C-associative-cocone-data {X = X}) →
    is-equiv (cocone-AB-join-C-cocone-A-join-BC {X = X})
  is-equiv-cocone-AB-join-C-cocone-A-join-BC-is-equiv-associative-cocone-data
    is-equiv-data is-equiv-cocone =
    is-equiv-htpy
      ( cocone-AB-join-C-associative-cocone-data ∘
        associative-cocone-data-cocone-A-join-BC)
      ( λ d →
        inv
          ( triangle-cocone-AB-join-C-cocone-A-join-BC-associative-cocone-data
            d))
      ( is-equiv-comp
        ( cocone-AB-join-C-associative-cocone-data)
        ( associative-cocone-data-cocone-A-join-BC)
        ( is-equiv-data)
        ( is-equiv-cocone))

  is-equiv-cocone-AB-join-C-cocone-A-join-BC :
    {l4 : Level} {X : UU l4} →
    is-equiv (cocone-AB-join-C-cocone-A-join-BC {X = X})
  is-equiv-cocone-AB-join-C-cocone-A-join-BC =
    is-equiv-cocone-AB-join-C-cocone-A-join-BC-is-equiv-associative-cocone-data
      ( is-equiv-associative-cocone-data-cocone-A-join-BC)
      ( is-equiv-cocone-AB-join-C-associative-cocone-data)

  path-inl-htpy-horizontal-cocone-map-associative-join :
    {l4 : Level} {X : UU l4} (h : A * (B * C) → X)
    (a : A) →
    h (map-left-associative-join (inl-join a)) ＝
    map-AB-cocone-A-join-BC
      ( cocone-map pr1 pr2
        ( cocone-join {A = A} {B = B * C})
        ( h))
      ( inl-join a)
  path-inl-htpy-horizontal-cocone-map-associative-join h a =
    ap h (compute-inl-map-left-associative-join a) ∙
    inv
      ( compute-inl-map-AB-cocone-A-join-BC
        ( cocone-map pr1 pr2
          ( cocone-join {A = A} {B = B * C})
          ( h))
        ( a))

  path-inr-htpy-horizontal-cocone-map-associative-join :
    {l4 : Level} {X : UU l4} (h : A * (B * C) → X)
    (b : B) →
    h (map-left-associative-join (inr-join b)) ＝
    map-AB-cocone-A-join-BC
      ( cocone-map pr1 pr2
        ( cocone-join {A = A} {B = B * C})
        ( h))
      ( inr-join b)
  path-inr-htpy-horizontal-cocone-map-associative-join h b =
    ap h (compute-inr-map-left-associative-join b) ∙
    inv
      ( compute-inr-map-AB-cocone-A-join-BC
        ( cocone-map pr1 pr2
          ( cocone-join {A = A} {B = B * C})
          ( h))
        ( b))

  coherence-htpy-horizontal-cocone-map-associative-join :
    {l4 : Level} {X : UU l4} (h : A * (B * C) → X)
    (a : A) (b : B) →
    dependent-identification
      ( λ x →
        h (map-left-associative-join x) ＝
        map-AB-cocone-A-join-BC
          ( cocone-map pr1 pr2
            ( cocone-join {A = A} {B = B * C})
            ( h))
          ( x))
      ( glue-join (a , b))
      ( path-inl-htpy-horizontal-cocone-map-associative-join h a)
      ( path-inr-htpy-horizontal-cocone-map-associative-join h b)
  coherence-htpy-horizontal-cocone-map-associative-join {X = X} h a b =
    map-compute-dependent-identification-eq-value-function
      ( h ∘ map-left-associative-join)
      ( map-AB-cocone-A-join-BC
        ( cocone-map pr1 pr2
          ( cocone-join {A = A} {B = B * C})
          ( h)))
      ( glue-join (a , b))
      ( path-inl-htpy-horizontal-cocone-map-associative-join h a)
      ( path-inr-htpy-horizontal-cocone-map-associative-join h b)
      ( equational-reasoning
        ap (h ∘ map-left-associative-join) p ∙
        (ap h linrL ∙ inv linrG)
        ＝
        (ap (h ∘ map-left-associative-join) p ∙ ap h linrL) ∙
        inv linrG
          by inv (assoc (ap (h ∘ map-left-associative-join) p)
            (ap h linrL)
            (inv linrG))
        ＝ (ap h (ap map-left-associative-join p) ∙ ap h linrL) ∙
          inv linrG
          by ap (λ q → (q ∙ ap h linrL) ∙ inv linrG)
            ( ap-comp h map-left-associative-join p)
        ＝ ap h (ap map-left-associative-join p ∙ linrL) ∙
          inv linrG
          by ap (_∙ inv linrG)
            ( inv
              ( ap-concat h (ap map-left-associative-join p) linrL))
        ＝ ap h (linlL ∙ glueOuter) ∙ inv linrG
          by ap (λ q → ap h q ∙ inv linrG)
            ( compute-glue-map-left-associative-join (a , b))
        ＝ (ap h linlL ∙ ap h glueOuter) ∙ inv linrG
          by ap (_∙ inv linrG) (ap-concat h linlL glueOuter)
        ＝ ap h linlL ∙ (ap h glueOuter ∙ inv linrG)
          by assoc (ap h linlL) (ap h glueOuter) (inv linrG)
        ＝ ap h linlL ∙ (inv linlG ∙ apG)
          by ap (ap h linlL ∙_)
            ( inv (right-transpose-compute-glue-cogap-join dAB a b))
        ＝ (ap h linlL ∙ inv linlG) ∙ apG
          by inv (assoc (ap h linlL) (inv linlG) apG))
    where
    d :
      cocone
        ( λ (t : A × (B * C)) → pr1 t)
        ( λ (t : A × (B * C)) → pr2 t)
        ( X)
    d =
      cocone-map pr1 pr2
        ( cocone-join {A = A} {B = B * C})
        ( h)

    dAB : cocone {S = A × B} {A = A} {B = B} pr1 pr2 X
    dAB = cocone-AB-cocone-A-join-BC d

    G : A * B → X
    G = map-AB-cocone-A-join-BC d

    p = glue-join (a , b)
    glueOuter = glue-join (a , inl-join b)
    linlL = compute-inl-map-left-associative-join a
    linrL = compute-inr-map-left-associative-join b
    linlG = compute-inl-map-AB-cocone-A-join-BC d a
    linrG = compute-inr-map-AB-cocone-A-join-BC d b
    apG = ap G p

  dependent-cocone-htpy-horizontal-cocone-map-associative-join :
    {l4 : Level} {X : UU l4} (h : A * (B * C) → X) →
    dependent-cocone pr1 pr2 cocone-join
      ( λ x →
        h (map-left-associative-join x) ＝
        map-AB-cocone-A-join-BC
          ( cocone-map pr1 pr2
            ( cocone-join {A = A} {B = B * C})
            ( h))
          ( x))
  pr1 (dependent-cocone-htpy-horizontal-cocone-map-associative-join h) =
    path-inl-htpy-horizontal-cocone-map-associative-join h
  pr1 (pr2 (dependent-cocone-htpy-horizontal-cocone-map-associative-join h)) =
    path-inr-htpy-horizontal-cocone-map-associative-join h
  pr2 (pr2 (dependent-cocone-htpy-horizontal-cocone-map-associative-join h))
    ( a , b) =
    coherence-htpy-horizontal-cocone-map-associative-join h a b

  htpy-horizontal-cocone-map-associative-join :
    {l4 : Level} {X : UU l4} (h : A * (B * C) → X) →
    (h ∘ map-left-associative-join) ~
    horizontal-map-cocone pr1 pr2
      ( cocone-AB-join-C-cocone-A-join-BC
        ( cocone-map pr1 pr2
          ( cocone-join {A = A} {B = B * C})
          ( h)))
  htpy-horizontal-cocone-map-associative-join h =
    dependent-cogap-join
      ( dependent-cocone-htpy-horizontal-cocone-map-associative-join h)

  htpy-horizontal-cocone-map-associative-join-compute :
    {l4 : Level} {X : UU l4} (h : A * (B * C) → X) →
    (h ∘ map-left-associative-join) ~
    horizontal-map-cocone pr1 pr2
      ( cocone-AB-join-C-cocone-A-join-BC
        ( cocone-map pr1 pr2
          ( cocone-join {A = A} {B = B * C})
          ( h)))
  htpy-horizontal-cocone-map-associative-join-compute h =
    inv-htpy
      ( htpy-cogap-join-cocone-map-compute
        ( cocone-left-map-associative-join)
        ( h))

  htpy-vertical-cocone-map-associative-join :
    {l4 : Level} {X : UU l4} (h : A * (B * C) → X) →
    (h ∘ inr-join ∘ inr-join) ~
    vertical-map-cocone pr1 pr2
      ( cocone-AB-join-C-cocone-A-join-BC
        ( cocone-map pr1 pr2
          ( cocone-join {A = A} {B = B * C})
          ( h)))
  htpy-vertical-cocone-map-associative-join h = refl-htpy

  target-to-source-htpy-horizontal-cocone-map-associative-join :
    {l4 : Level} {X : UU l4} (h : A * (B * C) → X) →
    horizontal-map-cocone pr1 pr2
      ( cocone-AB-join-C-cocone-A-join-BC
        ( cocone-map pr1 pr2
          ( cocone-join {A = A} {B = B * C})
          ( h))) ~
    (h ∘ map-left-associative-join)
  target-to-source-htpy-horizontal-cocone-map-associative-join h =
    htpy-cogap-join-cocone-map-compute
      ( cocone-left-map-associative-join)
      ( h)

  path-inl-target-to-source-coherence-htpy-cocone-map-associative-join :
    {l4 : Level} {X : UU l4} (h : A * (B * C) → X)
    (a : A) (c : C) →
    target-to-source-htpy-horizontal-cocone-map-associative-join h
      ( inl-join a) ∙
    ( ap h (coherence-map-associative-join (inl-join a) c) ∙ refl) ＝
    dependent-cogap-join
      ( dependent-cocone-H-cocone-A-join-BC
        ( cocone-map pr1 pr2
          ( cocone-join {A = A} {B = B * C})
          ( h))
        ( c))
      ( inl-join a)
  path-inl-target-to-source-coherence-htpy-cocone-map-associative-join
    {X = X} h a c =
    equational-reasoning
      H (inl-join a) ∙ (ap h coh ∙ refl)
      ＝ pH ∙ (ap h coh ∙ refl)
        by ap (_∙ (ap h coh ∙ refl)) compute-inl-H
      ＝ pH ∙ ap h coh
        by ap (pH ∙_) right-unit
      ＝ (linlG ∙ inv (ap h linlL)) ∙
        ap h (linlL ∙ glueOuter)
        by ap (pH ∙_) (ap (ap h) compute-coh)
      ＝ (linlG ∙ inv (ap h linlL)) ∙
        (ap h linlL ∙ ap h glueOuter)
        by ap (pH ∙_) (ap-concat h linlL glueOuter)
      ＝ linlG ∙
        (inv (ap h linlL) ∙ (ap h linlL ∙ ap h glueOuter))
        by assoc linlG (inv (ap h linlL)) (ap h linlL ∙ ap h glueOuter)
      ＝ linlG ∙ ((inv (ap h linlL) ∙ ap h linlL) ∙ ap h glueOuter)
        by ap (linlG ∙_)
          ( inv (assoc (inv (ap h linlL)) (ap h linlL) (ap h glueOuter)))
      ＝ linlG ∙ (refl ∙ ap h glueOuter)
        by ap (λ q → linlG ∙ (q ∙ ap h glueOuter))
          ( left-inv (ap h linlL))
      ＝ linlG ∙ ap h glueOuter
        by ap (linlG ∙_) left-unit
      ＝ dependent-cogap-join
        ( dependent-cocone-H-cocone-A-join-BC d c)
        ( inl-join a)
        by inv compute-inl-target
    where
    d :
      cocone
        ( λ (t : A × (B * C)) → pr1 t)
        ( λ (t : A × (B * C)) → pr2 t)
        ( X)
    d =
      cocone-map pr1 pr2
        ( cocone-join {A = A} {B = B * C})
        ( h)

    H = target-to-source-htpy-horizontal-cocone-map-associative-join h
    coh = coherence-map-associative-join (inl-join a) c
    linlL = compute-inl-map-left-associative-join a
    glueOuter = glue-join (a , inr-join c)
    linlG = compute-inl-map-AB-cocone-A-join-BC d a
    pH = path-inl-htpy-cogap-join-cocone-map
      cocone-left-map-associative-join h a

    compute-inl-H =
      compute-inl-dependent-cogap-join
        ( dependent-cocone-htpy-cogap-join-cocone-map
          cocone-left-map-associative-join h)
        ( a)

    compute-coh = compute-inl-coherence-map-associative-join a c

    compute-inl-target =
      compute-inl-dependent-cogap-join
        ( dependent-cocone-H-cocone-A-join-BC d c)
        ( a)

  path-inr-target-to-source-coherence-htpy-cocone-map-associative-join :
    {l4 : Level} {X : UU l4} (h : A * (B * C) → X)
    (b : B) (c : C) →
    target-to-source-htpy-horizontal-cocone-map-associative-join h
      ( inr-join b) ∙
    ( ap h (coherence-map-associative-join (inr-join b) c) ∙ refl) ＝
    dependent-cogap-join
      ( dependent-cocone-H-cocone-A-join-BC
        ( cocone-map pr1 pr2
          ( cocone-join {A = A} {B = B * C})
          ( h))
        ( c))
      ( inr-join b)
  path-inr-target-to-source-coherence-htpy-cocone-map-associative-join
    {X = X} h b c =
    equational-reasoning
      H (inr-join b) ∙ (ap h coh ∙ refl)
      ＝ pH ∙ (ap h coh ∙ refl)
        by ap (_∙ (ap h coh ∙ refl)) compute-inr-H
      ＝ pH ∙ ap h coh
        by ap (pH ∙_) right-unit
      ＝ (linrG ∙ inv (ap h linrL)) ∙ ap h (linrL ∙ apinr)
        by ap (pH ∙_) (ap (ap h) compute-coh)
      ＝ (linrG ∙ inv (ap h linrL)) ∙
        (ap h linrL ∙ ap h apinr)
        by ap (pH ∙_) (ap-concat h linrL apinr)
      ＝ linrG ∙
        (inv (ap h linrL) ∙ (ap h linrL ∙ ap h apinr))
        by assoc linrG (inv (ap h linrL)) (ap h linrL ∙ ap h apinr)
      ＝ linrG ∙ ((inv (ap h linrL) ∙ ap h linrL) ∙ ap h apinr)
        by ap (linrG ∙_)
          ( inv (assoc (inv (ap h linrL)) (ap h linrL) (ap h apinr)))
      ＝ linrG ∙ (refl ∙ ap h apinr)
        by ap (λ q → linrG ∙ (q ∙ ap h apinr))
          ( left-inv (ap h linrL))
      ＝ linrG ∙ ap h apinr
        by ap (linrG ∙_) left-unit
      ＝ linrG ∙ ap (h ∘ inr-join) p
        by ap (linrG ∙_) (inv (ap-comp h inr-join p))
      ＝ dependent-cogap-join
        ( dependent-cocone-H-cocone-A-join-BC d c)
        ( inr-join b)
        by inv compute-inr-target
    where
    d :
      cocone
        ( λ (t : A × (B * C)) → pr1 t)
        ( λ (t : A × (B * C)) → pr2 t)
        ( X)
    d =
      cocone-map pr1 pr2
        ( cocone-join {A = A} {B = B * C})
        ( h)

    H = target-to-source-htpy-horizontal-cocone-map-associative-join h
    coh = coherence-map-associative-join (inr-join b) c
    p = glue-join (b , c)
    linrL = compute-inr-map-left-associative-join b
    apinr = ap inr-join p
    linrG = compute-inr-map-AB-cocone-A-join-BC d b
    pH = path-inr-htpy-cogap-join-cocone-map
      cocone-left-map-associative-join h b

    compute-inr-H =
      compute-inr-dependent-cogap-join
        ( dependent-cocone-htpy-cogap-join-cocone-map
          cocone-left-map-associative-join h)
        ( b)

    compute-coh = compute-inr-coherence-map-associative-join b c

    compute-inr-target =
      compute-inr-dependent-cogap-join
        ( dependent-cocone-H-cocone-A-join-BC d c)
        ( b)

  path-inl-coherence-htpy-cocone-map-associative-join :
    {l4 : Level} {X : UU l4} (h : A * (B * C) → X)
    (a : A) (c : C) →
    ap h (coherence-map-associative-join (inl-join a) c) ∙ refl ＝
    htpy-horizontal-cocone-map-associative-join h (inl-join a) ∙
    dependent-cogap-join
      ( dependent-cocone-H-cocone-A-join-BC
        ( cocone-map pr1 pr2
          ( cocone-join {A = A} {B = B * C})
          ( h))
        ( c))
      ( inl-join a)
  path-inl-coherence-htpy-cocone-map-associative-join {X = X} h a c =
    equational-reasoning
      ap h coh ∙ refl
      ＝ ap h coh
        by right-unit
      ＝ ap h (linlL ∙ glueOuter)
        by ap (ap h) (compute-inl-coherence-map-associative-join a c)
      ＝ ap h linlL ∙ ap h glueOuter
        by ap-concat h linlL glueOuter
      ＝ ap h linlL ∙ (refl ∙ ap h glueOuter)
        by ap (ap h linlL ∙_) (inv left-unit)
      ＝ ap h linlL ∙ ((inv linlG ∙ linlG) ∙ ap h glueOuter)
        by ap (λ q → ap h linlL ∙ (q ∙ ap h glueOuter))
          ( inv (left-inv linlG))
      ＝ ap h linlL ∙ (inv linlG ∙ (linlG ∙ ap h glueOuter))
        by ap (ap h linlL ∙_) (assoc (inv linlG) linlG (ap h glueOuter))
      ＝ (ap h linlL ∙ inv linlG) ∙ (linlG ∙ ap h glueOuter)
        by inv (assoc (ap h linlL) (inv linlG) (linlG ∙ ap h glueOuter))
      ＝ htpy-horizontal-cocone-map-associative-join h (inl-join a) ∙
        dependent-cogap-join
          ( dependent-cocone-H-cocone-A-join-BC d c)
          ( inl-join a)
        by inv
          ( ap-binary
            ( _∙_)
            ( compute-inl-dependent-cogap-join
              ( dependent-cocone-htpy-horizontal-cocone-map-associative-join h)
              ( a))
            ( compute-inl-dependent-cogap-join
              ( dependent-cocone-H-cocone-A-join-BC d c)
              ( a)))
    where
    d :
      cocone
        ( λ (t : A × (B * C)) → pr1 t)
        ( λ (t : A × (B * C)) → pr2 t)
        ( X)
    d =
      cocone-map pr1 pr2
        ( cocone-join {A = A} {B = B * C})
        ( h)

    coh = coherence-map-associative-join (inl-join a) c
    linlL = compute-inl-map-left-associative-join a
    glueOuter = glue-join (a , inr-join c)
    linlG = compute-inl-map-AB-cocone-A-join-BC d a

  path-inr-coherence-htpy-cocone-map-associative-join :
    {l4 : Level} {X : UU l4} (h : A * (B * C) → X)
    (b : B) (c : C) →
    ap h (coherence-map-associative-join (inr-join b) c) ∙ refl ＝
    htpy-horizontal-cocone-map-associative-join h (inr-join b) ∙
    dependent-cogap-join
      ( dependent-cocone-H-cocone-A-join-BC
        ( cocone-map pr1 pr2
          ( cocone-join {A = A} {B = B * C})
          ( h))
        ( c))
      ( inr-join b)
  path-inr-coherence-htpy-cocone-map-associative-join {X = X} h b c =
    equational-reasoning
      ap h coh ∙ refl
      ＝ ap h coh
        by right-unit
      ＝ ap h (linrL ∙ apinr)
        by ap (ap h) (compute-inr-coherence-map-associative-join b c)
      ＝ ap h linrL ∙ ap h apinr
        by ap-concat h linrL apinr
      ＝ ap h linrL ∙ ap (h ∘ inr-join) p
        by ap (ap h linrL ∙_) (inv (ap-comp h inr-join p))
      ＝ ap h linrL ∙ (refl ∙ ap (h ∘ inr-join) p)
        by ap (ap h linrL ∙_) (inv left-unit)
      ＝ ap h linrL ∙ ((inv linrG ∙ linrG) ∙ ap (h ∘ inr-join) p)
        by ap (λ q → ap h linrL ∙ (q ∙ ap (h ∘ inr-join) p))
          ( inv (left-inv linrG))
      ＝ ap h linrL ∙ (inv linrG ∙ (linrG ∙ ap (h ∘ inr-join) p))
        by ap (ap h linrL ∙_)
          ( assoc (inv linrG) linrG (ap (h ∘ inr-join) p))
      ＝ (ap h linrL ∙ inv linrG) ∙
        (linrG ∙ ap (h ∘ inr-join) p)
        by inv
          ( assoc
            ( ap h linrL)
            ( inv linrG)
            ( linrG ∙ ap (h ∘ inr-join) p))
      ＝ htpy-horizontal-cocone-map-associative-join h (inr-join b) ∙
        dependent-cogap-join
          ( dependent-cocone-H-cocone-A-join-BC d c)
          ( inr-join b)
        by inv
          ( ap-binary
            ( _∙_)
            ( compute-inr-dependent-cogap-join
              ( dependent-cocone-htpy-horizontal-cocone-map-associative-join h)
              ( b))
            ( compute-inr-dependent-cogap-join
              ( dependent-cocone-H-cocone-A-join-BC d c)
              ( b)))
    where
    d :
      cocone
        ( λ (t : A × (B * C)) → pr1 t)
        ( λ (t : A × (B * C)) → pr2 t)
        ( X)
    d =
      cocone-map pr1 pr2
        ( cocone-join {A = A} {B = B * C})
        ( h)

    coh = coherence-map-associative-join (inr-join b) c
    p = glue-join (b , c)
    linrL = compute-inr-map-left-associative-join b
    apinr = ap inr-join p
    linrG = compute-inr-map-AB-cocone-A-join-BC d b

  is-equiv-cocone-A-join-BC-cocone-AB-join-C-is-equiv-associative-cocone-data :
    {l4 : Level} {X : UU l4} →
    is-equiv (associative-cocone-data-cocone-AB-join-C {X = X}) →
    is-equiv (cocone-A-join-BC-associative-cocone-data {X = X}) →
    is-equiv (cocone-A-join-BC-cocone-AB-join-C {X = X})
  is-equiv-cocone-A-join-BC-cocone-AB-join-C-is-equiv-associative-cocone-data
    is-equiv-data is-equiv-cocone =
    is-equiv-htpy
      ( cocone-A-join-BC-associative-cocone-data ∘
        associative-cocone-data-cocone-AB-join-C)
      ( λ e →
        inv
          ( triangle-cocone-A-join-BC-cocone-AB-join-C-associative-cocone-data
            e))
      ( is-equiv-comp
        ( cocone-A-join-BC-associative-cocone-data)
        ( associative-cocone-data-cocone-AB-join-C)
        ( is-equiv-data)
        ( is-equiv-cocone))

  vertical-htpy-section-cocone-A-join-BC-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} (e : cocone-AB-join-C X) →
    pr1
      ( pr2
        ( cocone-AB-join-C-cocone-A-join-BC
          ( cocone-A-join-BC-cocone-AB-join-C e))) ~
    pr1 (pr2 e)
  vertical-htpy-section-cocone-A-join-BC-cocone-AB-join-C e =
    compute-inr-map-BC-cocone-AB-join-C e

  dependent-cocone-horizontal-htpy-section-cocone-A-join-BC-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} (e : cocone-AB-join-C X) →
    dependent-cocone pr1 pr2 cocone-join
      ( λ x →
        map-AB-cocone-A-join-BC
          ( cocone-A-join-BC-cocone-AB-join-C e) x ＝
        horizontal-map-cocone pr1 pr2 e x)
  dependent-cocone-horizontal-htpy-section-cocone-A-join-BC-cocone-AB-join-C
    e@(F , G , H) =
    dependent-cocone-F
    where
    d : cocone-A-join-BC _
    d = cocone-A-join-BC-cocone-AB-join-C e

    J : B * C → _
    J = map-BC-cocone-AB-join-C e

    compute-inl-J : J ∘ inl-join ~ F ∘ inr-join
    compute-inl-J = compute-inl-map-BC-cocone-AB-join-C e

    F' : A * B → _
    F' = map-AB-cocone-A-join-BC d

    compute-inl-F' : F' ∘ inl-join ~ F ∘ inl-join
    compute-inl-F' = compute-inl-map-AB-cocone-A-join-BC d

    compute-inr-F' : F' ∘ inr-join ~ J ∘ inl-join
    compute-inr-F' = compute-inr-map-AB-cocone-A-join-BC d

    compute-glue-F' :
      statement-coherence-htpy-cocone pr1 pr2
        ( cocone-map pr1 pr2 cocone-join F')
        ( cocone-AB-cocone-A-join-BC d)
        ( compute-inl-F')
        ( compute-inr-F')
    compute-glue-F' = compute-glue-map-AB-cocone-A-join-BC d

    path-F-inl : (a : A) → F' (inl-join a) ＝ F (inl-join a)
    path-F-inl = compute-inl-F'

    path-F-inr : (b : B) → F' (inr-join b) ＝ F (inr-join b)
    path-F-inr b = compute-inr-F' b ∙ compute-inl-J b

    compute-inl-K :
      (a : A) (b : B) →
      dependent-cogap-join
        ( dependent-cocone-K-cocone-AB-join-C e a)
        ( inl-join b) ＝
      ap F (glue-join (a , b)) ∙ inv (compute-inl-J b)
    compute-inl-K a b =
      compute-inl-dependent-cogap-join
        ( dependent-cocone-K-cocone-AB-join-C e a)
        ( b)

    coherence-F :
      (a : A) (b : B) →
      dependent-identification
        ( λ x → F' x ＝ F x)
        ( glue-join (a , b))
        ( path-F-inl a)
        ( path-F-inr b)
    coherence-F a b =
      map-compute-dependent-identification-eq-value-function
        ( F')
        ( F)
        ( p)
        ( path-F-inl a)
        ( path-F-inr b)
        ( equational-reasoning
          ap F' p ∙ path-F-inr b
          ＝ ap F' p ∙ (compute-inr-F' b ∙ linl)
            by refl
          ＝ (ap F' p ∙ compute-inr-F' b) ∙ linl
            by inv (assoc (ap F' p) (compute-inr-F' b) linl)
          ＝
            ( compute-inl-F' a ∙
              dependent-cogap-join
                ( dependent-cocone-K-cocone-AB-join-C e a)
                ( inl-join b)) ∙ linl
            by ap (_∙ linl) (compute-glue-F' (a , b))
          ＝ (compute-inl-F' a ∙ (ap F p ∙ inv linl)) ∙ linl
            by ap (λ q → (compute-inl-F' a ∙ q) ∙ linl) (compute-inl-K a b)
          ＝ compute-inl-F' a ∙ ((ap F p ∙ inv linl) ∙ linl)
            by assoc (compute-inl-F' a) (ap F p ∙ inv linl) linl
          ＝ compute-inl-F' a ∙ (ap F p ∙ (inv linl ∙ linl))
            by ap (compute-inl-F' a ∙_) (assoc (ap F p) (inv linl) linl)
          ＝ compute-inl-F' a ∙ (ap F p ∙ refl)
            by ap (λ q → compute-inl-F' a ∙ (ap F p ∙ q)) (left-inv linl)
          ＝ compute-inl-F' a ∙ ap F p
            by ap (compute-inl-F' a ∙_) right-unit
          ＝ path-F-inl a ∙ ap F p
            by refl)
      where
      p = glue-join (a , b)
      linl = compute-inl-J b

    dependent-cocone-F :
      dependent-cocone pr1 pr2 cocone-join
        ( λ x → F' x ＝ F x)
    pr1 dependent-cocone-F = path-F-inl
    pr1 (pr2 dependent-cocone-F) = path-F-inr
    pr2 (pr2 dependent-cocone-F) (a , b) = coherence-F a b

  horizontal-htpy-section-cocone-A-join-BC-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} (e : cocone-AB-join-C X) →
    pr1
      ( cocone-AB-join-C-cocone-A-join-BC
      ( cocone-A-join-BC-cocone-AB-join-C e)) ~
    pr1 e
  horizontal-htpy-section-cocone-A-join-BC-cocone-AB-join-C e =
    dependent-cogap-join
      ( dependent-cocone-horizontal-htpy-section-cocone-A-join-BC-cocone-AB-join-C
    e)

  compute-inl-coherence-htpy-section-tail-cocone-A-join-BC-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} (e : cocone-AB-join-C X) →
    (a : A) (c : C) →
    path-inl-dependent-cocone-H-cocone-A-join-BC
      ( cocone-A-join-BC-cocone-AB-join-C e)
      ( c)
      ( a) ∙
    compute-inr-map-BC-cocone-AB-join-C e c ＝
    horizontal-htpy-section-cocone-A-join-BC-cocone-AB-join-C e
      ( inl-join a) ∙
    coherence-square-cocone pr1 pr2 e (inl-join a , c)
  compute-inl-coherence-htpy-section-tail-cocone-A-join-BC-cocone-AB-join-C
    e@(F , G , H) a c =
    equational-reasoning
      path-inl-dependent-cocone-H-cocone-A-join-BC d c a ∙ v
      ＝ (α ∙ dependent-cogap-join
          ( dependent-cocone-K-cocone-AB-join-C e a)
          ( inr-join c)) ∙ v
        by refl
      ＝ (α ∙ (H (inl-join a , c) ∙ inv v)) ∙ v
        by ap (λ q → (α ∙ q) ∙ v) compute-inr-K
      ＝ α ∙ ((H (inl-join a , c) ∙ inv v) ∙ v)
        by assoc α (H (inl-join a , c) ∙ inv v) v
      ＝ α ∙ (H (inl-join a , c) ∙ (inv v ∙ v))
        by ap (α ∙_) (assoc (H (inl-join a , c)) (inv v) v)
      ＝ α ∙ (H (inl-join a , c) ∙ refl)
        by ap (λ q → α ∙ (H (inl-join a , c) ∙ q)) (left-inv v)
      ＝ α ∙ H (inl-join a , c)
        by ap (α ∙_) right-unit
      ＝ hF (inl-join a) ∙ H (inl-join a , c)
        by ap (_∙ H (inl-join a , c)) (inv compute-inl-hF)
    where
    d : cocone-A-join-BC _
    d = cocone-A-join-BC-cocone-AB-join-C e

    v = compute-inr-map-BC-cocone-AB-join-C e c

    α = compute-inl-map-AB-cocone-A-join-BC d a

    hF =
      horizontal-htpy-section-cocone-A-join-BC-cocone-AB-join-C e

    compute-inr-K =
      compute-inr-dependent-cogap-join
        ( dependent-cocone-K-cocone-AB-join-C e a)
        ( c)

    compute-inl-hF =
      compute-inl-dependent-cogap-join
        ( dependent-cocone-horizontal-htpy-section-cocone-A-join-BC-cocone-AB-join-C
          e)
        ( a)

  compute-inl-coherence-htpy-section-cocone-A-join-BC-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} (e : cocone-AB-join-C X) →
    (a : A) (c : C) →
    pr2
      ( pr2
        ( cocone-AB-join-C-cocone-A-join-BC
          ( cocone-A-join-BC-cocone-AB-join-C e)))
      ( inl-join a , c) ∙
    vertical-htpy-section-cocone-A-join-BC-cocone-AB-join-C e c ＝
    horizontal-htpy-section-cocone-A-join-BC-cocone-AB-join-C e
      ( inl-join a) ∙
    coherence-square-cocone pr1 pr2 e (inl-join a , c)
  compute-inl-coherence-htpy-section-cocone-A-join-BC-cocone-AB-join-C
    e@(F , G , H) a c =
    ap (_∙ v) compute-inl-H' ∙
    compute-inl-coherence-htpy-section-tail-cocone-A-join-BC-cocone-AB-join-C
      e a c
    where
    d : cocone-A-join-BC _
    d = cocone-A-join-BC-cocone-AB-join-C e

    H' : (x : A * B) → map-AB-cocone-A-join-BC d x ＝
      map-BC-cocone-AB-join-C e (inr-join c)
    H' x =
      dependent-cogap-join
        ( dependent-cocone-H-cocone-A-join-BC d c)
        ( x)

    v = compute-inr-map-BC-cocone-AB-join-C e c

    compute-inl-H' =
      compute-inl-dependent-cogap-join
        ( dependent-cocone-H-cocone-A-join-BC d c)
        ( a)

  compute-inr-coherence-htpy-section-tail-cocone-A-join-BC-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} (e : cocone-AB-join-C X) →
    (b : B) (c : C) →
    path-inr-dependent-cocone-H-cocone-A-join-BC
      ( cocone-A-join-BC-cocone-AB-join-C e)
      ( c)
      ( b) ∙
    compute-inr-map-BC-cocone-AB-join-C e c ＝
    horizontal-htpy-section-cocone-A-join-BC-cocone-AB-join-C e
      ( inr-join b) ∙
    coherence-square-cocone pr1 pr2 e (inr-join b , c)
  compute-inr-coherence-htpy-section-tail-cocone-A-join-BC-cocone-AB-join-C
    e@(F , G , H) b c =
    equational-reasoning
      path-inr-dependent-cocone-H-cocone-A-join-BC d c b ∙ v
      ＝ (β ∙ ap J p) ∙ v
        by refl
      ＝ β ∙ (ap J p ∙ v)
        by assoc β (ap J p) v
      ＝ β ∙ (linl ∙ H (inr-join b , c))
        by ap (β ∙_) (compute-glue-map-BC-cocone-AB-join-C e (b , c))
      ＝ (β ∙ linl) ∙ H (inr-join b , c)
        by inv (assoc β linl (H (inr-join b , c)))
      ＝ hF (inr-join b) ∙ H (inr-join b , c)
        by ap (_∙ H (inr-join b , c)) (inv compute-inr-hF)
    where
    d : cocone-A-join-BC _
    d = cocone-A-join-BC-cocone-AB-join-C e

    J : B * C → _
    J = map-BC-cocone-AB-join-C e

    p = glue-join (b , c)

    v = compute-inr-map-BC-cocone-AB-join-C e c

    linl = compute-inl-map-BC-cocone-AB-join-C e b

    β = compute-inr-map-AB-cocone-A-join-BC d b

    hF =
      horizontal-htpy-section-cocone-A-join-BC-cocone-AB-join-C e

    compute-inr-hF =
      compute-inr-dependent-cogap-join
        ( dependent-cocone-horizontal-htpy-section-cocone-A-join-BC-cocone-AB-join-C
          e)
        ( b)

  compute-inr-coherence-htpy-section-cocone-A-join-BC-cocone-AB-join-C :
    {l4 : Level} {X : UU l4} (e : cocone-AB-join-C X) →
    (b : B) (c : C) →
    pr2
      ( pr2
        ( cocone-AB-join-C-cocone-A-join-BC
          ( cocone-A-join-BC-cocone-AB-join-C e)))
      ( inr-join b , c) ∙
    vertical-htpy-section-cocone-A-join-BC-cocone-AB-join-C e c ＝
    horizontal-htpy-section-cocone-A-join-BC-cocone-AB-join-C e
      ( inr-join b) ∙
    coherence-square-cocone pr1 pr2 e (inr-join b , c)
  compute-inr-coherence-htpy-section-cocone-A-join-BC-cocone-AB-join-C
    e@(F , G , H) b c =
    ap (_∙ v) compute-inr-H' ∙
    compute-inr-coherence-htpy-section-tail-cocone-A-join-BC-cocone-AB-join-C
      e b c
    where
    d : cocone-A-join-BC _
    d = cocone-A-join-BC-cocone-AB-join-C e

    H' : (x : A * B) → map-AB-cocone-A-join-BC d x ＝
      map-BC-cocone-AB-join-C e (inr-join c)
    H' x =
      dependent-cogap-join
        ( dependent-cocone-H-cocone-A-join-BC d c)
        ( x)

    v = compute-inr-map-BC-cocone-AB-join-C e c

    compute-inr-H' =
      compute-inr-dependent-cogap-join
        ( dependent-cocone-H-cocone-A-join-BC d c)
        ( b)

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

  coherence-map-inv-map-associative-join :
    ( (x : A * B) (c : C) →
      triangle-family-map-inv-coherence-map-associative-join x c) →
    (x : A * B) (c : C) →
    dependent-identification
      ( λ z → map-inv-associative-join (map-associative-join z) ＝ z)
      ( glue-join (x , c))
      ( compute-inl-map-inv-map-associative-join x)
      ( compute-inr-map-inv-map-associative-join c)
  coherence-map-inv-map-associative-join H x c =
    map-compute-dependent-identification-eq-value-function
      ( map-inv-associative-join ∘ map-associative-join)
      ( id)
      ( p)
      ( compute-inl-map-inv-map-associative-join x)
      ( compute-inr-map-inv-map-associative-join c)
      ( equational-reasoning
        ap (map-inv-associative-join ∘ map-associative-join) p ∙ qr
        ＝ ap map-inv-associative-join (ap map-associative-join p) ∙ qr
          by ap (_∙ qr)
            ( ap-comp map-inv-associative-join map-associative-join p)
        ＝ ap map-inv-associative-join (ap map-associative-join p) ∙
            ((ap map-inv-associative-join ainr ∙ finr) ∙ rinr)
          by refl
        ＝ ( ap map-inv-associative-join (ap map-associative-join p) ∙
            ( ap map-inv-associative-join ainr ∙ finr)) ∙
            rinr
          by inv
            ( assoc
              ( ap map-inv-associative-join (ap map-associative-join p))
              ( ap map-inv-associative-join ainr ∙ finr)
              ( rinr))
        ＝ ( ( ap map-inv-associative-join (ap map-associative-join p) ∙
              ap map-inv-associative-join ainr) ∙
            finr) ∙
            rinr
          by ap (_∙ rinr)
            ( inv
              ( assoc
                ( ap map-inv-associative-join (ap map-associative-join p))
                ( ap map-inv-associative-join ainr)
                ( finr)))
        ＝ ( ap map-inv-associative-join
            ( ap map-associative-join p ∙ ainr) ∙
            finr) ∙
            rinr
          by ap (λ q → (q ∙ finr) ∙ rinr)
            ( inv
              ( ap-concat
                ( map-inv-associative-join)
                ( ap map-associative-join p)
                ( ainr)))
        ＝ ( ap map-inv-associative-join (ainl ∙ coh) ∙ finr) ∙
            rinr
          by ap (λ q → (ap map-inv-associative-join q ∙ finr) ∙ rinr)
            ( compute-glue-map-associative-join (x , c))
        ＝ ((ap map-inv-associative-join ainl ∙
            ap map-inv-associative-join coh) ∙
            finr) ∙
            rinr
          by ap (_∙ rinr)
            ( ap (_∙ finr)
              ( ap-concat map-inv-associative-join ainl coh))
        ＝ ( ap map-inv-associative-join ainl ∙
            ( ap map-inv-associative-join coh ∙ finr)) ∙
            rinr
          by ap (_∙ rinr)
            ( assoc
              ( ap map-inv-associative-join ainl)
              ( ap map-inv-associative-join coh)
              ( finr))
        ＝ ap map-inv-associative-join ainl ∙
            ((ap map-inv-associative-join coh ∙ finr) ∙ rinr)
          by assoc
            ( ap map-inv-associative-join ainl)
            ( ap map-inv-associative-join coh ∙ finr)
            ( rinr)
        ＝ ap map-inv-associative-join ainl ∙
            (ap map-inv-associative-join coh ∙ (finr ∙ rinr))
          by ap (ap map-inv-associative-join ainl ∙_)
            ( assoc (ap map-inv-associative-join coh) finr rinr)
        ＝ ap map-inv-associative-join ainl ∙ (linv ∙ ap id p)
          by ap (ap map-inv-associative-join ainl ∙_) (H x c)
        ＝ (ap map-inv-associative-join ainl ∙ linv) ∙ ap id p
          by inv (assoc (ap map-inv-associative-join ainl) linv (ap id p)))
    where
    p = glue-join (x , c)
    ainl = compute-inl-map-associative-join x
    ainr = compute-inr-map-associative-join c
    coh = coherence-map-associative-join x c
    linv = compute-map-inv-map-left-associative-join x
    finr = compute-inr-map-inv-associative-join (inr-join c)
    rinr = compute-inr-map-right-associative-join c
    qr = compute-inr-map-inv-map-associative-join c

  dependent-cocone-map-inv-map-associative-join :
    ( (x : A * B) (c : C) →
      triangle-family-map-inv-coherence-map-associative-join x c) →
    dependent-cocone pr1 pr2 cocone-join
      ( λ z → map-inv-associative-join (map-associative-join z) ＝ z)
  pr1 (dependent-cocone-map-inv-map-associative-join H) =
    compute-inl-map-inv-map-associative-join
  pr1 (pr2 (dependent-cocone-map-inv-map-associative-join H)) =
    compute-inr-map-inv-map-associative-join
  pr2 (pr2 (dependent-cocone-map-inv-map-associative-join H)) (x , c) =
    coherence-map-inv-map-associative-join H x c

  compute-map-inv-map-associative-join :
    ( (x : A * B) (c : C) →
      triangle-family-map-inv-coherence-map-associative-join x c) →
    map-inv-associative-join ∘ map-associative-join ~ id
  compute-map-inv-map-associative-join H =
    dependent-cogap-join (dependent-cocone-map-inv-map-associative-join H)

  coherence-triangle-map-inv-coherence-product-join :
    UU (l1 ⊔ l2 ⊔ l3)
  coherence-triangle-map-inv-coherence-product-join =
    (a : A) (b : B) (c : C) →
    dependent-identification
      ( λ z →
        triangle-family-map-inv-coherence-map-associative-join
          ( pr1 z)
          ( pr2 z))
      ( eq-pair-Σ
        { A = A * B}
        { B = λ _ → C}
        ( glue-join (a , b))
        ( tr-constant-type-family
          { A = A * B}
          { B = C}
          ( glue-join (a , b))
          ( c)))
      ( compute-inl-triangle-map-inv-coherence-map-associative-join a c)
      ( compute-inr-triangle-map-inv-coherence-map-associative-join b c)

  path-family-triangle-map-inv-coherence-product-join :
    (A * B) × C → UU (l1 ⊔ l2 ⊔ l3)
  path-family-triangle-map-inv-coherence-product-join z =
    map-inv-associative-join (map-left-associative-join (pr1 z)) ＝
    inr-join (pr2 z)

  left-path-triangle-map-inv-coherence-product-join :
    (z : (A * B) × C) →
    path-family-triangle-map-inv-coherence-product-join z
  left-path-triangle-map-inv-coherence-product-join z =
    ap map-inv-associative-join
      ( coherence-map-associative-join (pr1 z) (pr2 z)) ∙
    ( compute-inr-map-inv-associative-join (inr-join (pr2 z)) ∙
      compute-inr-map-right-associative-join (pr2 z))

  right-path-triangle-map-inv-coherence-product-join :
    (z : (A * B) × C) →
    path-family-triangle-map-inv-coherence-product-join z
  right-path-triangle-map-inv-coherence-product-join z =
    compute-map-inv-map-left-associative-join (pr1 z) ∙
    ap id (glue-join (pr1 z , pr2 z))

  coherence-square-triangle-map-inv-coherence-product-join :
    UU (l1 ⊔ l2 ⊔ l3)
  coherence-square-triangle-map-inv-coherence-product-join =
    (a : A) (b : B) (c : C) →
    apd
      ( left-path-triangle-map-inv-coherence-product-join)
      ( eq-pair-Σ
        { A = A * B}
        { B = λ _ → C}
        ( glue-join (a , b))
        ( tr-constant-type-family
          { A = A * B}
          { B = C}
          ( glue-join (a , b))
          ( c))) ∙
    compute-inr-triangle-map-inv-coherence-map-associative-join b c ＝
    ap
      ( tr
        ( path-family-triangle-map-inv-coherence-product-join)
        ( eq-pair-Σ
          { A = A * B}
          { B = λ _ → C}
          ( glue-join (a , b))
          ( tr-constant-type-family
            { A = A * B}
            { B = C}
            ( glue-join (a , b))
            ( c))))
      ( compute-inl-triangle-map-inv-coherence-map-associative-join a c) ∙
    apd
      ( right-path-triangle-map-inv-coherence-product-join)
      ( eq-pair-Σ
        { A = A * B}
        { B = λ _ → C}
        ( glue-join (a , b))
      ( tr-constant-type-family
          { A = A * B}
          { B = C}
          ( glue-join (a , b))
          ( c)))

  coherence-square-triangle-map-inv-coherence-product-join-base-path :
    {x y : A * B} (p : x ＝ y) (c : C) →
    (H0 : triangle-family-map-inv-coherence-map-associative-join x c)
    (H1 : triangle-family-map-inv-coherence-map-associative-join y c) →
    ( apd
      ( λ x → left-path-triangle-map-inv-coherence-product-join (x , c))
      ( p) ∙
      H1 ＝
      ap
        ( tr
          ( λ x →
            path-family-triangle-map-inv-coherence-product-join (x , c))
          ( p))
        ( H0) ∙
      apd
        ( λ x → right-path-triangle-map-inv-coherence-product-join (x , c))
        ( p)) →
    apd
      ( left-path-triangle-map-inv-coherence-product-join)
      ( eq-pair-Σ
        { A = A * B}
        { B = λ _ → C}
        ( p)
        ( tr-constant-type-family
          { A = A * B}
          { B = C}
          ( p)
          ( c))) ∙
    H1 ＝
    ap
      ( tr
        ( path-family-triangle-map-inv-coherence-product-join)
        ( eq-pair-Σ
          { A = A * B}
          { B = λ _ → C}
          ( p)
          ( tr-constant-type-family
            { A = A * B}
            { B = C}
            ( p)
            ( c))))
      ( H0) ∙
    apd
      ( right-path-triangle-map-inv-coherence-product-join)
      ( eq-pair-Σ
        { A = A * B}
        { B = λ _ → C}
        ( p)
        ( tr-constant-type-family
          { A = A * B}
          { B = C}
          ( p)
          ( c)))
  coherence-square-triangle-map-inv-coherence-product-join-base-path
    refl c H0 H1 H =
    H

  coherence-square-triangle-map-inv-coherence-join-at :
    (a : A) (b : B) (c : C) → UU (l1 ⊔ l2 ⊔ l3)
  coherence-square-triangle-map-inv-coherence-join-at a b c =
    apd
      ( λ x → left-path-triangle-map-inv-coherence-product-join (x , c))
      ( glue-join (a , b)) ∙
    compute-inr-triangle-map-inv-coherence-map-associative-join b c ＝
    ap
      ( tr
        ( λ x →
          path-family-triangle-map-inv-coherence-product-join (x , c))
        ( glue-join (a , b)))
      ( compute-inl-triangle-map-inv-coherence-map-associative-join a c) ∙
    apd
      ( λ x → right-path-triangle-map-inv-coherence-product-join (x , c))
      ( glue-join (a , b))

  coherence-square-triangle-map-inv-coherence-join :
    UU (l1 ⊔ l2 ⊔ l3)
  coherence-square-triangle-map-inv-coherence-join =
    (a : A) (b : B) (c : C) →
    coherence-square-triangle-map-inv-coherence-join-at a b c

  coherence-square-identifications-triangle-map-inv-coherence-join :
    (a : A) (b : B) (c : C) → UU (l1 ⊔ l2 ⊔ l3)
  coherence-square-identifications-triangle-map-inv-coherence-join a b c =
    coherence-square-identifications
      ( ap
        ( tr
          ( λ x →
            path-family-triangle-map-inv-coherence-product-join (x , c))
          ( glue-join (a , b)))
        ( compute-inl-triangle-map-inv-coherence-map-associative-join a c))
      ( apd
        ( λ x → left-path-triangle-map-inv-coherence-product-join (x , c))
        ( glue-join (a , b)))
      ( apd
        ( λ x → right-path-triangle-map-inv-coherence-product-join (x , c))
        ( glue-join (a , b)))
      ( compute-inr-triangle-map-inv-coherence-map-associative-join b c)

  coherence-triangle-map-inv-coherence-product-join-coherence-square :
    coherence-square-triangle-map-inv-coherence-product-join →
    coherence-triangle-map-inv-coherence-product-join
  coherence-triangle-map-inv-coherence-product-join-coherence-square H a b c =
    map-compute-dependent-identification-eq-value
      { P =
        path-family-triangle-map-inv-coherence-product-join}
      ( left-path-triangle-map-inv-coherence-product-join)
      ( right-path-triangle-map-inv-coherence-product-join)
      ( eq-pair-Σ
        { A = A * B}
        { B = λ _ → C}
        ( glue-join (a , b))
        ( tr-constant-type-family
          { A = A * B}
          { B = C}
          ( glue-join (a , b))
          ( c)))
      ( compute-inl-triangle-map-inv-coherence-map-associative-join a c)
      ( compute-inr-triangle-map-inv-coherence-map-associative-join b c)
      ( H a b c)

  dependent-cocone-triangle-map-inv-coherence-product-join :
    coherence-triangle-map-inv-coherence-product-join →
    dependent-cocone
      ( left-map-span-product-join)
      ( right-map-span-product-join)
      ( cocone-product-join)
      ( λ z →
        triangle-family-map-inv-coherence-map-associative-join
          ( pr1 z)
          ( pr2 z))
  pr1 (dependent-cocone-triangle-map-inv-coherence-product-join H) (a , c) =
    compute-inl-triangle-map-inv-coherence-map-associative-join a c
  pr1
    ( pr2 (dependent-cocone-triangle-map-inv-coherence-product-join H))
    ( b , c) =
    compute-inr-triangle-map-inv-coherence-map-associative-join b c
  pr2
    ( pr2 (dependent-cocone-triangle-map-inv-coherence-product-join H))
    ( (a , b) , c) =
    tr
      ( λ p →
        dependent-identification
          ( λ z →
            triangle-family-map-inv-coherence-map-associative-join
              ( pr1 z)
              ( pr2 z))
          ( p)
          ( compute-inl-triangle-map-inv-coherence-map-associative-join a c)
          ( compute-inr-triangle-map-inv-coherence-map-associative-join b c))
      ( inv (compute-glue-cocone-product-join ((a , b) , c)))
      ( H a b c)

  triangle-map-inv-coherence-product-join :
    coherence-triangle-map-inv-coherence-product-join →
    (z : (A * B) × C) →
    triangle-family-map-inv-coherence-map-associative-join (pr1 z) (pr2 z)
  triangle-map-inv-coherence-product-join H =
    map-inv-is-equiv
      ( dependent-universal-property-universal-property-pushout
        ( left-map-span-product-join)
        ( right-map-span-product-join)
        ( cocone-product-join)
        ( universal-property-pushout-cocone-product-join)
        ( λ z →
          triangle-family-map-inv-coherence-map-associative-join
            ( pr1 z)
            ( pr2 z)))
      ( dependent-cocone-triangle-map-inv-coherence-product-join H)

  triangle-map-inv-coherence-map-associative-join :
    coherence-triangle-map-inv-coherence-product-join →
    (x : A * B) (c : C) →
    triangle-family-map-inv-coherence-map-associative-join x c
  triangle-map-inv-coherence-map-associative-join H x c =
    triangle-map-inv-coherence-product-join H (x , c)

  compute-map-inv-map-associative-join-product-coherence :
    coherence-triangle-map-inv-coherence-product-join →
    map-inv-associative-join ∘ map-associative-join ~ id
  compute-map-inv-map-associative-join-product-coherence H =
    compute-map-inv-map-associative-join
      ( triangle-map-inv-coherence-map-associative-join H)

  triangle-map-inv-coherence-product-join-coherence-square :
    coherence-square-triangle-map-inv-coherence-product-join →
    (z : (A * B) × C) →
    triangle-family-map-inv-coherence-map-associative-join (pr1 z) (pr2 z)
  triangle-map-inv-coherence-product-join-coherence-square H =
    triangle-map-inv-coherence-product-join
      ( coherence-triangle-map-inv-coherence-product-join-coherence-square H)

  triangle-map-inv-coherence-map-associative-join-coherence-square :
    coherence-square-triangle-map-inv-coherence-product-join →
    (x : A * B) (c : C) →
    triangle-family-map-inv-coherence-map-associative-join x c
  triangle-map-inv-coherence-map-associative-join-coherence-square H x c =
    triangle-map-inv-coherence-product-join-coherence-square H (x , c)

  compute-map-inv-map-associative-join-product-coherence-square :
    coherence-square-triangle-map-inv-coherence-product-join →
    map-inv-associative-join ∘ map-associative-join ~ id
  compute-map-inv-map-associative-join-product-coherence-square H =
    compute-map-inv-map-associative-join
      ( triangle-map-inv-coherence-map-associative-join-coherence-square H)

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

  coherence-map-associative-map-inv-associative-join :
    ( (a : A) (y : B * C) →
      triangle-family-map-associative-coherence-map-inv-associative-join a y) →
    (a : A) (y : B * C) →
    dependent-identification
      ( λ z → map-associative-join (map-inv-associative-join z) ＝ z)
      ( glue-join (a , y))
      ( compute-inl-map-associative-map-inv-associative-join a)
      ( compute-inr-map-associative-map-inv-associative-join y)
  coherence-map-associative-map-inv-associative-join H a y =
    map-compute-dependent-identification-eq-value-function
      ( map-associative-join ∘ map-inv-associative-join)
      ( id)
      ( p)
      ( compute-inl-map-associative-map-inv-associative-join a)
      ( compute-inr-map-associative-map-inv-associative-join y)
      ( equational-reasoning
        ap (map-associative-join ∘ map-inv-associative-join) p ∙ qr
        ＝ ap map-associative-join (ap map-inv-associative-join p) ∙ qr
          by ap (_∙ qr)
            ( ap-comp map-associative-join map-inv-associative-join p)
        ＝ ap map-associative-join (ap map-inv-associative-join p) ∙
            ( ap map-associative-join finr ∙ Hr)
          by refl
        ＝ ( ap map-associative-join (ap map-inv-associative-join p) ∙
            ap map-associative-join finr) ∙
            Hr
          by inv
            ( assoc
              ( ap map-associative-join (ap map-inv-associative-join p))
              ( ap map-associative-join finr)
              ( Hr))
        ＝ ap map-associative-join (ap map-inv-associative-join p ∙ finr) ∙
            Hr
          by ap (_∙ Hr)
            ( inv
              ( ap-concat
                ( map-associative-join)
                ( ap map-inv-associative-join p)
                ( finr)))
        ＝ ap map-associative-join (finl ∙ coh) ∙ Hr
          by ap (λ q → ap map-associative-join q ∙ Hr)
            ( compute-glue-map-inv-associative-join (a , y))
        ＝ (ap map-associative-join finl ∙ ap map-associative-join coh) ∙
            Hr
          by ap (_∙ Hr) (ap-concat map-associative-join finl coh)
        ＝ ap map-associative-join finl ∙
            (ap map-associative-join coh ∙ Hr)
          by assoc
            ( ap map-associative-join finl)
            ( ap map-associative-join coh)
            ( Hr)
        ＝ ap map-associative-join finl ∙ ((ainl ∙ linl) ∙ ap id p)
          by ap (ap map-associative-join finl ∙_) (H a y)
        ＝ (ap map-associative-join finl ∙ (ainl ∙ linl)) ∙ ap id p
          by inv (assoc (ap map-associative-join finl) (ainl ∙ linl) (ap id p))
        ＝ ((ap map-associative-join finl ∙ ainl) ∙ linl) ∙ ap id p
          by ap (_∙ ap id p)
            ( inv (assoc (ap map-associative-join finl) ainl linl)))
    where
    p = glue-join (a , y)
    finl = compute-inl-map-inv-associative-join a
    finr = compute-inr-map-inv-associative-join y
    coh = coherence-map-inv-associative-join a y
    Hr = compute-map-associative-map-right-associative-join y
    ainl = compute-inl-map-associative-join (inl-join a)
    linl = compute-inl-map-left-associative-join a
    qr = compute-inr-map-associative-map-inv-associative-join y

  dependent-cocone-map-associative-map-inv-associative-join :
    ( (a : A) (y : B * C) →
      triangle-family-map-associative-coherence-map-inv-associative-join a y) →
    dependent-cocone pr1 pr2 cocone-join
      ( λ z → map-associative-join (map-inv-associative-join z) ＝ z)
  pr1 (dependent-cocone-map-associative-map-inv-associative-join H) =
    compute-inl-map-associative-map-inv-associative-join
  pr1 (pr2 (dependent-cocone-map-associative-map-inv-associative-join H)) =
    compute-inr-map-associative-map-inv-associative-join
  pr2 (pr2 (dependent-cocone-map-associative-map-inv-associative-join H)) (a , y) =
    coherence-map-associative-map-inv-associative-join H a y

  compute-map-associative-map-inv-associative-join :
    ( (a : A) (y : B * C) →
      triangle-family-map-associative-coherence-map-inv-associative-join a y) →
    map-associative-join ∘ map-inv-associative-join ~ id
  compute-map-associative-map-inv-associative-join H =
    dependent-cogap-join
      ( dependent-cocone-map-associative-map-inv-associative-join H)

  coherence-triangle-map-associative-coherence-left-product-join :
    UU (l1 ⊔ l2 ⊔ l3)
  coherence-triangle-map-associative-coherence-left-product-join =
    (a : A) (b : B) (c : C) →
    dependent-identification
      ( λ z →
        triangle-family-map-associative-coherence-map-inv-associative-join
          ( pr1 z)
          ( pr2 z))
      ( eq-pair-Σ
        { A = A}
        { B = λ _ → B * C}
        ( refl)
        ( glue-join (b , c)))
      ( compute-inl-triangle-map-associative-coherence-map-inv-associative-join
        a b)
      ( compute-inr-triangle-map-associative-coherence-map-inv-associative-join
        a c)

  path-family-triangle-map-associative-coherence-left-product-join :
    A × (B * C) → UU (l1 ⊔ l2 ⊔ l3)
  path-family-triangle-map-associative-coherence-left-product-join z =
    map-associative-join (inl-join (inl-join (pr1 z))) ＝
    inr-join (pr2 z)

  left-path-triangle-map-associative-coherence-left-product-join :
    (z : A × (B * C)) →
    path-family-triangle-map-associative-coherence-left-product-join z
  left-path-triangle-map-associative-coherence-left-product-join z =
    ap map-associative-join
      ( coherence-map-inv-associative-join (pr1 z) (pr2 z)) ∙
    compute-map-associative-map-right-associative-join (pr2 z)

  right-path-triangle-map-associative-coherence-left-product-join :
    (z : A × (B * C)) →
    path-family-triangle-map-associative-coherence-left-product-join z
  right-path-triangle-map-associative-coherence-left-product-join z =
    ( compute-inl-map-associative-join (inl-join (pr1 z)) ∙
      compute-inl-map-left-associative-join (pr1 z)) ∙
    ap id (glue-join (pr1 z , pr2 z))

  coherence-square-triangle-map-associative-coherence-left-product-join :
    UU (l1 ⊔ l2 ⊔ l3)
  coherence-square-triangle-map-associative-coherence-left-product-join =
    (a : A) (b : B) (c : C) →
    apd
      ( left-path-triangle-map-associative-coherence-left-product-join)
      ( eq-pair-Σ
        { A = A}
        { B = λ _ → B * C}
        ( refl)
        ( glue-join (b , c))) ∙
    compute-inr-triangle-map-associative-coherence-map-inv-associative-join
      a c ＝
    ap
      ( tr
        ( path-family-triangle-map-associative-coherence-left-product-join)
        ( eq-pair-Σ
          { A = A}
          { B = λ _ → B * C}
          ( refl)
          ( glue-join (b , c))))
      ( compute-inl-triangle-map-associative-coherence-map-inv-associative-join
        a b) ∙
    apd
      ( right-path-triangle-map-associative-coherence-left-product-join)
      ( eq-pair-Σ
        { A = A}
        { B = λ _ → B * C}
        ( refl)
        ( glue-join (b , c)))

  coherence-triangle-map-associative-coherence-left-product-join-coherence-square :
    coherence-square-triangle-map-associative-coherence-left-product-join →
    coherence-triangle-map-associative-coherence-left-product-join
  coherence-triangle-map-associative-coherence-left-product-join-coherence-square
    H a b c =
    map-compute-dependent-identification-eq-value
      { P =
        path-family-triangle-map-associative-coherence-left-product-join}
      ( left-path-triangle-map-associative-coherence-left-product-join)
      ( right-path-triangle-map-associative-coherence-left-product-join)
      ( eq-pair-Σ
        { A = A}
        { B = λ _ → B * C}
        ( refl)
        ( glue-join (b , c)))
      ( compute-inl-triangle-map-associative-coherence-map-inv-associative-join
        a b)
      ( compute-inr-triangle-map-associative-coherence-map-inv-associative-join
        a c)
      ( H a b c)

  dependent-cocone-triangle-map-associative-coherence-left-product-join :
    coherence-triangle-map-associative-coherence-left-product-join →
    dependent-cocone
      ( left-map-span-left-product-join)
      ( right-map-span-left-product-join)
      ( cocone-left-product-join')
      ( λ z →
        triangle-family-map-associative-coherence-map-inv-associative-join
          ( pr1 z)
          ( pr2 z))
  pr1
    ( dependent-cocone-triangle-map-associative-coherence-left-product-join H)
    ( a , b) =
    compute-inl-triangle-map-associative-coherence-map-inv-associative-join a b
  pr1
    ( pr2
      ( dependent-cocone-triangle-map-associative-coherence-left-product-join H))
    ( a , c) =
    compute-inr-triangle-map-associative-coherence-map-inv-associative-join a c
  pr2
    ( pr2
      ( dependent-cocone-triangle-map-associative-coherence-left-product-join H))
    ( a , b , c) =
    tr
      ( λ p →
        dependent-identification
          ( λ z →
            triangle-family-map-associative-coherence-map-inv-associative-join
              ( pr1 z)
              ( pr2 z))
          ( p)
          ( compute-inl-triangle-map-associative-coherence-map-inv-associative-join
            a b)
          ( compute-inr-triangle-map-associative-coherence-map-inv-associative-join
            a c))
      ( inv (compute-glue-cocone-left-product-join' (a , b , c)))
      ( H a b c)

  triangle-map-associative-coherence-left-product-join :
    coherence-triangle-map-associative-coherence-left-product-join →
    (z : A × (B * C)) →
    triangle-family-map-associative-coherence-map-inv-associative-join
      ( pr1 z)
      ( pr2 z)
  triangle-map-associative-coherence-left-product-join H =
    map-inv-is-equiv
      ( dependent-universal-property-universal-property-pushout
        ( left-map-span-left-product-join)
        ( right-map-span-left-product-join)
        ( cocone-left-product-join')
        ( universal-property-pushout-cocone-left-product-join')
        ( λ z →
          triangle-family-map-associative-coherence-map-inv-associative-join
            ( pr1 z)
            ( pr2 z)))
      ( dependent-cocone-triangle-map-associative-coherence-left-product-join H)

  triangle-map-associative-coherence-map-inv-associative-join :
    coherence-triangle-map-associative-coherence-left-product-join →
    (a : A) (y : B * C) →
    triangle-family-map-associative-coherence-map-inv-associative-join a y
  triangle-map-associative-coherence-map-inv-associative-join H a y =
    triangle-map-associative-coherence-left-product-join H (a , y)

  compute-map-associative-map-inv-associative-join-left-product-coherence :
    coherence-triangle-map-associative-coherence-left-product-join →
    map-associative-join ∘ map-inv-associative-join ~ id
  compute-map-associative-map-inv-associative-join-left-product-coherence H =
    compute-map-associative-map-inv-associative-join
      ( triangle-map-associative-coherence-map-inv-associative-join H)

  triangle-map-associative-coherence-left-product-join-coherence-square :
    coherence-square-triangle-map-associative-coherence-left-product-join →
    (z : A × (B * C)) →
    triangle-family-map-associative-coherence-map-inv-associative-join
      ( pr1 z)
      ( pr2 z)
  triangle-map-associative-coherence-left-product-join-coherence-square H =
    triangle-map-associative-coherence-left-product-join
      ( coherence-triangle-map-associative-coherence-left-product-join-coherence-square
        H)

  triangle-map-associative-coherence-map-inv-associative-join-coherence-square :
    coherence-square-triangle-map-associative-coherence-left-product-join →
    (a : A) (y : B * C) →
    triangle-family-map-associative-coherence-map-inv-associative-join a y
  triangle-map-associative-coherence-map-inv-associative-join-coherence-square
    H a y =
    triangle-map-associative-coherence-left-product-join-coherence-square
      H (a , y)

  compute-map-associative-map-inv-associative-join-left-product-coherence-square :
    coherence-square-triangle-map-associative-coherence-left-product-join →
    map-associative-join ∘ map-inv-associative-join ~ id
  compute-map-associative-map-inv-associative-join-left-product-coherence-square
    H =
    compute-map-associative-map-inv-associative-join
      ( triangle-map-associative-coherence-map-inv-associative-join-coherence-square
        H)

  is-equiv-map-associative-join-coherence-squares :
    coherence-square-triangle-map-inv-coherence-product-join →
    coherence-square-triangle-map-associative-coherence-left-product-join →
    is-equiv map-associative-join
  is-equiv-map-associative-join-coherence-squares H K =
    is-equiv-is-invertible
      ( map-inv-associative-join)
      ( compute-map-associative-map-inv-associative-join-left-product-coherence-square
        K)
      ( compute-map-inv-map-associative-join-product-coherence-square H)

  equiv-associative-join-coherence-squares :
    coherence-square-triangle-map-inv-coherence-product-join →
    coherence-square-triangle-map-associative-coherence-left-product-join →
    ((A * B) * C) ≃ (A * (B * C))
  pr1 (equiv-associative-join-coherence-squares H K) =
    map-associative-join
  pr2 (equiv-associative-join-coherence-squares H K) =
    is-equiv-map-associative-join-coherence-squares H K

```
