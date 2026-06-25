# Blakers-Massey for span pushouts

```agda
module synthetic-homotopy-theory.blakers-massey-span-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-truncation
open import foundation.identity-types
open import foundation.iterated-successors-truncation-levels
open import foundation.transport-along-identifications
open import foundation.truncation-equivalences
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.universe-levels

open import synthetic-homotopy-theory.connectivity-joins-of-types
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.span-pushouts
```

</details>

## Idea

For a relation `Q : X → Y → 𝒰`, the generalized Blakers-Massey theorem for the
span pushout reduces to a pointwise theorem about the glue maps

```text
  Q x y → inl x ＝ inr y.
```

The core connectedness hypothesis in the ABFJ/Favonia-Finster-Licata-Lumsdaine
and Coq-HoTT code-family proof says that certain joins of path spaces in the
row and column total spaces of `Q` are connected. This file records the reusable
derivation of that hypothesis from row and column connectedness.

## Row and column total spaces

```agda
is-connected-map-pr1-is-connected-fam :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
  ((a : A) → is-connected k (B a)) → is-connected-map k (pr1 {B = B})
is-connected-map-pr1-is-connected-fam k H a =
  is-connected-equiv (equiv-fiber-pr1 _ a) (H a)

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Q : X → Y → UU l3)
  where

  row-total-space-span-pushout : X → UU (l2 ⊔ l3)
  row-total-space-span-pushout x = Σ Y (Q x)

  column-total-space-span-pushout : Y → UU (l1 ⊔ l3)
  column-total-space-span-pushout y = Σ X (λ x → Q x y)
```

## The connected join hypothesis

```agda
  connected-join-hypothesis-span-pushout : 𝕋 → UU (l1 ⊔ l2 ⊔ l3)
  connected-join-hypothesis-span-pushout m =
    (x1 x3 : X) (y2 y4 : Y)
    (q12 : Q x1 y2) (q32 : Q x3 y2) (q34 : Q x3 y4) →
    is-connected
      ( m)
      ( ( (x1 , q12) ＝ (x3 , q32)) *
        ( (y2 , q32) ＝ (y4 , q34)))

  is-connected-join-paths-span-pushout :
    (k n : 𝕋) →
    ((x : X) → is-connected (succ-𝕋 k) (row-total-space-span-pushout x)) →
    ((y : Y) → is-connected (succ-𝕋 n) (column-total-space-span-pushout y)) →
    connected-join-hypothesis-span-pushout (add+2-𝕋 n k)
  is-connected-join-paths-span-pushout
    k n row-connected column-connected x1 x3 y2 y4 q12 q32 q34 =
    is-connected-join-is-connected
      ( n)
      ( k)
      ( is-connected-eq-is-connected (column-connected y2))
      ( is-connected-eq-is-connected (row-connected x3))
```

## The code families for the pointwise theorem

```agda
  code-right-span-pushout :
    (m : 𝕋) (x0 : X) (y : Y) →
    inl-span-pushout Q x0 ＝ inr-span-pushout Q y → UU (l1 ⊔ l2 ⊔ l3)
  code-right-span-pushout m x0 y r =
    type-trunc m (fiber (glue-span-pushout Q x0 y) r)

  is-contr-code-right-span-pushout-is-connected-map-glue-span-pushout :
    (m : 𝕋) →
    ((x : X) (y : Y) → is-connected-map m (glue-span-pushout Q x y)) →
    (x : X) (y : Y) (r : inl-span-pushout Q x ＝ inr-span-pushout Q y) →
    is-contr (code-right-span-pushout m x y r)
  is-contr-code-right-span-pushout-is-connected-map-glue-span-pushout
    m H x y r =
    H x y r

  is-connected-map-glue-span-pushout-is-contr-code-right-span-pushout :
    (m : 𝕋) →
    ( (x : X) (y : Y) (r : inl-span-pushout Q x ＝ inr-span-pushout Q y) →
      is-contr (code-right-span-pushout m x y r)) →
    (x : X) (y : Y) → is-connected-map m (glue-span-pushout Q x y)
  is-connected-map-glue-span-pushout-is-contr-code-right-span-pushout
    m H x y r =
    H x y r

  code-left-1-span-pushout :
    (x0 x1 : X) →
    inl-span-pushout Q x0 ＝ inl-span-pushout Q x1 →
    UU (l1 ⊔ l2 ⊔ l3)
  code-left-1-span-pushout x0 x1 r =
    Σ (x0 ＝ x1) (λ s → ap (inl-span-pushout Q) s ＝ r)

  code-left-2-span-pushout :
    (x0 x1 : X) →
    inl-span-pushout Q x0 ＝ inl-span-pushout Q x1 →
    UU (l1 ⊔ l2 ⊔ l3)
  code-left-2-span-pushout x0 x1 r =
    Σ Y
      ( λ y0 →
        Σ (Q x0 y0)
          ( λ q00 →
            Σ (Q x1 y0)
              ( λ q10 →
                glue-span-pushout Q x0 y0 q00 ∙
                inv (glue-span-pushout Q x1 y0 q10) ＝ r)))

  y-code-left-2-span-pushout :
    {x0 x1 : X} {r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1} →
    code-left-2-span-pushout x0 x1 r → Y
  y-code-left-2-span-pushout = pr1

  q00-code-left-2-span-pushout :
    {x0 x1 : X} {r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1}
    (c : code-left-2-span-pushout x0 x1 r) →
    Q x0 (y-code-left-2-span-pushout c)
  q00-code-left-2-span-pushout c = pr1 (pr2 c)

  q10-code-left-2-span-pushout :
    {x0 x1 : X} {r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1}
    (c : code-left-2-span-pushout x0 x1 r) →
    Q x1 (y-code-left-2-span-pushout c)
  q10-code-left-2-span-pushout c = pr1 (pr2 (pr2 c))

  code-left-2-with-join-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1) →
    inl-span-pushout Q x0 ＝ inl-span-pushout Q x1 →
    UU (l1 ⊔ l2 ⊔ l3)
  code-left-2-with-join-span-pushout x0 x1 y1 q11 r =
    Σ (code-left-2-span-pushout x0 x1 r)
      ( λ c →
        ( _＝_
          { A = column-total-space-span-pushout
                  ( y-code-left-2-span-pushout c)}
          ( x0 , q00-code-left-2-span-pushout c)
          ( x1 , q10-code-left-2-span-pushout c)) *
        ( _＝_
          { A = row-total-space-span-pushout x1}
          ( y-code-left-2-span-pushout c , q10-code-left-2-span-pushout c)
          ( y1 , q11)))

  projection-code-left-2-with-join-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-2-with-join-span-pushout x0 x1 y1 q11 r →
    code-left-2-span-pushout x0 x1 r
  projection-code-left-2-with-join-span-pushout x0 x1 y1 q11 r =
    pr1

  is-connected-map-projection-code-left-2-with-join-span-pushout :
    (m : 𝕋) →
    connected-join-hypothesis-span-pushout m →
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    is-connected-map m
      ( projection-code-left-2-with-join-span-pushout x0 x1 y1 q11 r)
  is-connected-map-projection-code-left-2-with-join-span-pushout
    m H x0 x1 y1 q11 r =
    is-connected-map-pr1-is-connected-fam
      ( m)
      ( λ c → H x0 x1 (y-code-left-2-span-pushout c) y1
        ( q00-code-left-2-span-pushout c)
        ( q10-code-left-2-span-pushout c)
        ( q11))

  is-truncation-equivalence-projection-code-left-2-with-join-span-pushout :
    (m : 𝕋) →
    connected-join-hypothesis-span-pushout m →
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    is-truncation-equivalence m
      ( projection-code-left-2-with-join-span-pushout x0 x1 y1 q11 r)
  is-truncation-equivalence-projection-code-left-2-with-join-span-pushout
    m H x0 x1 y1 q11 r =
    is-truncation-equivalence-is-connected-map
      ( projection-code-left-2-with-join-span-pushout x0 x1 y1 q11 r)
      ( is-connected-map-projection-code-left-2-with-join-span-pushout
        ( m)
        ( H)
        ( x0)
        ( x1)
        ( y1)
        ( q11)
        ( r))

  equiv-trunc-projection-code-left-2-with-join-span-pushout :
    (m : 𝕋) →
    connected-join-hypothesis-span-pushout m →
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    type-trunc m (code-left-2-with-join-span-pushout x0 x1 y1 q11 r) ≃
    type-trunc m (code-left-2-span-pushout x0 x1 r)
  pr1
    ( equiv-trunc-projection-code-left-2-with-join-span-pushout
      m H x0 x1 y1 q11 r) =
    map-trunc m
      ( projection-code-left-2-with-join-span-pushout x0 x1 y1 q11 r)
  pr2
    ( equiv-trunc-projection-code-left-2-with-join-span-pushout
      m H x0 x1 y1 q11 r) =
    is-truncation-equivalence-projection-code-left-2-with-join-span-pushout
      ( m)
      ( H)
      ( x0)
      ( x1)
      ( y1)
      ( q11)
      ( r)

  code-left-2a-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1) →
    inl-span-pushout Q x0 ＝ inl-span-pushout Q x1 →
    UU (l1 ⊔ l2 ⊔ l3)
  code-left-2a-span-pushout x0 x1 y1 q11 r =
    Σ (x0 ＝ x1)
      ( λ s →
        Σ (Q x0 y1)
          ( λ q01 →
            Σ (tr (λ x → Q x y1) s q01 ＝ q11)
              ( λ _ →
                glue-span-pushout Q x0 y1 q01 ∙
                inv (glue-span-pushout Q x1 y1 q11) ＝ r)))

  code-left-2b-span-pushout :
    (x0 x1 : X) →
    inl-span-pushout Q x0 ＝ inl-span-pushout Q x1 →
    UU (l1 ⊔ l2 ⊔ l3)
  code-left-2b-span-pushout x0 x1 r =
    Σ (x0 ＝ x1)
      ( λ s →
        Σ Y
          ( λ y0 →
            Σ (Q x0 y0)
              ( λ q00 →
                Σ (Q x1 y0)
                  ( λ q10 →
                    Σ (tr (λ x → Q x y0) s q00 ＝ q10)
                      ( λ _ →
                        glue-span-pushout Q x0 y0 q00 ∙
                        inv (glue-span-pushout Q x1 y0 q10) ＝ r)))))

  code-left-2c-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1) →
    inl-span-pushout Q x0 ＝ inl-span-pushout Q x1 →
    UU (l1 ⊔ l2 ⊔ l3)
  code-left-2c-span-pushout x0 x1 y1 q11 r =
    Σ (Q x0 y1)
      ( λ q01 →
        glue-span-pushout Q x0 y1 q01 ∙
        inv (glue-span-pushout Q x1 y1 q11) ＝ r)

  map-code-left-2a-code-left-2b-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-2a-span-pushout x0 x1 y1 q11 r →
    code-left-2b-span-pushout x0 x1 r
  map-code-left-2a-code-left-2b-span-pushout
    x0 x1 y1 q11 r (s , q01 , w , u) =
    s , y1 , q01 , q11 , w , u

  map-code-left-2a-code-left-2c-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-2a-span-pushout x0 x1 y1 q11 r →
    code-left-2c-span-pushout x0 x1 y1 q11 r
  map-code-left-2a-code-left-2c-span-pushout
    x0 x1 y1 q11 r (s , q01 , w , u) =
    q01 , u

  map-code-left-2b-code-left-2-span-pushout :
    (x0 x1 : X) (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-2b-span-pushout x0 x1 r →
    code-left-2-span-pushout x0 x1 r
  map-code-left-2b-code-left-2-span-pushout
    x0 x1 r (s , y0 , q00 , q10 , w , u) =
    y0 , q00 , q10 , u

  map-code-left-2c-code-left-2-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-2c-span-pushout x0 x1 y1 q11 r →
    code-left-2-span-pushout x0 x1 r
  map-code-left-2c-code-left-2-span-pushout
    x0 x1 y1 q11 r (q01 , u) =
    y1 , q01 , q11 , u

  map-code-left-2b-code-left-2-with-join-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-2b-span-pushout x0 x1 r →
    code-left-2-with-join-span-pushout x0 x1 y1 q11 r
  map-code-left-2b-code-left-2-with-join-span-pushout
    x0 x1 y1 q11 r (s , y0 , q00 , q10 , w , u) =
    ( y0 , q00 , q10 , u) ,
    inl-join (eq-pair-Σ s w)

  map-code-left-2c-code-left-2-with-join-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-2c-span-pushout x0 x1 y1 q11 r →
    code-left-2-with-join-span-pushout x0 x1 y1 q11 r
  map-code-left-2c-code-left-2-with-join-span-pushout
    x0 x1 y1 q11 r (q01 , u) =
    ( y1 , q01 , q11 , u) ,
    inr-join refl

  code-left-2-decomposition-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1) →
    inl-span-pushout Q x0 ＝ inl-span-pushout Q x1 →
    UU (l1 ⊔ l2 ⊔ l3)
  code-left-2-decomposition-span-pushout x0 x1 y1 q11 r =
    pushout
      ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)

  map-code-left-2-decomposition-code-left-2-with-join-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-2-decomposition-span-pushout x0 x1 y1 q11 r →
    code-left-2-with-join-span-pushout x0 x1 y1 q11 r
  map-code-left-2-decomposition-code-left-2-with-join-span-pushout
    x0 x1 y1 q11 r =
    cogap
      ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2b-code-left-2-with-join-span-pushout x0 x1 y1 q11 r ,
        map-code-left-2c-code-left-2-with-join-span-pushout x0 x1 y1 q11 r ,
        λ { (s , q01 , w , u) →
          eq-pair-Σ refl (glue-join (eq-pair-Σ s w , refl))})

  compute-inl-map-code-left-2-decomposition-code-left-2-with-join-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (b : code-left-2b-span-pushout x0 x1 r) →
    map-code-left-2-decomposition-code-left-2-with-join-span-pushout
      x0 x1 y1 q11 r
      ( inl-pushout
        ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
        ( b)) ＝
    map-code-left-2b-code-left-2-with-join-span-pushout x0 x1 y1 q11 r b
  compute-inl-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
    x0 x1 y1 q11 r =
    compute-inl-cogap
      ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2b-code-left-2-with-join-span-pushout x0 x1 y1 q11 r ,
        map-code-left-2c-code-left-2-with-join-span-pushout x0 x1 y1 q11 r ,
        λ { (s , q01 , w , u) →
          eq-pair-Σ refl (glue-join (eq-pair-Σ s w , refl))})

  compute-inr-map-code-left-2-decomposition-code-left-2-with-join-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (c : code-left-2c-span-pushout x0 x1 y1 q11 r) →
    map-code-left-2-decomposition-code-left-2-with-join-span-pushout
      x0 x1 y1 q11 r
      ( inr-pushout
        ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
        ( c)) ＝
    map-code-left-2c-code-left-2-with-join-span-pushout x0 x1 y1 q11 r c
  compute-inr-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
    x0 x1 y1 q11 r =
    compute-inr-cogap
      ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2b-code-left-2-with-join-span-pushout x0 x1 y1 q11 r ,
        map-code-left-2c-code-left-2-with-join-span-pushout x0 x1 y1 q11 r ,
        λ { (s , q01 , w , u) →
          eq-pair-Σ refl (glue-join (eq-pair-Σ s w , refl))})

  map-column-path-code-left-2-decomposition-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (c : code-left-2-span-pushout x0 x1 r) →
    ( _＝_
      { A = column-total-space-span-pushout
              ( y-code-left-2-span-pushout c)}
      ( x0 , q00-code-left-2-span-pushout c)
      ( x1 , q10-code-left-2-span-pushout c)) →
    code-left-2-decomposition-span-pushout x0 x1 y1 q11 r
  map-column-path-code-left-2-decomposition-span-pushout
    x0 x1 y1 q11 r (y0 , q00 , q10 , u) p =
    inl-pushout
      ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
      ( pr1 (pair-eq-Σ p) ,
        y0 ,
        q00 ,
        q10 ,
        pr2 (pair-eq-Σ p) ,
        u)

  map-row-path-code-left-2-decomposition-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (c : code-left-2-span-pushout x0 x1 r) →
    ( _＝_
      { A = row-total-space-span-pushout x1}
      ( y-code-left-2-span-pushout c , q10-code-left-2-span-pushout c)
      ( y1 , q11)) →
    code-left-2-decomposition-span-pushout x0 x1 y1 q11 r
  map-row-path-code-left-2-decomposition-span-pushout
    x0 x1 .y0 .q10 r (y0 , q00 , q10 , u) refl =
    inr-pushout
      ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y0 q10 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y0 q10 r)
      ( q00 , u)

  coherence-column-row-path-code-left-2-decomposition-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (c : code-left-2-span-pushout x0 x1 r)
    (p :
      _＝_
        { A = column-total-space-span-pushout
                ( y-code-left-2-span-pushout c)}
        ( x0 , q00-code-left-2-span-pushout c)
        ( x1 , q10-code-left-2-span-pushout c))
    (q :
      _＝_
        { A = row-total-space-span-pushout x1}
        ( y-code-left-2-span-pushout c , q10-code-left-2-span-pushout c)
        ( y1 , q11)) →
    map-column-path-code-left-2-decomposition-span-pushout
      x0 x1 y1 q11 r c p ＝
    map-row-path-code-left-2-decomposition-span-pushout
      x0 x1 y1 q11 r c q
  coherence-column-row-path-code-left-2-decomposition-span-pushout
    x0 .x0 .y0 .q00 r (y0 , q00 , .q00 , u) refl refl =
    glue-pushout
      ( map-code-left-2a-code-left-2b-span-pushout x0 x0 y0 q00 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x0 y0 q00 r)
      ( refl , q00 , refl , u)

  map-code-left-2-with-join-code-left-2-decomposition-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-2-with-join-span-pushout x0 x1 y1 q11 r →
    code-left-2-decomposition-span-pushout x0 x1 y1 q11 r
  map-code-left-2-with-join-code-left-2-decomposition-span-pushout
    x0 x1 y1 q11 r (c , j) =
    cogap-join
      ( code-left-2-decomposition-span-pushout x0 x1 y1 q11 r)
      ( map-column-path-code-left-2-decomposition-span-pushout
        x0 x1 y1 q11 r c ,
        map-row-path-code-left-2-decomposition-span-pushout
        x0 x1 y1 q11 r c ,
        λ (p , q) →
          coherence-column-row-path-code-left-2-decomposition-span-pushout
            x0 x1 y1 q11 r c p q)
      ( j)

  compute-inl-map-code-left-2-with-join-code-left-2-decomposition-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (c : code-left-2-span-pushout x0 x1 r)
    (p :
      _＝_
        { A = column-total-space-span-pushout
                ( y-code-left-2-span-pushout c)}
        ( x0 , q00-code-left-2-span-pushout c)
        ( x1 , q10-code-left-2-span-pushout c)) →
    map-code-left-2-with-join-code-left-2-decomposition-span-pushout
      x0 x1 y1 q11 r
      ( c , inl-join p) ＝
    map-column-path-code-left-2-decomposition-span-pushout
      x0 x1 y1 q11 r c p
  compute-inl-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
    x0 x1 y1 q11 r c =
    compute-inl-cogap-join
      ( map-column-path-code-left-2-decomposition-span-pushout
        x0 x1 y1 q11 r c ,
        map-row-path-code-left-2-decomposition-span-pushout
        x0 x1 y1 q11 r c ,
        λ (p , q) →
          coherence-column-row-path-code-left-2-decomposition-span-pushout
            x0 x1 y1 q11 r c p q)

  compute-inr-map-code-left-2-with-join-code-left-2-decomposition-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (c : code-left-2-span-pushout x0 x1 r)
    (q :
      _＝_
        { A = row-total-space-span-pushout x1}
        ( y-code-left-2-span-pushout c , q10-code-left-2-span-pushout c)
        ( y1 , q11)) →
    map-code-left-2-with-join-code-left-2-decomposition-span-pushout
      x0 x1 y1 q11 r
      ( c , inr-join q) ＝
    map-row-path-code-left-2-decomposition-span-pushout
      x0 x1 y1 q11 r c q
  compute-inr-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
    x0 x1 y1 q11 r c =
    compute-inr-cogap-join
      ( map-column-path-code-left-2-decomposition-span-pushout
        x0 x1 y1 q11 r c ,
        map-row-path-code-left-2-decomposition-span-pushout
        x0 x1 y1 q11 r c ,
        λ (p , q) →
          coherence-column-row-path-code-left-2-decomposition-span-pushout
            x0 x1 y1 q11 r c p q)
```

## Lifting the pointwise glue theorem to the total gap map

```agda
  is-connected-map-gap-span-pushout-is-connected-map-glue-span-pushout-Blakers-Massey :
    (k n : 𝕋) →
    ( (x : X) (y : Y) →
      is-connected-map (add+2-𝕋 n k) (glue-span-pushout Q x y)) →
    is-connected-map (add+2-𝕋 n k) (gap-span-pushout Q)
  is-connected-map-gap-span-pushout-is-connected-map-glue-span-pushout-Blakers-Massey
    k n =
    is-connected-map-gap-span-pushout-is-connected-map-glue-span-pushout
      ( Q)
      ( add+2-𝕋 n k)

  is-connected-map-glue-span-pushout-Blakers-Massey-is-connected-map-gap-span-pushout :
    (k n : 𝕋) →
    is-connected-map (add+2-𝕋 n k) (gap-span-pushout Q) →
    (x : X) (y : Y) →
    is-connected-map (add+2-𝕋 n k) (glue-span-pushout Q x y)
  is-connected-map-glue-span-pushout-Blakers-Massey-is-connected-map-gap-span-pushout
    k n =
    is-connected-map-glue-span-pushout-is-connected-map-gap-span-pushout
      ( Q)
      ( add+2-𝕋 n k)
```

## Row and column hypotheses for an ordinary span

```agda
module _
  {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B)
  where

  equiv-row-total-space-relation-map-span-pushout-fiber-left-map :
    (a : A) →
    row-total-space-span-pushout (relation-map-span-pushout f g) a ≃
    fiber f a
  pr1 (equiv-row-total-space-relation-map-span-pushout-fiber-left-map a)
    (_ , s , p , _) =
    s , p
  pr2 (equiv-row-total-space-relation-map-span-pushout-fiber-left-map a) =
    is-equiv-is-invertible
      ( λ (s , p) → g s , s , p , refl)
      ( λ (s , p) → refl)
      ( λ { (_ , s , p , refl) → refl})

  equiv-column-total-space-relation-map-span-pushout-fiber-right-map :
    (b : B) →
    column-total-space-span-pushout (relation-map-span-pushout f g) b ≃
    fiber g b
  pr1 (equiv-column-total-space-relation-map-span-pushout-fiber-right-map b)
    (_ , s , _ , q) =
    s , q
  pr2 (equiv-column-total-space-relation-map-span-pushout-fiber-right-map b) =
    is-equiv-is-invertible
      ( λ (s , q) → f s , s , refl , q)
      ( λ (s , q) → refl)
      ( λ { (_ , s , refl , q) → refl})

  is-connected-row-total-space-relation-map-span-pushout-is-connected-map-left-map :
    (k : 𝕋) →
    is-connected-map k f →
    (a : A) →
    is-connected k
      ( row-total-space-span-pushout (relation-map-span-pushout f g) a)
  is-connected-row-total-space-relation-map-span-pushout-is-connected-map-left-map
    k H a =
    is-connected-equiv
      ( equiv-row-total-space-relation-map-span-pushout-fiber-left-map a)
      ( H a)

  is-connected-column-total-space-relation-map-span-pushout-is-connected-map-right-map :
    (k : 𝕋) →
    is-connected-map k g →
    (b : B) →
    is-connected k
      ( column-total-space-span-pushout (relation-map-span-pushout f g) b)
  is-connected-column-total-space-relation-map-span-pushout-is-connected-map-right-map
    k H b =
    is-connected-equiv
      ( equiv-column-total-space-relation-map-span-pushout-fiber-right-map b)
      ( H b)

  is-connected-join-paths-relation-map-span-pushout-is-connected-maps :
    (k n : 𝕋) →
    is-connected-map (succ-𝕋 k) f →
    is-connected-map (succ-𝕋 n) g →
    (a1 a3 : A) (b2 b4 : B)
    (q12 : relation-map-span-pushout f g a1 b2)
    (q32 : relation-map-span-pushout f g a3 b2)
    (q34 : relation-map-span-pushout f g a3 b4) →
    is-connected
      ( add+2-𝕋 n k)
      ( ( (a1 , q12) ＝ (a3 , q32)) *
        ( (b2 , q32) ＝ (b4 , q34)))
  is-connected-join-paths-relation-map-span-pushout-is-connected-maps
    k n H K =
    is-connected-join-paths-span-pushout
      ( relation-map-span-pushout f g)
      ( k)
      ( n)
      ( is-connected-row-total-space-relation-map-span-pushout-is-connected-map-left-map
        ( succ-𝕋 k)
        ( H))
      ( is-connected-column-total-space-relation-map-span-pushout-is-connected-map-right-map
        ( succ-𝕋 n)
        ( K))
```
