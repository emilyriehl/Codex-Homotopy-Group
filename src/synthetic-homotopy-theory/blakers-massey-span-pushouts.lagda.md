# Blakers-Massey for span pushouts

```agda
module synthetic-homotopy-theory.blakers-massey-span-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.identity-types
open import foundation.iterated-successors-truncation-levels
open import foundation.truncation-levels
open import foundation.universe-levels

open import synthetic-homotopy-theory.connectivity-joins-of-types
open import synthetic-homotopy-theory.joins-of-types
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
  is-connected-join-paths-span-pushout :
    (k n : 𝕋) →
    ((x : X) → is-connected (succ-𝕋 k) (row-total-space-span-pushout x)) →
    ((y : Y) → is-connected (succ-𝕋 n) (column-total-space-span-pushout y)) →
    (x1 x3 : X) (y2 y4 : Y)
    (q12 : Q x1 y2) (q32 : Q x3 y2) (q34 : Q x3 y4) →
    is-connected
      ( add+2-𝕋 n k)
      ( ( (x1 , q12) ＝ (x3 , q32)) *
        ( (y2 , q32) ＝ (y4 , q34)))
  is-connected-join-paths-span-pushout
    k n row-connected column-connected x1 x3 y2 y4 q12 q32 q34 =
    is-connected-join-is-connected
      ( n)
      ( k)
      ( is-connected-eq-is-connected (column-connected y2))
      ( is-connected-eq-is-connected (row-connected x3))
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
