# Naturality of effectiveness of truncation for loop spaces

```agda
module synthetic-homotopy-theory.naturality-effectiveness-loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.functoriality-truncation
open import foundation.identity-types
open import foundation.naturality-effectiveness-truncation
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.universe-levels

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

Naturality of effectiveness of truncation compares paths based at
`map-trunc (succ-𝕋 k) f (unit-trunc a)`. For pointed applications, the
corresponding loop must be transported along the truncation-unit naturality path
to be based at `unit-trunc (f a)`.

## Transport algebra for loop spaces

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  eq-tr-type-Ω-concat-inv-right-unit :
    (p : x ＝ y) (q : y ＝ y) →
    tr-type-Ω (p ∙ refl) ((p ∙ q) ∙ inv p) ＝ q
  eq-tr-type-Ω-concat-inv-right-unit refl q = right-unit
```

## Theorem

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  {a : A}
  where

  tr-naturality-map-effectiveness-trunc :
    (p : type-trunc k (a ＝ a)) →
    tr-type-Ω
      ( naturality-unit-trunc (succ-𝕋 k) f a ∙ refl)
      ( ap (map-trunc (succ-𝕋 k) f)
        ( map-effectiveness-trunc k a a p)) ＝
    map-effectiveness-trunc k (f a) (f a) (map-trunc k (ap f) p)
  tr-naturality-map-effectiveness-trunc p =
    ( ap
      ( tr-type-Ω (naturality-unit-trunc (succ-𝕋 k) f a ∙ refl))
      ( naturality-map-effectiveness-trunc k f p)) ∙
    ( eq-tr-type-Ω-concat-inv-right-unit
      ( naturality-unit-trunc (succ-𝕋 k) f a)
      ( map-effectiveness-trunc k (f a) (f a) (map-trunc k (ap f) p)))
```
