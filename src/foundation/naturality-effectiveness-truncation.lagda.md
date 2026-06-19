# Naturality of effectiveness of truncation

```agda
module foundation.naturality-effectiveness-truncation where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.functoriality-truncation
open import foundation.identity-types
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.universe-levels
```

</details>

## Idea

Effectiveness of truncation is natural in maps. Applying the truncation of a
map to the effective path associated to a truncated identification agrees with
first applying the truncation of the action on identifications and then using
effectiveness in the codomain, up to the naturality paths of the truncation
unit.

## Theorem

```agda
module _
  {l : Level} (k : 𝕋) {A : UU l} {a x : A}
  where

  compute-map-effectiveness-trunc-unit-trunc :
    (q : a ＝ x) →
    map-effectiveness-trunc k a x (unit-trunc q) ＝
    ap unit-trunc q
  compute-map-effectiveness-trunc-unit-trunc refl =
    refl-effectiveness-trunc k a

module _
  {l : Level} (k : 𝕋) {A : UU l} {a : A}
  where

  preserves-concat-map-effectiveness-trunc-unit-trunc :
    (p q : a ＝ a) →
    map-effectiveness-trunc k a a (unit-trunc (p ∙ q)) ＝
    ( map-effectiveness-trunc k a a (unit-trunc p)) ∙
    ( map-effectiveness-trunc k a a (unit-trunc q))
  preserves-concat-map-effectiveness-trunc-unit-trunc p q =
    ( compute-map-effectiveness-trunc-unit-trunc k (p ∙ q)) ∙
    ( ap-concat (unit-trunc {k = succ-𝕋 k}) p q) ∙
    ( ap-binary
      ( λ r s → r ∙ s)
      ( inv (compute-map-effectiveness-trunc-unit-trunc k p))
      ( inv (compute-map-effectiveness-trunc-unit-trunc k q)))

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  {a x : A}
  where

  naturality-map-effectiveness-trunc :
    (p : type-trunc k (a ＝ x)) →
    ap (map-trunc (succ-𝕋 k) f)
      ( map-effectiveness-trunc k a x p) ＝
    ( naturality-unit-trunc (succ-𝕋 k) f a) ∙
    ( map-effectiveness-trunc k (f a) (f x) (map-trunc k (ap f) p)) ∙
    ( inv (naturality-unit-trunc (succ-𝕋 k) f x))

  compute-naturality-map-effectiveness-trunc-unit-trunc :
    (q : a ＝ x) →
    ap (map-trunc (succ-𝕋 k) f)
      ( map-effectiveness-trunc k a x (unit-trunc q)) ＝
    ( naturality-unit-trunc (succ-𝕋 k) f a) ∙
    ( map-effectiveness-trunc
      ( k)
      ( f a)
      ( f x)
      ( map-trunc k (ap f) (unit-trunc q))) ∙
    ( inv (naturality-unit-trunc (succ-𝕋 k) f x))
  compute-naturality-map-effectiveness-trunc-unit-trunc refl =
    ( ap
      ( ap (map-trunc (succ-𝕋 k) f))
      ( refl-effectiveness-trunc k a)) ∙
    ( inv ((ap (_∙ inv η) right-unit) ∙ (right-inv η))) ∙
    ( ap
      ( λ u → η ∙ u ∙ inv η)
      ( inv
        ( ( ap
            ( map-effectiveness-trunc k (f a) (f a))
            ( naturality-unit-trunc k (ap f) refl)) ∙
          ( refl-effectiveness-trunc k (f a)))))
    where
    η = naturality-unit-trunc (succ-𝕋 k) f a

  naturality-map-effectiveness-trunc =
    function-dependent-universal-property-trunc
      ( λ p →
        Id-Truncated-Type'
          ( Id-Truncated-Type
            ( trunc (succ-𝕋 k) B)
            ( map-trunc (succ-𝕋 k) f (unit-trunc a))
            ( map-trunc (succ-𝕋 k) f (unit-trunc x)))
          ( ap (map-trunc (succ-𝕋 k) f)
            ( map-effectiveness-trunc k a x p))
          ( ( naturality-unit-trunc (succ-𝕋 k) f a) ∙
            ( map-effectiveness-trunc k (f a) (f x) (map-trunc k (ap f) p)) ∙
            ( inv (naturality-unit-trunc (succ-𝕋 k) f x))))
      compute-naturality-map-effectiveness-trunc-unit-trunc
```
