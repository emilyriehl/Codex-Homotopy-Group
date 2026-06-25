# Span pushouts

```agda
module synthetic-homotopy-theory.span-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.standard-pullbacks
open import foundation.universe-levels

open import synthetic-homotopy-theory.gap-maps-pushouts
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

A binary relation `Q : X → Y → 𝒰` determines a span

```text
  X <- Σ x y, Q x y -> Y.
```

The pushout of this span is a relation-indexed pushout. Its canonical gap map
from the total relation into the pullback of the two inclusions is the map used
in the Blakers-Massey proof before specializing to ordinary pushout squares.

## Definitions

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Q : X → Y → UU l3)
  where

  total-relation-span-pushout : UU (l1 ⊔ l2 ⊔ l3)
  total-relation-span-pushout = Σ X (λ x → Σ Y (Q x))

  left-map-span-pushout : total-relation-span-pushout → X
  left-map-span-pushout = pr1

  right-map-span-pushout : total-relation-span-pushout → Y
  right-map-span-pushout t = pr1 (pr2 t)

  span-pushout : UU (l1 ⊔ l2 ⊔ l3)
  span-pushout = pushout left-map-span-pushout right-map-span-pushout

  inl-span-pushout : X → span-pushout
  inl-span-pushout =
    inl-pushout left-map-span-pushout right-map-span-pushout

  inr-span-pushout : Y → span-pushout
  inr-span-pushout =
    inr-pushout left-map-span-pushout right-map-span-pushout

  glue-span-pushout :
    (x : X) (y : Y) → Q x y → inl-span-pushout x ＝ inr-span-pushout y
  glue-span-pushout x y q =
    glue-pushout left-map-span-pushout right-map-span-pushout (x , y , q)

  gap-span-pushout :
    total-relation-span-pushout →
    standard-pullback inl-span-pushout inr-span-pushout
  pr1 (gap-span-pushout (x , y , q)) = x
  pr1 (pr2 (gap-span-pushout (x , y , q))) = y
  pr2 (pr2 (gap-span-pushout (x , y , q))) = glue-span-pushout x y q

  triangle-gap-pushout-gap-span-pushout :
    gap-pushout
      ( left-map-span-pushout)
      ( right-map-span-pushout)
      ( cocone-pushout left-map-span-pushout right-map-span-pushout) ~
    gap-span-pushout
  triangle-gap-pushout-gap-span-pushout (x , y , q) = refl
```

## Relation associated to two maps

```agda
module _
  {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B)
  where

  relation-map-span-pushout : A → B → UU (l1 ⊔ l2 ⊔ l3)
  relation-map-span-pushout a b =
    Σ S (λ s → (f s ＝ a) × (g s ＝ b))

  map-total-relation-map-span-pushout :
    total-relation-span-pushout relation-map-span-pushout → S
  map-total-relation-map-span-pushout (_ , _ , s , _ , _) = s

  map-inv-total-relation-map-span-pushout :
    S → total-relation-span-pushout relation-map-span-pushout
  map-inv-total-relation-map-span-pushout s =
    f s , g s , s , refl , refl

  is-section-map-inv-total-relation-map-span-pushout :
    ( map-total-relation-map-span-pushout ∘
      map-inv-total-relation-map-span-pushout) ~
    id
  is-section-map-inv-total-relation-map-span-pushout s = refl

  is-retraction-map-inv-total-relation-map-span-pushout :
    ( map-inv-total-relation-map-span-pushout ∘
      map-total-relation-map-span-pushout) ~
    id
  is-retraction-map-inv-total-relation-map-span-pushout
    (.(f s) , .(g s) , s , refl , refl) =
    refl

  is-equiv-map-total-relation-map-span-pushout :
    is-equiv map-total-relation-map-span-pushout
  is-equiv-map-total-relation-map-span-pushout =
    is-equiv-is-invertible
      ( map-inv-total-relation-map-span-pushout)
      ( is-section-map-inv-total-relation-map-span-pushout)
      ( is-retraction-map-inv-total-relation-map-span-pushout)

  equiv-total-relation-map-span-pushout :
    total-relation-span-pushout relation-map-span-pushout ≃ S
  pr1 equiv-total-relation-map-span-pushout =
    map-total-relation-map-span-pushout
  pr2 equiv-total-relation-map-span-pushout =
    is-equiv-map-total-relation-map-span-pushout
```
