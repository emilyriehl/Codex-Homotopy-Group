# Loop spaces of pointed equivalences

```agda
module synthetic-homotopy-theory.loop-spaces-pointed-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.whiskering-pointed-homotopies-composition

open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

The loop-space functor preserves the inverse and composition structure of
pointed equivalences. This file records explicit pointed homotopies for those
comparisons, so LES modules can use them without carrying generic pointed-map
algebra locally.

## Definitions

```agda
pointed-htpy-Ω-inv-pointed-equiv :
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (e : A ≃∗ B) →
  pointed-map-Ω (pointed-map-inv-pointed-equiv e) ~∗
  pointed-map-inv-pointed-equiv (pointed-equiv-Ω-pointed-equiv e)
pointed-htpy-Ω-inv-pointed-equiv e =
  concat-pointed-htpy
    ( inv-left-unit-law-comp-pointed-map
      ( pointed-map-Ω (pointed-map-inv-pointed-equiv e)))
    ( concat-pointed-htpy
      ( right-whisker-comp-pointed-htpy
        ( id-pointed-map)
        ( pointed-map-inv-pointed-equiv (pointed-equiv-Ω-pointed-equiv e) ∘∗
          pointed-map-pointed-equiv (pointed-equiv-Ω-pointed-equiv e))
        ( inv-pointed-htpy
          ( is-pointed-retraction-pointed-map-inv-pointed-equiv
            ( pointed-equiv-Ω-pointed-equiv e)))
        ( pointed-map-Ω (pointed-map-inv-pointed-equiv e)))
      ( concat-pointed-htpy
        ( associative-comp-pointed-map
          ( pointed-map-inv-pointed-equiv (pointed-equiv-Ω-pointed-equiv e))
          ( pointed-map-pointed-equiv (pointed-equiv-Ω-pointed-equiv e))
          ( pointed-map-Ω (pointed-map-inv-pointed-equiv e)))
        ( concat-pointed-htpy
          ( left-whisker-comp-pointed-htpy
            ( pointed-map-inv-pointed-equiv (pointed-equiv-Ω-pointed-equiv e))
            ( pointed-map-pointed-equiv (pointed-equiv-Ω-pointed-equiv e) ∘∗
              pointed-map-Ω (pointed-map-inv-pointed-equiv e))
            ( id-pointed-map)
            ( concat-pointed-htpy
              ( inv-pointed-htpy
                ( preserves-comp-pointed-map-Ω
                  ( pointed-map-pointed-equiv e)
                  ( pointed-map-inv-pointed-equiv e)))
              ( concat-pointed-htpy
                ( pointed-htpy-Ω
                  ( pointed-map-pointed-equiv e ∘∗
                    pointed-map-inv-pointed-equiv e)
                  ( id-pointed-map)
                  ( is-pointed-section-pointed-map-inv-pointed-equiv e))
                ( preserves-id-pointed-map-Ω))))
          ( right-unit-law-comp-pointed-map
            ( pointed-map-inv-pointed-equiv
              ( pointed-equiv-Ω-pointed-equiv e))))))

is-retraction-map-Ω-pointed-map-inv-pointed-equiv :
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (e : A ≃∗ B) (q : type-Ω A) →
  map-Ω (pointed-map-inv-pointed-equiv e)
    ( map-Ω (pointed-map-pointed-equiv e) q) ＝
  q
is-retraction-map-Ω-pointed-map-inv-pointed-equiv e q =
  ( pr1 (pointed-htpy-Ω-inv-pointed-equiv e)
    ( map-Ω (pointed-map-pointed-equiv e) q)) ∙
  ( is-retraction-map-inv-equiv (equiv-Ω-pointed-equiv e) q)

pointed-htpy-section-explicit-inv-comp-pointed-equiv :
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  (e : A ≃∗ B) (f : B ≃∗ C) →
  ( pointed-map-pointed-equiv (comp-pointed-equiv f e) ∘∗
    ( pointed-map-inv-pointed-equiv e ∘∗
      pointed-map-inv-pointed-equiv f)) ~∗
  id-pointed-map
pointed-htpy-section-explicit-inv-comp-pointed-equiv e f =
  concat-pointed-htpy
    ( associative-comp-pointed-map
      ( pointed-map-pointed-equiv f)
      ( pointed-map-pointed-equiv e)
      ( pointed-map-inv-pointed-equiv e ∘∗
        pointed-map-inv-pointed-equiv f))
    ( concat-pointed-htpy
      ( left-whisker-comp-pointed-htpy
        ( pointed-map-pointed-equiv f)
        ( pointed-map-pointed-equiv e ∘∗
          ( pointed-map-inv-pointed-equiv e ∘∗
            pointed-map-inv-pointed-equiv f))
        ( ( pointed-map-pointed-equiv e ∘∗
            pointed-map-inv-pointed-equiv e) ∘∗
          pointed-map-inv-pointed-equiv f)
        ( inv-associative-comp-pointed-map
          ( pointed-map-pointed-equiv e)
          ( pointed-map-inv-pointed-equiv e)
          ( pointed-map-inv-pointed-equiv f)))
      ( concat-pointed-htpy
        ( left-whisker-comp-pointed-htpy
          ( pointed-map-pointed-equiv f)
          ( ( pointed-map-pointed-equiv e ∘∗
              pointed-map-inv-pointed-equiv e) ∘∗
            pointed-map-inv-pointed-equiv f)
          ( pointed-map-inv-pointed-equiv f)
          ( concat-pointed-htpy
            ( right-whisker-comp-pointed-htpy
              ( pointed-map-pointed-equiv e ∘∗
                pointed-map-inv-pointed-equiv e)
              ( id-pointed-map)
              ( is-pointed-section-pointed-map-inv-pointed-equiv e)
              ( pointed-map-inv-pointed-equiv f))
            ( left-unit-law-comp-pointed-map
              ( pointed-map-inv-pointed-equiv f))))
        ( is-pointed-section-pointed-map-inv-pointed-equiv f)))

pointed-htpy-inv-comp-pointed-equiv :
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  (e : A ≃∗ B) (f : B ≃∗ C) →
  ( pointed-map-inv-pointed-equiv e ∘∗
    pointed-map-inv-pointed-equiv f) ~∗
  pointed-map-inv-pointed-equiv (comp-pointed-equiv f e)
pointed-htpy-inv-comp-pointed-equiv e f =
  concat-pointed-htpy
    ( inv-left-unit-law-comp-pointed-map
      ( pointed-map-inv-pointed-equiv e ∘∗
        pointed-map-inv-pointed-equiv f))
    ( concat-pointed-htpy
      ( right-whisker-comp-pointed-htpy
        ( id-pointed-map)
        ( pointed-map-inv-pointed-equiv (comp-pointed-equiv f e) ∘∗
          pointed-map-pointed-equiv (comp-pointed-equiv f e))
        ( inv-pointed-htpy
          ( is-pointed-retraction-pointed-map-inv-pointed-equiv
            ( comp-pointed-equiv f e)))
        ( pointed-map-inv-pointed-equiv e ∘∗
          pointed-map-inv-pointed-equiv f))
      ( concat-pointed-htpy
        ( associative-comp-pointed-map
          ( pointed-map-inv-pointed-equiv (comp-pointed-equiv f e))
          ( pointed-map-pointed-equiv (comp-pointed-equiv f e))
          ( pointed-map-inv-pointed-equiv e ∘∗
            pointed-map-inv-pointed-equiv f))
        ( concat-pointed-htpy
          ( left-whisker-comp-pointed-htpy
            ( pointed-map-inv-pointed-equiv (comp-pointed-equiv f e))
            ( pointed-map-pointed-equiv (comp-pointed-equiv f e) ∘∗
              ( pointed-map-inv-pointed-equiv e ∘∗
                pointed-map-inv-pointed-equiv f))
            ( id-pointed-map)
            ( pointed-htpy-section-explicit-inv-comp-pointed-equiv e f))
          ( right-unit-law-comp-pointed-map
            ( pointed-map-inv-pointed-equiv
              ( comp-pointed-equiv f e))))))
```
