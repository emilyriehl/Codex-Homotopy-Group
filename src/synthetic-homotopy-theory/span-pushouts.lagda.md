# Span pushouts

```agda
module synthetic-homotopy-theory.span-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
open import foundation.connected-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.standard-pullbacks
open import foundation.truncation-levels
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.gap-maps-pushouts
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
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

  is-equiv-map-inv-total-relation-map-span-pushout :
    is-equiv map-inv-total-relation-map-span-pushout
  is-equiv-map-inv-total-relation-map-span-pushout =
    is-equiv-is-invertible
      ( map-total-relation-map-span-pushout)
      ( is-retraction-map-inv-total-relation-map-span-pushout)
      ( is-section-map-inv-total-relation-map-span-pushout)

  coherence-left-map-total-relation-map-span-pushout :
    coherence-square-maps
      ( map-total-relation-map-span-pushout)
      ( left-map-span-pushout relation-map-span-pushout)
      ( f)
      ( id)
  coherence-left-map-total-relation-map-span-pushout
    (_ , _ , _ , p , _) =
    inv p

  coherence-right-map-total-relation-map-span-pushout :
    coherence-square-maps
      ( right-map-span-pushout relation-map-span-pushout)
      ( map-total-relation-map-span-pushout)
      ( id)
      ( g)
  coherence-right-map-total-relation-map-span-pushout
    (_ , _ , _ , _ , q) =
    q

  cocone-pushout-relation-map-span-pushout :
    cocone
      ( left-map-span-pushout relation-map-span-pushout)
      ( right-map-span-pushout relation-map-span-pushout)
      ( pushout f g)
  cocone-pushout-relation-map-span-pushout =
    comp-cocone-hom-span
      ( f)
      ( g)
      ( left-map-span-pushout relation-map-span-pushout)
      ( right-map-span-pushout relation-map-span-pushout)
      ( id)
      ( id)
      ( map-total-relation-map-span-pushout)
      ( cocone-pushout f g)
      ( coherence-left-map-total-relation-map-span-pushout)
      ( coherence-right-map-total-relation-map-span-pushout)

  universal-property-pushout-cocone-pushout-relation-map-span-pushout :
    universal-property-pushout
      ( left-map-span-pushout relation-map-span-pushout)
      ( right-map-span-pushout relation-map-span-pushout)
      ( cocone-pushout-relation-map-span-pushout)
  universal-property-pushout-cocone-pushout-relation-map-span-pushout =
    universal-property-pushout-extended-by-equivalences
      ( f)
      ( g)
      ( left-map-span-pushout relation-map-span-pushout)
      ( right-map-span-pushout relation-map-span-pushout)
      ( id)
      ( id)
      ( map-total-relation-map-span-pushout)
      ( cocone-pushout f g)
      ( up-pushout f g)
      ( coherence-left-map-total-relation-map-span-pushout)
      ( coherence-right-map-total-relation-map-span-pushout)
      ( is-equiv-id)
      ( is-equiv-id)
      ( is-equiv-map-total-relation-map-span-pushout)

  map-span-pushout-relation-map-span-pushout-pushout :
    span-pushout relation-map-span-pushout → pushout f g
  map-span-pushout-relation-map-span-pushout-pushout =
    cogap
      ( left-map-span-pushout relation-map-span-pushout)
      ( right-map-span-pushout relation-map-span-pushout)
      ( cocone-pushout-relation-map-span-pushout)

  is-equiv-map-span-pushout-relation-map-span-pushout-pushout :
    is-equiv map-span-pushout-relation-map-span-pushout-pushout
  is-equiv-map-span-pushout-relation-map-span-pushout-pushout =
    is-pushout-universal-property-pushout
      ( left-map-span-pushout relation-map-span-pushout)
      ( right-map-span-pushout relation-map-span-pushout)
      ( cocone-pushout-relation-map-span-pushout)
      ( universal-property-pushout-cocone-pushout-relation-map-span-pushout)

  equiv-span-pushout-relation-map-span-pushout-pushout :
    span-pushout relation-map-span-pushout ≃ pushout f g
  pr1 equiv-span-pushout-relation-map-span-pushout-pushout =
    map-span-pushout-relation-map-span-pushout-pushout
  pr2 equiv-span-pushout-relation-map-span-pushout-pushout =
    is-equiv-map-span-pushout-relation-map-span-pushout-pushout

  equiv-pushout-span-pushout-relation-map-span-pushout :
    pushout f g ≃ span-pushout relation-map-span-pushout
  equiv-pushout-span-pushout-relation-map-span-pushout =
    inv-equiv equiv-span-pushout-relation-map-span-pushout-pushout

  map-standard-pullback-span-pushout-relation-map-span-pushout-pushout :
    standard-pullback
      ( inl-span-pushout relation-map-span-pushout)
      ( inr-span-pushout relation-map-span-pushout) →
    standard-pullback (inl-pushout f g) (inr-pushout f g)
  pr1
    ( map-standard-pullback-span-pushout-relation-map-span-pushout-pushout
      ( a , b , p)) =
    a
  pr1
    ( pr2
      ( map-standard-pullback-span-pushout-relation-map-span-pushout-pushout
        ( a , b , p))) =
    b
  pr2
    ( pr2
      ( map-standard-pullback-span-pushout-relation-map-span-pushout-pushout
        ( a , b , p))) =
    concat'
      ( inl-pushout f g a)
      ( compute-inr-cogap
        ( left-map-span-pushout relation-map-span-pushout)
        ( right-map-span-pushout relation-map-span-pushout)
        ( cocone-pushout-relation-map-span-pushout)
        ( b))
      ( concat
        ( inv
          ( compute-inl-cogap
            ( left-map-span-pushout relation-map-span-pushout)
            ( right-map-span-pushout relation-map-span-pushout)
            ( cocone-pushout-relation-map-span-pushout)
            ( a)))
        ( map-span-pushout-relation-map-span-pushout-pushout
          ( inr-span-pushout relation-map-span-pushout b))
        ( ap map-span-pushout-relation-map-span-pushout-pushout p))

  is-equiv-map-standard-pullback-span-pushout-relation-map-span-pushout-pushout :
    is-equiv
      ( map-standard-pullback-span-pushout-relation-map-span-pushout-pushout)
  is-equiv-map-standard-pullback-span-pushout-relation-map-span-pushout-pushout =
    is-equiv-tot-is-fiberwise-equiv
      ( λ a →
        is-equiv-tot-is-fiberwise-equiv
          ( λ b →
            is-equiv-comp
              ( concat'
                ( inl-pushout f g a)
                ( compute-inr-cogap
                  ( left-map-span-pushout relation-map-span-pushout)
                  ( right-map-span-pushout relation-map-span-pushout)
                  ( cocone-pushout-relation-map-span-pushout)
                  ( b)))
              ( concat
                ( inv
                  ( compute-inl-cogap
                    ( left-map-span-pushout relation-map-span-pushout)
                    ( right-map-span-pushout relation-map-span-pushout)
                    ( cocone-pushout-relation-map-span-pushout)
                    ( a)))
                ( map-span-pushout-relation-map-span-pushout-pushout
                  ( inr-span-pushout relation-map-span-pushout b)) ∘
                ap map-span-pushout-relation-map-span-pushout-pushout)
              ( is-equiv-comp
                ( concat
                  ( inv
                    ( compute-inl-cogap
                      ( left-map-span-pushout relation-map-span-pushout)
                      ( right-map-span-pushout relation-map-span-pushout)
                      ( cocone-pushout-relation-map-span-pushout)
                      ( a)))
                  ( map-span-pushout-relation-map-span-pushout-pushout
                    ( inr-span-pushout relation-map-span-pushout b)))
                ( ap map-span-pushout-relation-map-span-pushout-pushout)
                ( is-equiv-map-equiv
                  ( equiv-ap
                    ( equiv-span-pushout-relation-map-span-pushout-pushout)
                    ( inl-span-pushout relation-map-span-pushout a)
                    ( inr-span-pushout relation-map-span-pushout b)))
                ( is-equiv-concat
                  ( inv
                    ( compute-inl-cogap
                      ( left-map-span-pushout relation-map-span-pushout)
                      ( right-map-span-pushout relation-map-span-pushout)
                      ( cocone-pushout-relation-map-span-pushout)
                      ( a)))
                  ( map-span-pushout-relation-map-span-pushout-pushout
                    ( inr-span-pushout relation-map-span-pushout b))))
              ( is-equiv-concat'
                ( inl-pushout f g a)
                ( compute-inr-cogap
                  ( left-map-span-pushout relation-map-span-pushout)
                  ( right-map-span-pushout relation-map-span-pushout)
                  ( cocone-pushout-relation-map-span-pushout)
                  ( b)))))

  equiv-standard-pullback-span-pushout-relation-map-span-pushout-pushout :
    standard-pullback
      ( inl-span-pushout relation-map-span-pushout)
      ( inr-span-pushout relation-map-span-pushout) ≃
    standard-pullback (inl-pushout f g) (inr-pushout f g)
  pr1 equiv-standard-pullback-span-pushout-relation-map-span-pushout-pushout =
    map-standard-pullback-span-pushout-relation-map-span-pushout-pushout
  pr2 equiv-standard-pullback-span-pushout-relation-map-span-pushout-pushout =
    is-equiv-map-standard-pullback-span-pushout-relation-map-span-pushout-pushout

  triangle-map-standard-pullback-gap-span-pushout-relation-map-span-pushout :
    ( map-standard-pullback-span-pushout-relation-map-span-pushout-pushout ∘
      gap-span-pushout relation-map-span-pushout) ~
    gap-pushout
      ( left-map-span-pushout relation-map-span-pushout)
      ( right-map-span-pushout relation-map-span-pushout)
      ( cocone-pushout-relation-map-span-pushout)
  triangle-map-standard-pullback-gap-span-pushout-relation-map-span-pushout
    ( a , b , q) =
    eq-Eq-standard-pullback
      ( inl-pushout f g)
      ( inr-pushout f g)
      ( refl)
      ( refl)
      ( left-unit ∙ inv path-coherence ∙ inv right-unit)
    where
    t = a , b , q

    H :
      map-span-pushout-relation-map-span-pushout-pushout
        ( inl-span-pushout relation-map-span-pushout a) ＝
      inl-pushout f g a
    H =
      compute-inl-cogap
        ( left-map-span-pushout relation-map-span-pushout)
        ( right-map-span-pushout relation-map-span-pushout)
        ( cocone-pushout-relation-map-span-pushout)
        ( a)

    K :
      map-span-pushout-relation-map-span-pushout-pushout
        ( inr-span-pushout relation-map-span-pushout b) ＝
      inr-pushout f g b
    K =
      compute-inr-cogap
        ( left-map-span-pushout relation-map-span-pushout)
        ( right-map-span-pushout relation-map-span-pushout)
        ( cocone-pushout-relation-map-span-pushout)
        ( b)

    path-coherence :
      coherence-square-standard-pullback
        ( map-standard-pullback-span-pushout-relation-map-span-pushout-pushout
          ( gap-span-pushout relation-map-span-pushout t)) ＝
      coherence-square-cocone
        ( left-map-span-pushout relation-map-span-pushout)
        ( right-map-span-pushout relation-map-span-pushout)
        ( cocone-pushout-relation-map-span-pushout)
        ( t)
    path-coherence =
      ( assoc
        ( inv H)
        ( ap
          ( map-span-pushout-relation-map-span-pushout-pushout)
          ( glue-span-pushout relation-map-span-pushout a b q))
        ( K)) ∙
      ( ap
        ( concat (inv H) (inr-pushout f g b))
        ( compute-glue-cogap
          ( left-map-span-pushout relation-map-span-pushout)
          ( right-map-span-pushout relation-map-span-pushout)
          ( cocone-pushout-relation-map-span-pushout)
          ( t))) ∙
      ( inv
        ( assoc
          ( inv H)
          ( H)
          ( coherence-square-cocone
            ( left-map-span-pushout relation-map-span-pushout)
            ( right-map-span-pushout relation-map-span-pushout)
            ( cocone-pushout-relation-map-span-pushout)
            ( t)))) ∙
      ( ap
        ( _∙
          coherence-square-cocone
            ( left-map-span-pushout relation-map-span-pushout)
            ( right-map-span-pushout relation-map-span-pushout)
            ( cocone-pushout-relation-map-span-pushout)
            ( t))
        ( left-inv H)) ∙
      ( left-unit)

  is-connected-map-gap-pushout-relation-map-span-pushout-is-connected-map-gap-span-pushout :
    (k : 𝕋) →
    is-connected-map k (gap-span-pushout relation-map-span-pushout) →
    is-connected-map k
      ( gap-pushout
        ( left-map-span-pushout relation-map-span-pushout)
        ( right-map-span-pushout relation-map-span-pushout)
        ( cocone-pushout-relation-map-span-pushout))
  is-connected-map-gap-pushout-relation-map-span-pushout-is-connected-map-gap-span-pushout
    k H =
    is-connected-map-htpy'
      ( k)
      ( triangle-map-standard-pullback-gap-span-pushout-relation-map-span-pushout)
      ( is-connected-map-comp
        ( k)
        ( is-connected-map-is-equiv
          ( is-equiv-map-standard-pullback-span-pushout-relation-map-span-pushout-pushout))
        ( H))

  triangle-gap-pushout-relation-map-span-pushout-gap-pushout :
    ( gap-pushout
      ( left-map-span-pushout relation-map-span-pushout)
      ( right-map-span-pushout relation-map-span-pushout)
      ( cocone-pushout-relation-map-span-pushout) ∘
      map-inv-total-relation-map-span-pushout) ~
    gap-pushout f g (cocone-pushout f g)
  triangle-gap-pushout-relation-map-span-pushout-gap-pushout s =
    eq-Eq-standard-pullback
      ( inl-pushout f g)
      ( inr-pushout f g)
      ( refl)
      ( refl)
      ( left-unit ∙ inv right-unit ∙ inv right-unit)

  is-connected-map-gap-pushout-is-connected-map-gap-span-pushout :
    (k : 𝕋) →
    is-connected-map k (gap-span-pushout relation-map-span-pushout) →
    is-connected-map k (gap-pushout f g (cocone-pushout f g))
  is-connected-map-gap-pushout-is-connected-map-gap-span-pushout k H =
    is-connected-map-htpy'
      ( k)
      ( triangle-gap-pushout-relation-map-span-pushout-gap-pushout)
      ( is-connected-map-comp
        ( k)
        ( is-connected-map-gap-pushout-relation-map-span-pushout-is-connected-map-gap-span-pushout
          ( k)
          ( H))
        ( is-connected-map-is-equiv
          ( is-equiv-map-inv-total-relation-map-span-pushout)))
```
