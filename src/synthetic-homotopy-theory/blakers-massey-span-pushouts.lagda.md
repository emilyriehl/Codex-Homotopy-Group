# Blakers-Massey for span pushouts

```agda
module synthetic-homotopy-theory.blakers-massey-span-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.action-on-identifications-dependent-functions
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.contractible-types
open import foundation.commuting-squares-of-maps
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-extensionality-axiom
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.iterated-successors-truncation-levels
open import foundation.precomposition-functions
open import foundation.span-diagrams
open import foundation.transport-along-identifications
open import foundation.torsorial-type-families
open import foundation.truncation-equivalences
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.truncated-types
open import foundation.univalence
open import foundation.universe-levels

open import synthetic-homotopy-theory.connectivity-joins-of-types
open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.span-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
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

## Truncated pushouts

```agda
module _
  {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (m : 𝕋) (f : S → A) (g : S → B)
  where

  pushout-trunc-span : UU (l1 ⊔ l2 ⊔ l3)
  pushout-trunc-span = pushout (map-trunc m f) (map-trunc m g)

  cocone-pushout-trunc-span : cocone f g pushout-trunc-span
  pr1 cocone-pushout-trunc-span =
    inl-pushout (map-trunc m f) (map-trunc m g) ∘ unit-trunc
  pr1 (pr2 cocone-pushout-trunc-span) =
    inr-pushout (map-trunc m f) (map-trunc m g) ∘ unit-trunc
  pr2 (pr2 cocone-pushout-trunc-span) s =
    ( inv
      ( ap
        ( inl-pushout (map-trunc m f) (map-trunc m g))
        ( naturality-unit-trunc m f s))) ∙
    ( glue-pushout (map-trunc m f) (map-trunc m g) (unit-trunc s)) ∙
    ( ap
      ( inr-pushout (map-trunc m f) (map-trunc m g))
      ( naturality-unit-trunc m g s))

  map-pushout-trunc-span :
    pushout f g → pushout-trunc-span
  map-pushout-trunc-span =
    cogap f g cocone-pushout-trunc-span

  compute-inl-map-pushout-trunc-span :
    map-pushout-trunc-span ∘ inl-pushout f g ~
    inl-pushout (map-trunc m f) (map-trunc m g) ∘ unit-trunc
  compute-inl-map-pushout-trunc-span =
    compute-inl-cogap f g cocone-pushout-trunc-span

  compute-inr-map-pushout-trunc-span :
    map-pushout-trunc-span ∘ inr-pushout f g ~
    inr-pushout (map-trunc m f) (map-trunc m g) ∘ unit-trunc
  compute-inr-map-pushout-trunc-span =
    compute-inr-cogap f g cocone-pushout-trunc-span

  compute-glue-map-pushout-trunc-span :
    statement-coherence-htpy-cocone f g
      ( cocone-map f g (cocone-pushout f g) map-pushout-trunc-span)
      ( cocone-pushout-trunc-span)
      ( compute-inl-map-pushout-trunc-span)
      ( compute-inr-map-pushout-trunc-span)
  compute-glue-map-pushout-trunc-span =
    compute-glue-cogap f g cocone-pushout-trunc-span

  map-left-inv-pushout-trunc-span :
    type-trunc m A → type-trunc m (pushout f g)
  map-left-inv-pushout-trunc-span =
    map-universal-property-trunc
      ( trunc m (pushout f g))
      ( unit-trunc ∘ inl-pushout f g)

  map-right-inv-pushout-trunc-span :
    type-trunc m B → type-trunc m (pushout f g)
  map-right-inv-pushout-trunc-span =
    map-universal-property-trunc
      ( trunc m (pushout f g))
      ( unit-trunc ∘ inr-pushout f g)

  coherence-inv-pushout-trunc-span-unit :
    (s : S) →
    map-left-inv-pushout-trunc-span (map-trunc m f (unit-trunc s)) ＝
    map-right-inv-pushout-trunc-span (map-trunc m g (unit-trunc s))
  coherence-inv-pushout-trunc-span-unit s =
    ( ap map-left-inv-pushout-trunc-span
      ( naturality-unit-trunc m f s)) ∙
    ( triangle-universal-property-trunc
      ( trunc m (pushout f g))
      ( unit-trunc ∘ inl-pushout f g)
      ( f s)) ∙
    ( ap unit-trunc (glue-pushout f g s)) ∙
    ( inv
      ( triangle-universal-property-trunc
        ( trunc m (pushout f g))
        ( unit-trunc ∘ inr-pushout f g)
        ( g s))) ∙
    ( inv
      ( ap map-right-inv-pushout-trunc-span
        ( naturality-unit-trunc m g s)))

  coherence-inv-pushout-trunc-span :
    (t : type-trunc m S) →
    map-left-inv-pushout-trunc-span (map-trunc m f t) ＝
    map-right-inv-pushout-trunc-span (map-trunc m g t)
  coherence-inv-pushout-trunc-span =
    function-dependent-universal-property-trunc
      ( λ t →
        Id-Truncated-Type'
          ( trunc m (pushout f g))
          ( map-left-inv-pushout-trunc-span (map-trunc m f t))
          ( map-right-inv-pushout-trunc-span (map-trunc m g t)))
      ( coherence-inv-pushout-trunc-span-unit)

  cocone-inv-pushout-trunc-span :
    cocone
      ( map-trunc m f)
      ( map-trunc m g)
      ( type-trunc m (pushout f g))
  pr1 cocone-inv-pushout-trunc-span =
    map-left-inv-pushout-trunc-span
  pr1 (pr2 cocone-inv-pushout-trunc-span) =
    map-right-inv-pushout-trunc-span
  pr2 (pr2 cocone-inv-pushout-trunc-span) =
    coherence-inv-pushout-trunc-span

  map-inv-pushout-trunc-span :
    pushout-trunc-span → type-trunc m (pushout f g)
  map-inv-pushout-trunc-span =
    cogap (map-trunc m f) (map-trunc m g) cocone-inv-pushout-trunc-span

  map-left-extension-pushout-trunc-span :
    {l : Level} (X : Truncated-Type l m) →
    (pushout f g → type-Truncated-Type X) →
    type-trunc m A → type-Truncated-Type X
  map-left-extension-pushout-trunc-span X h =
    map-universal-property-trunc X (h ∘ inl-pushout f g)

  map-right-extension-pushout-trunc-span :
    {l : Level} (X : Truncated-Type l m) →
    (pushout f g → type-Truncated-Type X) →
    type-trunc m B → type-Truncated-Type X
  map-right-extension-pushout-trunc-span X h =
    map-universal-property-trunc X (h ∘ inr-pushout f g)

  coherence-extension-pushout-trunc-span-unit :
    {l : Level} (X : Truncated-Type l m)
    (h : pushout f g → type-Truncated-Type X) (s : S) →
    map-left-extension-pushout-trunc-span X h
      ( map-trunc m f (unit-trunc s)) ＝
    map-right-extension-pushout-trunc-span X h
      ( map-trunc m g (unit-trunc s))
  coherence-extension-pushout-trunc-span-unit X h s =
    ( ap (map-left-extension-pushout-trunc-span X h)
      ( naturality-unit-trunc m f s)) ∙
    ( triangle-universal-property-trunc
      ( X)
      ( h ∘ inl-pushout f g)
      ( f s)) ∙
    ( ap h (glue-pushout f g s)) ∙
    ( inv
      ( triangle-universal-property-trunc
        ( X)
        ( h ∘ inr-pushout f g)
        ( g s))) ∙
    ( inv
      ( ap (map-right-extension-pushout-trunc-span X h)
        ( naturality-unit-trunc m g s)))

  coherence-extension-pushout-trunc-span :
    {l : Level} (X : Truncated-Type l m)
    (h : pushout f g → type-Truncated-Type X) →
    (t : type-trunc m S) →
    map-left-extension-pushout-trunc-span X h (map-trunc m f t) ＝
    map-right-extension-pushout-trunc-span X h (map-trunc m g t)
  coherence-extension-pushout-trunc-span X h =
    function-dependent-universal-property-trunc
      ( λ t →
        Id-Truncated-Type'
          ( X)
          ( map-left-extension-pushout-trunc-span X h (map-trunc m f t))
          ( map-right-extension-pushout-trunc-span X h (map-trunc m g t)))
      ( coherence-extension-pushout-trunc-span-unit X h)

  cocone-extension-pushout-trunc-span :
    {l : Level} (X : Truncated-Type l m) →
    (pushout f g → type-Truncated-Type X) →
    cocone (map-trunc m f) (map-trunc m g) (type-Truncated-Type X)
  pr1 (cocone-extension-pushout-trunc-span X h) =
    map-left-extension-pushout-trunc-span X h
  pr1 (pr2 (cocone-extension-pushout-trunc-span X h)) =
    map-right-extension-pushout-trunc-span X h
  pr2 (pr2 (cocone-extension-pushout-trunc-span X h)) =
    coherence-extension-pushout-trunc-span X h

  map-extension-pushout-trunc-span :
    {l : Level} (X : Truncated-Type l m) →
    (pushout f g → type-Truncated-Type X) →
    pushout-trunc-span → type-Truncated-Type X
  map-extension-pushout-trunc-span X h =
    cogap
      ( map-trunc m f)
      ( map-trunc m g)
      ( cocone-extension-pushout-trunc-span X h)

  compute-inl-map-extension-pushout-trunc-span :
    {l : Level} (X : Truncated-Type l m)
    (h : pushout f g → type-Truncated-Type X) →
    map-extension-pushout-trunc-span X h ∘
    inl-pushout (map-trunc m f) (map-trunc m g) ~
    map-left-extension-pushout-trunc-span X h
  compute-inl-map-extension-pushout-trunc-span X h =
    compute-inl-cogap
      ( map-trunc m f)
      ( map-trunc m g)
      ( cocone-extension-pushout-trunc-span X h)

  compute-inr-map-extension-pushout-trunc-span :
    {l : Level} (X : Truncated-Type l m)
    (h : pushout f g → type-Truncated-Type X) →
    map-extension-pushout-trunc-span X h ∘
    inr-pushout (map-trunc m f) (map-trunc m g) ~
    map-right-extension-pushout-trunc-span X h
  compute-inr-map-extension-pushout-trunc-span X h =
    compute-inr-cogap
      ( map-trunc m f)
      ( map-trunc m g)
      ( cocone-extension-pushout-trunc-span X h)

  compute-glue-map-extension-pushout-trunc-span :
    {l : Level} (X : Truncated-Type l m)
    (h : pushout f g → type-Truncated-Type X) →
    statement-coherence-htpy-cocone
      ( map-trunc m f)
      ( map-trunc m g)
      ( cocone-map
        ( map-trunc m f)
        ( map-trunc m g)
        ( cocone-pushout (map-trunc m f) (map-trunc m g))
        ( map-extension-pushout-trunc-span X h))
      ( cocone-extension-pushout-trunc-span X h)
      ( compute-inl-map-extension-pushout-trunc-span X h)
      ( compute-inr-map-extension-pushout-trunc-span X h)
  compute-glue-map-extension-pushout-trunc-span X h =
    compute-glue-cogap
      ( map-trunc m f)
      ( map-trunc m g)
      ( cocone-extension-pushout-trunc-span X h)

  is-section-map-extension-precomp-pushout-trunc-span-inl :
    {l : Level} (X : Truncated-Type l m)
    (h : pushout f g → type-Truncated-Type X) (a : A) →
    ( map-extension-pushout-trunc-span X h ∘ map-pushout-trunc-span)
      ( inl-pushout f g a) ＝
    h (inl-pushout f g a)
  is-section-map-extension-precomp-pushout-trunc-span-inl X h a =
    ( ap
      ( map-extension-pushout-trunc-span X h)
      ( compute-inl-map-pushout-trunc-span a)) ∙
    ( compute-inl-map-extension-pushout-trunc-span X h (unit-trunc a)) ∙
    ( triangle-universal-property-trunc
      ( X)
      ( h ∘ inl-pushout f g)
      ( a))

  is-section-map-extension-precomp-pushout-trunc-span-inr :
    {l : Level} (X : Truncated-Type l m)
    (h : pushout f g → type-Truncated-Type X) (b : B) →
    ( map-extension-pushout-trunc-span X h ∘ map-pushout-trunc-span)
      ( inr-pushout f g b) ＝
    h (inr-pushout f g b)
  is-section-map-extension-precomp-pushout-trunc-span-inr X h b =
    ( ap
      ( map-extension-pushout-trunc-span X h)
      ( compute-inr-map-pushout-trunc-span b)) ∙
    ( compute-inr-map-extension-pushout-trunc-span X h (unit-trunc b)) ∙
    ( triangle-universal-property-trunc
      ( X)
      ( h ∘ inr-pushout f g)
      ( b))

  is-section-map-extension-precomp-pushout-trunc-span :
    {l : Level} (X : Truncated-Type l m) →
    ( precomp map-pushout-trunc-span (type-Truncated-Type X) ∘
      map-extension-pushout-trunc-span X) ~
    id
  is-section-map-extension-precomp-pushout-trunc-span X h =
    eq-htpy
      ( dependent-cogap f g
        ( is-section-map-extension-precomp-pushout-trunc-span-inl X h ,
          is-section-map-extension-precomp-pushout-trunc-span-inr X h ,
          λ s →
            map-compute-dependent-identification-eq-value-function
              ( map-extension-pushout-trunc-span X h ∘ map-pushout-trunc-span)
              ( h)
              ( glue-pushout f g s)
              ( is-section-map-extension-precomp-pushout-trunc-span-inl
                X h (f s))
              ( is-section-map-extension-precomp-pushout-trunc-span-inr
                X h (g s))
              ( coherence-square-is-section-map-extension-precomp-pushout-trunc-span
                X h s)))
    where
    coherence-square-is-section-map-extension-precomp-pushout-trunc-span :
      {l : Level} (X : Truncated-Type l m)
      (h : pushout f g → type-Truncated-Type X) (s : S) →
      ( ap (map-extension-pushout-trunc-span X h ∘ map-pushout-trunc-span)
          ( glue-pushout f g s) ∙
        is-section-map-extension-precomp-pushout-trunc-span-inr X h (g s)) ＝
      ( is-section-map-extension-precomp-pushout-trunc-span-inl X h (f s) ∙
        ap h (glue-pushout f g s))
    coherence-square-is-section-map-extension-precomp-pushout-trunc-span
      X h s =
      equational-reasoning
        ap (F ∘ M) p ∙ Rinr
        ＝ ap F (ap M p) ∙ Rinr
          by ap (_∙ Rinr) (ap-comp F M p)
        ＝
          ap F (ap M p) ∙
          ((ap F cinrM ∙ Finr (unit-trunc (g s))) ∙ triR)
          by refl
        ＝
          ap F (ap M p) ∙
          (ap F cinrM ∙ (Finr (unit-trunc (g s)) ∙ triR))
          by ap (ap F (ap M p) ∙_) (assoc (ap F cinrM) (Finr (unit-trunc (g s))) triR)
        ＝
          (ap F (ap M p) ∙ ap F cinrM) ∙
          (Finr (unit-trunc (g s)) ∙ triR)
          by inv (assoc (ap F (ap M p)) (ap F cinrM) (Finr (unit-trunc (g s)) ∙ triR))
        ＝
          ap F (ap M p ∙ cinrM) ∙
          (Finr (unit-trunc (g s)) ∙ triR)
          by ap (_∙ (Finr (unit-trunc (g s)) ∙ triR)) (inv (ap-concat F (ap M p) cinrM))
        ＝
          ap F (cinlM ∙ cohM) ∙
          (Finr (unit-trunc (g s)) ∙ triR)
          by ap (λ q → ap F q ∙ (Finr (unit-trunc (g s)) ∙ triR)) glueM
        ＝
          (ap F cinlM ∙ ap F cohM) ∙
          (Finr (unit-trunc (g s)) ∙ triR)
          by ap (_∙ (Finr (unit-trunc (g s)) ∙ triR)) (ap-concat F cinlM cohM)
        ＝
          ap F cinlM ∙
          (ap F cohM ∙ (Finr (unit-trunc (g s)) ∙ triR))
          by assoc (ap F cinlM) (ap F cohM) (Finr (unit-trunc (g s)) ∙ triR)
        ＝
          ap F cinlM ∙ (Finl (unit-trunc (f s)) ∙ (triL ∙ ap h p))
          by ap (ap F cinlM ∙_) coherence-extension
        ＝
          (ap F cinlM ∙ Finl (unit-trunc (f s))) ∙ (triL ∙ ap h p)
          by inv (assoc (ap F cinlM) (Finl (unit-trunc (f s))) (triL ∙ ap h p))
        ＝
          ((ap F cinlM ∙ Finl (unit-trunc (f s))) ∙ triL) ∙ ap h p
          by inv (assoc (ap F cinlM ∙ Finl (unit-trunc (f s))) triL (ap h p))
      where
      M = map-pushout-trunc-span

      F = map-extension-pushout-trunc-span X h

      p = glue-pushout f g s

      inlT = inl-pushout (map-trunc m f) (map-trunc m g)

      inrT = inr-pushout (map-trunc m f) (map-trunc m g)

      leftExt = map-left-extension-pushout-trunc-span X h

      rightExt = map-right-extension-pushout-trunc-span X h

      Finl = compute-inl-map-extension-pushout-trunc-span X h

      Finr = compute-inr-map-extension-pushout-trunc-span X h

      cinlM = compute-inl-map-pushout-trunc-span (f s)

      cinrM = compute-inr-map-pushout-trunc-span (g s)

      natf = naturality-unit-trunc m f s

      natg = naturality-unit-trunc m g s

      glueT = glue-pushout (map-trunc m f) (map-trunc m g) (unit-trunc s)

      cohM =
        pr2 (pr2 cocone-pushout-trunc-span) s

      glueM :
        ap M p ∙ cinrM ＝ cinlM ∙ cohM
      glueM = compute-glue-map-pushout-trunc-span s

      triL =
        triangle-universal-property-trunc
          ( X)
          ( h ∘ inl-pushout f g)
          ( f s)

      triR =
        triangle-universal-property-trunc
          ( X)
          ( h ∘ inr-pushout f g)
          ( g s)

      Rinr =
        is-section-map-extension-precomp-pushout-trunc-span-inr X h (g s)

      FinlT = Finl (map-trunc m f (unit-trunc s))

      FinrT = Finr (map-trunc m g (unit-trunc s))

      leftNat = ap leftExt natf

      rightNat = ap rightExt natg

      apInlNat = ap inlT natf

      apInrNat = ap inrT natg

      cohExt = coherence-extension-pushout-trunc-span X h (unit-trunc s)

      cohExt-unit :
        cohExt ＝ coherence-extension-pushout-trunc-span-unit X h s
      cohExt-unit =
        htpy-dependent-universal-property-trunc
          ( λ t →
            Id-Truncated-Type'
              ( X)
              ( map-left-extension-pushout-trunc-span X h
                ( map-trunc m f t))
              ( map-right-extension-pushout-trunc-span X h
                ( map-trunc m g t)))
          ( coherence-extension-pushout-trunc-span-unit X h)
          ( s)

      glueF :
        ap F glueT ∙ FinrT ＝ FinlT ∙ cohExt
      glueF =
        compute-glue-map-extension-pushout-trunc-span X h (unit-trunc s)

      right-naturality-Finr :
        ap F apInrNat ∙ Finr (unit-trunc (g s)) ＝
        FinrT ∙ rightNat
      right-naturality-Finr =
        ( ap (_∙ Finr (unit-trunc (g s))) (inv (ap-comp F inrT natg))) ∙
        ( inv (nat-htpy Finr natg))

      left-naturality-Finl :
        ap F (inv apInlNat) ∙ FinlT ＝
        Finl (unit-trunc (f s)) ∙ inv leftNat
      left-naturality-Finl =
        equational-reasoning
          ap F (inv apInlNat) ∙ FinlT
          ＝ inv (ap F apInlNat) ∙ FinlT
            by ap (_∙ FinlT) (ap-inv F apInlNat)
          ＝ inv q ∙ FinlT
            by ap (λ r → inv r ∙ FinlT) (inv (ap-comp F inlT natf))
          ＝ inv q ∙ ((q ∙ Finl (unit-trunc (f s))) ∙ inv leftNat)
            by
            ap (inv q ∙_)
              ( right-transpose-eq-concat
                ( FinlT)
                ( leftNat)
                ( q ∙ Finl (unit-trunc (f s)))
                ( nat-htpy Finl natf))
          ＝ inv q ∙ (q ∙ (Finl (unit-trunc (f s)) ∙ inv leftNat))
            by ap (inv q ∙_) (assoc q (Finl (unit-trunc (f s))) (inv leftNat))
          ＝ (inv q ∙ q) ∙ (Finl (unit-trunc (f s)) ∙ inv leftNat)
            by inv (assoc (inv q) q (Finl (unit-trunc (f s)) ∙ inv leftNat))
          ＝ refl ∙ (Finl (unit-trunc (f s)) ∙ inv leftNat)
            by ap (_∙ (Finl (unit-trunc (f s)) ∙ inv leftNat)) (left-inv q)
          ＝ Finl (unit-trunc (f s)) ∙ inv leftNat
            by left-unit
        where
        q = ap (F ∘ inlT) natf

      cancel-extension-unit :
        inv leftNat ∙ (cohExt ∙ (rightNat ∙ triR)) ＝ triL ∙ ap h p
      cancel-extension-unit =
        equational-reasoning
          inv leftNat ∙ (cohExt ∙ (rightNat ∙ triR))
          ＝ inv leftNat ∙ ((C ∙ inv rightNat) ∙ (rightNat ∙ triR))
            by
            ap
              ( λ q → inv leftNat ∙ (q ∙ (rightNat ∙ triR)))
              ( cohExt-unit)
          ＝ inv leftNat ∙ (C ∙ (inv rightNat ∙ (rightNat ∙ triR)))
            by ap (inv leftNat ∙_) (assoc C (inv rightNat) (rightNat ∙ triR))
          ＝ inv leftNat ∙ (C ∙ ((inv rightNat ∙ rightNat) ∙ triR))
            by
            ap
              ( λ q → inv leftNat ∙ (C ∙ q))
              ( inv (assoc (inv rightNat) rightNat triR))
          ＝ inv leftNat ∙ (C ∙ (refl ∙ triR))
            by
            ap
              ( λ q → inv leftNat ∙ (C ∙ (q ∙ triR)))
              ( left-inv rightNat)
          ＝ inv leftNat ∙ (C ∙ triR)
            by ap (λ q → inv leftNat ∙ (C ∙ q)) left-unit
          ＝ inv leftNat ∙ ((D ∙ inv triR) ∙ triR)
            by refl
          ＝ inv leftNat ∙ (D ∙ (inv triR ∙ triR))
            by ap (inv leftNat ∙_) (assoc D (inv triR) triR)
          ＝ inv leftNat ∙ (D ∙ refl)
            by ap (λ q → inv leftNat ∙ (D ∙ q)) (left-inv triR)
          ＝ inv leftNat ∙ D
            by ap (inv leftNat ∙_) right-unit
          ＝ (inv leftNat ∙ (leftNat ∙ triL)) ∙ ap h p
            by inv (assoc (inv leftNat) (leftNat ∙ triL) (ap h p))
          ＝ ((inv leftNat ∙ leftNat) ∙ triL) ∙ ap h p
            by ap (_∙ ap h p) (inv (assoc (inv leftNat) leftNat triL))
          ＝ (refl ∙ triL) ∙ ap h p
            by ap (λ q → (q ∙ triL) ∙ ap h p) (left-inv leftNat)
          ＝ triL ∙ ap h p
            by ap (_∙ ap h p) left-unit
        where
        D = (leftNat ∙ triL) ∙ ap h p

        C = D ∙ inv triR
      coherence-extension :
        ap F cohM ∙ (Finr (unit-trunc (g s)) ∙ triR) ＝
        Finl (unit-trunc (f s)) ∙ (triL ∙ ap h p)
      coherence-extension =
        equational-reasoning
          ap F cohM ∙ (Finr (unit-trunc (g s)) ∙ triR)
          ＝
            ap F ((inv apInlNat ∙ glueT) ∙ apInrNat) ∙
            (Finr (unit-trunc (g s)) ∙ triR)
            by refl
          ＝
            (ap F (inv apInlNat ∙ glueT) ∙ ap F apInrNat) ∙
            (Finr (unit-trunc (g s)) ∙ triR)
            by
            ap
              ( _∙ (Finr (unit-trunc (g s)) ∙ triR))
              ( ap-concat F (inv apInlNat ∙ glueT) apInrNat)
          ＝
            ap F (inv apInlNat ∙ glueT) ∙
            (ap F apInrNat ∙ (Finr (unit-trunc (g s)) ∙ triR))
            by
            assoc
              ( ap F (inv apInlNat ∙ glueT))
              ( ap F apInrNat)
              ( Finr (unit-trunc (g s)) ∙ triR)
          ＝
            ap F (inv apInlNat ∙ glueT) ∙
            ((ap F apInrNat ∙ Finr (unit-trunc (g s))) ∙ triR)
            by
            ap
              ( ap F (inv apInlNat ∙ glueT) ∙_)
              ( inv (assoc (ap F apInrNat) (Finr (unit-trunc (g s))) triR))
          ＝
            ap F (inv apInlNat ∙ glueT) ∙ ((FinrT ∙ rightNat) ∙ triR)
            by
            ap
              ( λ q → ap F (inv apInlNat ∙ glueT) ∙ (q ∙ triR))
              ( right-naturality-Finr)
          ＝
            ap F (inv apInlNat ∙ glueT) ∙
            (FinrT ∙ (rightNat ∙ triR))
            by
            ap
              ( ap F (inv apInlNat ∙ glueT) ∙_)
              ( assoc FinrT rightNat triR)
          ＝
            (ap F (inv apInlNat) ∙ ap F glueT) ∙
            (FinrT ∙ (rightNat ∙ triR))
            by
            ap
              ( _∙ (FinrT ∙ (rightNat ∙ triR)))
              ( ap-concat F (inv apInlNat) glueT)
          ＝
            ap F (inv apInlNat) ∙
            (ap F glueT ∙ (FinrT ∙ (rightNat ∙ triR)))
            by
            assoc
              ( ap F (inv apInlNat))
              ( ap F glueT)
              ( FinrT ∙ (rightNat ∙ triR))
          ＝
            ap F (inv apInlNat) ∙
            ((ap F glueT ∙ FinrT) ∙ (rightNat ∙ triR))
            by
            ap
              ( ap F (inv apInlNat) ∙_)
              ( inv (assoc (ap F glueT) FinrT (rightNat ∙ triR)))
          ＝
            ap F (inv apInlNat) ∙
            ((FinlT ∙ cohExt) ∙ (rightNat ∙ triR))
            by
            ap
              ( λ q → ap F (inv apInlNat) ∙ (q ∙ (rightNat ∙ triR)))
              ( glueF)
          ＝
            ap F (inv apInlNat) ∙
            (FinlT ∙ (cohExt ∙ (rightNat ∙ triR)))
            by
            ap
              ( ap F (inv apInlNat) ∙_)
              ( assoc FinlT cohExt (rightNat ∙ triR))
          ＝
            (ap F (inv apInlNat) ∙ FinlT) ∙
            (cohExt ∙ (rightNat ∙ triR))
            by
            inv
              ( assoc
                ( ap F (inv apInlNat))
                ( FinlT)
                ( cohExt ∙ (rightNat ∙ triR)))
          ＝
            (Finl (unit-trunc (f s)) ∙ inv leftNat) ∙
            (cohExt ∙ (rightNat ∙ triR))
            by
            ap
              ( _∙ (cohExt ∙ (rightNat ∙ triR)))
              ( left-naturality-Finl)
          ＝
            Finl (unit-trunc (f s)) ∙
            (inv leftNat ∙ (cohExt ∙ (rightNat ∙ triR)))
            by
            assoc
              ( Finl (unit-trunc (f s)))
              ( inv leftNat)
              ( cohExt ∙ (rightNat ∙ triR))
          ＝ Finl (unit-trunc (f s)) ∙ (triL ∙ ap h p)
            by ap (Finl (unit-trunc (f s)) ∙_) cancel-extension-unit


  left-htpy-map-extension-precomp-pushout-trunc-span :
    {l : Level} (X : Truncated-Type l m)
    (h : pushout-trunc-span → type-Truncated-Type X) →
    map-left-extension-pushout-trunc-span X (h ∘ map-pushout-trunc-span) ~
    h ∘ inl-pushout (map-trunc m f) (map-trunc m g)
  left-htpy-map-extension-precomp-pushout-trunc-span X h =
    function-dependent-universal-property-trunc
      ( λ t →
        Id-Truncated-Type'
          ( X)
          ( map-left-extension-pushout-trunc-span
            ( X)
            ( h ∘ map-pushout-trunc-span)
            ( t))
          ( h (inl-pushout (map-trunc m f) (map-trunc m g) t)))
      ( λ a →
        ( triangle-universal-property-trunc
          ( X)
          ( h ∘ map-pushout-trunc-span ∘ inl-pushout f g)
          ( a)) ∙
        ( ap h (compute-inl-map-pushout-trunc-span a)))

  right-htpy-map-extension-precomp-pushout-trunc-span :
    {l : Level} (X : Truncated-Type l m)
    (h : pushout-trunc-span → type-Truncated-Type X) →
    map-right-extension-pushout-trunc-span X (h ∘ map-pushout-trunc-span) ~
    h ∘ inr-pushout (map-trunc m f) (map-trunc m g)
  right-htpy-map-extension-precomp-pushout-trunc-span X h =
    function-dependent-universal-property-trunc
      ( λ t →
        Id-Truncated-Type'
          ( X)
          ( map-right-extension-pushout-trunc-span
            ( X)
            ( h ∘ map-pushout-trunc-span)
            ( t))
          ( h (inr-pushout (map-trunc m f) (map-trunc m g) t)))
      ( λ b →
        ( triangle-universal-property-trunc
          ( X)
          ( h ∘ map-pushout-trunc-span ∘ inr-pushout f g)
          ( b)) ∙
        ( ap h (compute-inr-map-pushout-trunc-span b)))

  is-retraction-map-extension-precomp-pushout-trunc-span-inl :
    {l : Level} (X : Truncated-Type l m)
    (h : pushout-trunc-span → type-Truncated-Type X)
    (a : type-trunc m A) →
    map-extension-pushout-trunc-span X (h ∘ map-pushout-trunc-span)
      ( inl-pushout (map-trunc m f) (map-trunc m g) a) ＝
    h (inl-pushout (map-trunc m f) (map-trunc m g) a)
  is-retraction-map-extension-precomp-pushout-trunc-span-inl X h a =
    ( compute-inl-map-extension-pushout-trunc-span
      ( X)
      ( h ∘ map-pushout-trunc-span)
      ( a)) ∙
    ( left-htpy-map-extension-precomp-pushout-trunc-span X h a)

  is-retraction-map-extension-precomp-pushout-trunc-span-inr :
    {l : Level} (X : Truncated-Type l m)
    (h : pushout-trunc-span → type-Truncated-Type X)
    (b : type-trunc m B) →
    map-extension-pushout-trunc-span X (h ∘ map-pushout-trunc-span)
      ( inr-pushout (map-trunc m f) (map-trunc m g) b) ＝
    h (inr-pushout (map-trunc m f) (map-trunc m g) b)
  is-retraction-map-extension-precomp-pushout-trunc-span-inr X h b =
    ( compute-inr-map-extension-pushout-trunc-span
      ( X)
      ( h ∘ map-pushout-trunc-span)
      ( b)) ∙
    ( right-htpy-map-extension-precomp-pushout-trunc-span X h b)

  is-retraction-map-extension-precomp-pushout-trunc-span :
    {l : Level} (X : Truncated-Type l m) →
    ( map-extension-pushout-trunc-span X ∘
      precomp map-pushout-trunc-span (type-Truncated-Type X)) ~
    id
  is-retraction-map-extension-precomp-pushout-trunc-span X h =
    eq-htpy
      ( dependent-cogap
        ( map-trunc m f)
        ( map-trunc m g)
        ( is-retraction-map-extension-precomp-pushout-trunc-span-inl X h ,
          is-retraction-map-extension-precomp-pushout-trunc-span-inr X h ,
          λ t →
            map-compute-dependent-identification-eq-value-function
              ( map-extension-pushout-trunc-span X
                ( h ∘ map-pushout-trunc-span))
              ( h)
              ( glue-pushout (map-trunc m f) (map-trunc m g) t)
              ( is-retraction-map-extension-precomp-pushout-trunc-span-inl
                X h (map-trunc m f t))
              ( is-retraction-map-extension-precomp-pushout-trunc-span-inr
                X h (map-trunc m g t))
              ( coherence-square-is-retraction-map-extension-precomp-pushout-trunc-span
                X h t)))
    where
    coherence-square-is-retraction-map-extension-precomp-pushout-trunc-span-unit :
      {l : Level} (X : Truncated-Type l m)
      (h : pushout-trunc-span → type-Truncated-Type X)
      (s : S) →
      ( ap
        ( map-extension-pushout-trunc-span X
          ( h ∘ map-pushout-trunc-span))
        ( glue-pushout
          ( map-trunc m f)
          ( map-trunc m g)
          ( unit-trunc s)) ∙
        is-retraction-map-extension-precomp-pushout-trunc-span-inr
          X h (map-trunc m g (unit-trunc s))) ＝
      ( is-retraction-map-extension-precomp-pushout-trunc-span-inl
        X h (map-trunc m f (unit-trunc s)) ∙
        ap h
          ( glue-pushout
            ( map-trunc m f)
            ( map-trunc m g)
            ( unit-trunc s)))
    coherence-square-is-retraction-map-extension-precomp-pushout-trunc-span-unit
      X h s =
      equational-reasoning
        ap F glueT ∙ RinrT
        ＝ ap F glueT ∙ (FinrT ∙ Rmapg)
          by refl
        ＝ (ap F glueT ∙ FinrT) ∙ Rmapg
          by inv (assoc (ap F glueT) FinrT Rmapg)
        ＝ (FinlT ∙ cohExt) ∙ Rmapg
          by ap (_∙ Rmapg) glueF
        ＝ FinlT ∙ (cohExt ∙ Rmapg)
          by assoc FinlT cohExt Rmapg
        ＝ FinlT ∙ (Lmapf ∙ ap h glueT)
          by ap (FinlT ∙_) cancel-retraction-unit
        ＝ (FinlT ∙ Lmapf) ∙ ap h glueT
          by inv (assoc FinlT Lmapf (ap h glueT))
      where
      M = map-pushout-trunc-span

      F = map-extension-pushout-trunc-span X (h ∘ M)

      p = glue-pushout f g s

      inlT = inl-pushout (map-trunc m f) (map-trunc m g)

      inrT = inr-pushout (map-trunc m f) (map-trunc m g)

      leftExt = map-left-extension-pushout-trunc-span X (h ∘ M)

      rightExt = map-right-extension-pushout-trunc-span X (h ∘ M)

      Finl = compute-inl-map-extension-pushout-trunc-span X (h ∘ M)

      Finr = compute-inr-map-extension-pushout-trunc-span X (h ∘ M)

      cinlM = compute-inl-map-pushout-trunc-span (f s)

      cinrM = compute-inr-map-pushout-trunc-span (g s)

      natf = naturality-unit-trunc m f s

      natg = naturality-unit-trunc m g s

      glueT = glue-pushout (map-trunc m f) (map-trunc m g) (unit-trunc s)

      cohExt =
        coherence-extension-pushout-trunc-span X (h ∘ M) (unit-trunc s)

      FinlT = Finl (map-trunc m f (unit-trunc s))

      FinrT = Finr (map-trunc m g (unit-trunc s))

      glueF :
        ap F glueT ∙ FinrT ＝ FinlT ∙ cohExt
      glueF =
        compute-glue-map-extension-pushout-trunc-span
          ( X)
          ( h ∘ M)
          ( unit-trunc s)

      L = left-htpy-map-extension-precomp-pushout-trunc-span X h

      R = right-htpy-map-extension-precomp-pushout-trunc-span X h

      Lmapf = L (map-trunc m f (unit-trunc s))

      Rmapg = R (map-trunc m g (unit-trunc s))

      Lunit = L (unit-trunc (f s))

      Runit = R (unit-trunc (g s))

      RinrT =
        is-retraction-map-extension-precomp-pushout-trunc-span-inr
          X h (map-trunc m g (unit-trunc s))

      leftNat = ap leftExt natf

      rightNat = ap rightExt natg

      apInlNat = ap inlT natf

      apInrNat = ap inrT natg

      hInlNat = ap (h ∘ inlT) natf

      hInrNat = ap (h ∘ inrT) natg

      triL =
        triangle-universal-property-trunc
          ( X)
          ( h ∘ M ∘ inl-pushout f g)
          ( f s)

      triR =
        triangle-universal-property-trunc
          ( X)
          ( h ∘ M ∘ inr-pushout f g)
          ( g s)

      cohM =
        pr2 (pr2 cocone-pushout-trunc-span) s

      glueM :
        ap M p ∙ cinrM ＝ cinlM ∙ cohM
      glueM = compute-glue-map-pushout-trunc-span s

      cohExt-unit :
        cohExt ＝ coherence-extension-pushout-trunc-span-unit X (h ∘ M) s
      cohExt-unit =
        htpy-dependent-universal-property-trunc
          ( λ t →
            Id-Truncated-Type'
              ( X)
              ( map-left-extension-pushout-trunc-span X (h ∘ M)
                ( map-trunc m f t))
              ( map-right-extension-pushout-trunc-span X (h ∘ M)
                ( map-trunc m g t)))
          ( coherence-extension-pushout-trunc-span-unit X (h ∘ M))
          ( s)

      left-htpy-unit :
        L (unit-trunc (f s)) ＝ triL ∙ ap h cinlM
      left-htpy-unit =
        htpy-dependent-universal-property-trunc
          ( λ a →
            Id-Truncated-Type'
              ( X)
              ( map-left-extension-pushout-trunc-span X (h ∘ M)
                ( a))
              ( h (inlT a)))
          ( λ a →
            ( triangle-universal-property-trunc
              ( X)
              ( h ∘ M ∘ inl-pushout f g)
              ( a)) ∙
            ( ap h (compute-inl-map-pushout-trunc-span a)))
          ( f s)

      right-htpy-unit :
        R (unit-trunc (g s)) ＝ triR ∙ ap h cinrM
      right-htpy-unit =
        htpy-dependent-universal-property-trunc
          ( λ b →
            Id-Truncated-Type'
              ( X)
              ( map-right-extension-pushout-trunc-span X (h ∘ M)
                ( b))
              ( h (inrT b)))
          ( λ b →
            ( triangle-universal-property-trunc
              ( X)
              ( h ∘ M ∘ inr-pushout f g)
              ( b)) ∙
            ( ap h (compute-inr-map-pushout-trunc-span b)))
          ( g s)

      right-naturality-R :
        inv rightNat ∙ Rmapg ＝ (triR ∙ ap h cinrM) ∙ inv hInrNat
      right-naturality-R =
        equational-reasoning
          inv rightNat ∙ Rmapg
          ＝ inv rightNat ∙ ((rightNat ∙ Runit) ∙ inv hInrNat)
            by
            ap
              ( inv rightNat ∙_)
              ( right-transpose-eq-concat
                ( Rmapg)
                ( hInrNat)
                ( rightNat ∙ Runit)
                ( nat-htpy R natg))
          ＝ (inv rightNat ∙ (rightNat ∙ Runit)) ∙ inv hInrNat
            by inv (assoc (inv rightNat) (rightNat ∙ Runit) (inv hInrNat))
          ＝ ((inv rightNat ∙ rightNat) ∙ Runit) ∙ inv hInrNat
            by ap (_∙ inv hInrNat) (inv (assoc (inv rightNat) rightNat Runit))
          ＝ (refl ∙ Runit) ∙ inv hInrNat
            by ap (λ q → (q ∙ Runit) ∙ inv hInrNat) (left-inv rightNat)
          ＝ Runit ∙ inv hInrNat
            by ap (_∙ inv hInrNat) left-unit
          ＝ (triR ∙ ap h cinrM) ∙ inv hInrNat
            by ap (_∙ inv hInrNat) right-htpy-unit

      left-naturality-L :
        ((leftNat ∙ triL) ∙ ap h cinlM) ∙ inv hInlNat ＝ Lmapf
      left-naturality-L =
        equational-reasoning
          ((leftNat ∙ triL) ∙ ap h cinlM) ∙ inv hInlNat
          ＝ (leftNat ∙ (triL ∙ ap h cinlM)) ∙ inv hInlNat
            by ap (_∙ inv hInlNat) (assoc leftNat triL (ap h cinlM))
          ＝ (leftNat ∙ Lunit) ∙ inv hInlNat
            by ap (λ q → (leftNat ∙ q) ∙ inv hInlNat) (inv left-htpy-unit)
          ＝ Lmapf
            by
            inv
              ( right-transpose-eq-concat
                ( Lmapf)
                ( hInlNat)
                ( leftNat ∙ Lunit)
                ( nat-htpy L natf))

      map-glue-retraction :
        ap (h ∘ M) p ∙ ap h cinrM ＝ ap h cinlM ∙ ap h cohM
      map-glue-retraction =
        equational-reasoning
          ap (h ∘ M) p ∙ ap h cinrM
          ＝ ap h (ap M p) ∙ ap h cinrM
            by ap (_∙ ap h cinrM) (ap-comp h M p)
          ＝ ap h (ap M p ∙ cinrM)
            by inv (ap-concat h (ap M p) cinrM)
          ＝ ap h (cinlM ∙ cohM)
            by ap (ap h) glueM
          ＝ ap h cinlM ∙ ap h cohM
            by ap-concat h cinlM cohM

      cancel-coherence-map :
        ap h cohM ∙ inv hInrNat ＝ inv hInlNat ∙ ap h glueT
      cancel-coherence-map =
        equational-reasoning
          ap h cohM ∙ inv hInrNat
          ＝ ap h ((inv apInlNat ∙ glueT) ∙ apInrNat) ∙ inv hInrNat
            by refl
          ＝
            (ap h (inv apInlNat ∙ glueT) ∙ ap h apInrNat) ∙
            inv hInrNat
            by
            ap
              ( _∙ inv hInrNat)
              ( ap-concat h (inv apInlNat ∙ glueT) apInrNat)
          ＝
            ap h (inv apInlNat ∙ glueT) ∙
            (ap h apInrNat ∙ inv hInrNat)
            by
            assoc
              ( ap h (inv apInlNat ∙ glueT))
              ( ap h apInrNat)
              ( inv hInrNat)
          ＝
            ap h (inv apInlNat ∙ glueT) ∙
            (hInrNat ∙ inv hInrNat)
            by
            ap
              ( λ q → ap h (inv apInlNat ∙ glueT) ∙ (q ∙ inv hInrNat))
              ( inv (ap-comp h inrT natg))
          ＝ ap h (inv apInlNat ∙ glueT) ∙ refl
            by
            ap
              ( ap h (inv apInlNat ∙ glueT) ∙_)
              ( right-inv hInrNat)
          ＝ ap h (inv apInlNat ∙ glueT)
            by right-unit
          ＝ ap h (inv apInlNat) ∙ ap h glueT
            by ap-concat h (inv apInlNat) glueT
          ＝ inv (ap h apInlNat) ∙ ap h glueT
            by ap (_∙ ap h glueT) (ap-inv h apInlNat)
          ＝ inv hInlNat ∙ ap h glueT
            by
            ap
              ( λ q → inv q ∙ ap h glueT)
              ( inv (ap-comp h inlT natf))

      cancel-retraction-unit :
        cohExt ∙ Rmapg ＝ Lmapf ∙ ap h glueT
      cancel-retraction-unit =
        equational-reasoning
          cohExt ∙ Rmapg
          ＝ (C ∙ inv rightNat) ∙ Rmapg
            by ap (_∙ Rmapg) cohExt-unit
          ＝ C ∙ (inv rightNat ∙ Rmapg)
            by assoc C (inv rightNat) Rmapg
          ＝ C ∙ ((triR ∙ ap h cinrM) ∙ inv hInrNat)
            by ap (C ∙_) right-naturality-R
          ＝ (D ∙ inv triR) ∙ ((triR ∙ ap h cinrM) ∙ inv hInrNat)
            by refl
          ＝ D ∙ (inv triR ∙ ((triR ∙ ap h cinrM) ∙ inv hInrNat))
            by assoc D (inv triR) ((triR ∙ ap h cinrM) ∙ inv hInrNat)
          ＝ D ∙ ((inv triR ∙ (triR ∙ ap h cinrM)) ∙ inv hInrNat)
            by
            ap
              ( D ∙_)
              ( inv (assoc (inv triR) (triR ∙ ap h cinrM) (inv hInrNat)))
          ＝ D ∙ (((inv triR ∙ triR) ∙ ap h cinrM) ∙ inv hInrNat)
            by
            ap
              ( λ q → D ∙ (q ∙ inv hInrNat))
              ( inv (assoc (inv triR) triR (ap h cinrM)))
          ＝ D ∙ ((refl ∙ ap h cinrM) ∙ inv hInrNat)
            by
            ap
              ( λ q → D ∙ ((q ∙ ap h cinrM) ∙ inv hInrNat))
              ( left-inv triR)
          ＝ D ∙ (ap h cinrM ∙ inv hInrNat)
            by
            ap
              ( λ q → D ∙ (q ∙ inv hInrNat))
              ( left-unit)
          ＝
            ((leftNat ∙ triL) ∙ ap (h ∘ M) p) ∙
            (ap h cinrM ∙ inv hInrNat)
            by refl
          ＝
            (leftNat ∙ triL) ∙
            (ap (h ∘ M) p ∙ (ap h cinrM ∙ inv hInrNat))
            by
            assoc
              ( leftNat ∙ triL)
              ( ap (h ∘ M) p)
              ( ap h cinrM ∙ inv hInrNat)
          ＝
            (leftNat ∙ triL) ∙
            ((ap (h ∘ M) p ∙ ap h cinrM) ∙ inv hInrNat)
            by
            ap
              ( (leftNat ∙ triL) ∙_)
              ( inv (assoc (ap (h ∘ M) p) (ap h cinrM) (inv hInrNat)))
          ＝
            (leftNat ∙ triL) ∙
            ((ap h cinlM ∙ ap h cohM) ∙ inv hInrNat)
            by
            ap
              ( λ q → (leftNat ∙ triL) ∙ (q ∙ inv hInrNat))
              ( map-glue-retraction)
          ＝
            (leftNat ∙ triL) ∙
            (ap h cinlM ∙ (ap h cohM ∙ inv hInrNat))
            by
            ap
              ( (leftNat ∙ triL) ∙_)
              ( assoc (ap h cinlM) (ap h cohM) (inv hInrNat))
          ＝
            (leftNat ∙ triL) ∙
            (ap h cinlM ∙ (inv hInlNat ∙ ap h glueT))
            by
            ap
              ( λ q → (leftNat ∙ triL) ∙ (ap h cinlM ∙ q))
              ( cancel-coherence-map)
          ＝
            (leftNat ∙ triL) ∙
            ((ap h cinlM ∙ inv hInlNat) ∙ ap h glueT)
            by
            ap
              ( (leftNat ∙ triL) ∙_)
              ( inv (assoc (ap h cinlM) (inv hInlNat) (ap h glueT)))
          ＝
            ((leftNat ∙ triL) ∙ (ap h cinlM ∙ inv hInlNat)) ∙
            ap h glueT
            by
            inv
              ( assoc
                ( leftNat ∙ triL)
                ( ap h cinlM ∙ inv hInlNat)
                ( ap h glueT))
          ＝
            (((leftNat ∙ triL) ∙ ap h cinlM) ∙ inv hInlNat) ∙
            ap h glueT
            by
            ap
              ( _∙ ap h glueT)
              ( inv (assoc (leftNat ∙ triL) (ap h cinlM) (inv hInlNat)))
          ＝ Lmapf ∙ ap h glueT
            by ap (_∙ ap h glueT) left-naturality-L
        where
        D = (leftNat ∙ triL) ∙ ap (h ∘ M) p

        C = D ∙ inv triR

    coherence-square-is-retraction-map-extension-precomp-pushout-trunc-span :
      {l : Level} (X : Truncated-Type l m)
      (h : pushout-trunc-span → type-Truncated-Type X)
      (t : type-trunc m S) →
      ( ap
        ( map-extension-pushout-trunc-span X
          ( h ∘ map-pushout-trunc-span))
        ( glue-pushout (map-trunc m f) (map-trunc m g) t) ∙
        is-retraction-map-extension-precomp-pushout-trunc-span-inr
          X h (map-trunc m g t)) ＝
      ( is-retraction-map-extension-precomp-pushout-trunc-span-inl
        X h (map-trunc m f t) ∙
        ap h (glue-pushout (map-trunc m f) (map-trunc m g) t))
    coherence-square-is-retraction-map-extension-precomp-pushout-trunc-span
      X h =
      function-dependent-universal-property-trunc
        ( λ t →
          Id-Truncated-Type'
            ( Id-Truncated-Type'
              ( X)
              ( map-extension-pushout-trunc-span X
                ( h ∘ map-pushout-trunc-span)
                ( inl-pushout (map-trunc m f) (map-trunc m g)
                  ( map-trunc m f t)))
              ( h
                ( inr-pushout (map-trunc m f) (map-trunc m g)
                  ( map-trunc m g t))))
            ( ap
              ( map-extension-pushout-trunc-span X
                ( h ∘ map-pushout-trunc-span))
              ( glue-pushout (map-trunc m f) (map-trunc m g) t) ∙
              is-retraction-map-extension-precomp-pushout-trunc-span-inr
                X h (map-trunc m g t))
            ( is-retraction-map-extension-precomp-pushout-trunc-span-inl
              X h (map-trunc m f t) ∙
              ap h (glue-pushout (map-trunc m f) (map-trunc m g) t)))
        ( coherence-square-is-retraction-map-extension-precomp-pushout-trunc-span-unit
          X h)


  is-truncation-equivalence-map-pushout-trunc-span :
    is-truncation-equivalence m map-pushout-trunc-span
  is-truncation-equivalence-map-pushout-trunc-span =
    is-truncation-equivalence-is-equiv-precomp
      ( λ l X →
        is-equiv-is-invertible
          ( map-extension-pushout-trunc-span X)
          ( is-section-map-extension-precomp-pushout-trunc-span X)
          ( is-retraction-map-extension-precomp-pushout-trunc-span X))

  truncation-equivalence-map-pushout-trunc-span :
    truncation-equivalence m (pushout f g) pushout-trunc-span
  pr1 truncation-equivalence-map-pushout-trunc-span =
    map-pushout-trunc-span
  pr2 truncation-equivalence-map-pushout-trunc-span =
    is-truncation-equivalence-map-pushout-trunc-span

  equiv-trunc-pushout-pushout-trunc-span :
    type-trunc m (pushout f g) ≃ type-trunc m pushout-trunc-span
  equiv-trunc-pushout-pushout-trunc-span =
    equiv-trunc-truncation-equivalence
      ( truncation-equivalence-map-pushout-trunc-span)
```

## Pushouts along equivalences

```agda
module _
  {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (is-equiv-f : is-equiv f)
  where

  equiv-left-map-pushout-is-equiv : S ≃ A
  pr1 equiv-left-map-pushout-is-equiv = f
  pr2 equiv-left-map-pushout-is-equiv = is-equiv-f

  cocone-inv-inr-pushout-is-equiv-left-map : cocone f g B
  pr1 cocone-inv-inr-pushout-is-equiv-left-map =
    g ∘ map-inv-equiv equiv-left-map-pushout-is-equiv
  pr1 (pr2 cocone-inv-inr-pushout-is-equiv-left-map) = id
  pr2 (pr2 cocone-inv-inr-pushout-is-equiv-left-map) s =
    ap g (is-retraction-map-inv-equiv equiv-left-map-pushout-is-equiv s)

  map-inv-inr-pushout-is-equiv-left-map : pushout f g → B
  map-inv-inr-pushout-is-equiv-left-map =
    cogap f g cocone-inv-inr-pushout-is-equiv-left-map

  is-retraction-map-inv-inr-pushout-is-equiv-left-map :
    ( map-inv-inr-pushout-is-equiv-left-map ∘ inr-pushout f g) ~ id
  is-retraction-map-inv-inr-pushout-is-equiv-left-map =
    compute-inr-cogap f g cocone-inv-inr-pushout-is-equiv-left-map

  coherence-glue-is-section-map-inv-inr-pushout-is-equiv-left-map :
    (s : S) →
    let
      e = equiv-left-map-pushout-is-equiv
      invf = map-inv-equiv e
      ret = is-retraction-map-inv-equiv e s
      sec = is-section-map-inv-equiv e (f s)
      G = glue-pushout f g (invf (f s))
      p = glue-pushout f g s
    in
      ( inv G ∙ ap (inl-pushout f g) sec) ∙ p ＝
      ap (inr-pushout f g) (ap g ret)
  coherence-glue-is-section-map-inv-inr-pushout-is-equiv-left-map s =
    equational-reasoning
      (inv G ∙ ap inl sec) ∙ p
      ＝ inv G ∙ (ap inl sec ∙ p)
        by assoc (inv G) (ap inl sec) p
      ＝ inv G ∙ (ap inl (ap f ret) ∙ p)
        by ap (λ q → inv G ∙ (ap inl q ∙ p)) coh
      ＝ inv G ∙ (ap (inl ∘ f) ret ∙ p)
        by ap (λ q → inv G ∙ (q ∙ p)) (inv (ap-comp inl f ret))
      ＝ inv G ∙ (G ∙ ap (inr ∘ g) ret)
        by ap (inv G ∙_) (inv (nat-htpy (glue-pushout f g) ret))
      ＝ inv G ∙ (G ∙ ap inr (ap g ret))
        by ap (λ q → inv G ∙ (G ∙ q)) (ap-comp inr g ret)
      ＝ (inv G ∙ G) ∙ ap inr (ap g ret)
        by inv (assoc (inv G) G (ap inr (ap g ret)))
      ＝ refl ∙ ap inr (ap g ret)
        by ap (_∙ ap inr (ap g ret)) (left-inv G)
      ＝ ap inr (ap g ret)
        by left-unit
    where
    e : S ≃ A
    e = equiv-left-map-pushout-is-equiv

    invf : A → S
    invf = map-inv-equiv e

    ret : invf (f s) ＝ s
    ret = is-retraction-map-inv-equiv e s

    sec : f (invf (f s)) ＝ f s
    sec = is-section-map-inv-equiv e (f s)

    coh : sec ＝ ap f ret
    coh = coherence-map-inv-equiv e s

    inl = inl-pushout f g
    inr = inr-pushout f g

    G : inl (f (invf (f s))) ＝ inr (g (invf (f s)))
    G = glue-pushout f g (invf (f s))

    p : inl (f s) ＝ inr (g s)
    p = glue-pushout f g s

  coherence-square-is-section-map-inv-inr-pushout-is-equiv-left-map :
    (s : S) →
    let
      R = map-inv-inr-pushout-is-equiv-left-map
      F = inr-pushout f g ∘ R
      p = glue-pushout f g s
      cinl = compute-inl-cogap f g cocone-inv-inr-pushout-is-equiv-left-map (f s)
      cinr = compute-inr-cogap f g cocone-inv-inr-pushout-is-equiv-left-map (g s)
      e = equiv-left-map-pushout-is-equiv
      invf = map-inv-equiv e
      sec = is-section-map-inv-equiv e (f s)
      G = glue-pushout f g (invf (f s))
    in
      ap F p ∙ ap (inr-pushout f g) cinr ＝
      ( ( ap (inr-pushout f g) cinl ∙ inv G ∙
          ap (inl-pushout f g) sec) ∙
        ap id p)
  coherence-square-is-section-map-inv-inr-pushout-is-equiv-left-map s =
    equational-reasoning
      ap F p ∙ ap inr cinr
      ＝ ap inr (ap R p) ∙ ap inr cinr
        by ap (_∙ ap inr cinr) (ap-comp inr R p)
      ＝ ap inr (ap R p ∙ cinr)
        by inv (ap-concat inr (ap R p) cinr)
      ＝ ap inr (cinl ∙ coh-cocone)
        by ap (ap inr) glue-R
      ＝ ap inr cinl ∙ ap inr coh-cocone
        by ap-concat inr cinl coh-cocone
      ＝ ap inr cinl ∙ ((inv G ∙ ap inl sec) ∙ p)
        by ap (ap inr cinl ∙_)
          ( inv (coherence-glue-is-section-map-inv-inr-pushout-is-equiv-left-map s))
      ＝ (ap inr cinl ∙ (inv G ∙ ap inl sec)) ∙ p
        by inv (assoc (ap inr cinl) (inv G ∙ ap inl sec) p)
      ＝ ((ap inr cinl ∙ inv G) ∙ ap inl sec) ∙ p
        by ap (_∙ p) (inv (assoc (ap inr cinl) (inv G) (ap inl sec)))
      ＝ ((ap inr cinl ∙ inv G) ∙ ap inl sec) ∙ ap id p
        by ap (((ap inr cinl ∙ inv G) ∙ ap inl sec) ∙_) (inv (ap-id p))
    where
    R : pushout f g → B
    R = map-inv-inr-pushout-is-equiv-left-map

    F : pushout f g → pushout f g
    F = inr-pushout f g ∘ R

    e : S ≃ A
    e = equiv-left-map-pushout-is-equiv

    invf : A → S
    invf = map-inv-equiv e

    sec : f (invf (f s)) ＝ f s
    sec = is-section-map-inv-equiv e (f s)

    inl = inl-pushout f g
    inr = inr-pushout f g

    p : inl (f s) ＝ inr (g s)
    p = glue-pushout f g s

    G : inl (f (invf (f s))) ＝ inr (g (invf (f s)))
    G = glue-pushout f g (invf (f s))

    cinl : R (inl (f s)) ＝ g (invf (f s))
    cinl = compute-inl-cogap f g cocone-inv-inr-pushout-is-equiv-left-map (f s)

    cinr : R (inr (g s)) ＝ g s
    cinr = compute-inr-cogap f g cocone-inv-inr-pushout-is-equiv-left-map (g s)

    coh-cocone : g (invf (f s)) ＝ g s
    coh-cocone = coherence-square-cocone f g cocone-inv-inr-pushout-is-equiv-left-map s

    glue-R : ap R p ∙ cinr ＝ cinl ∙ coh-cocone
    glue-R =
      compute-glue-cogap f g cocone-inv-inr-pushout-is-equiv-left-map s

  is-section-map-inv-inr-pushout-is-equiv-left-map :
    ( inr-pushout f g ∘ map-inv-inr-pushout-is-equiv-left-map) ~ id
  is-section-map-inv-inr-pushout-is-equiv-left-map =
    dependent-cogap
      ( f)
      ( g)
      ( ( λ a →
          ap (inr-pushout f g)
            ( compute-inl-cogap
              f g cocone-inv-inr-pushout-is-equiv-left-map a) ∙
          inv
            ( glue-pushout f g
              ( map-inv-equiv equiv-left-map-pushout-is-equiv a)) ∙
          ap (inl-pushout f g)
            ( is-section-map-inv-equiv
              equiv-left-map-pushout-is-equiv a)) ,
        ( λ b →
          ap (inr-pushout f g)
            ( compute-inr-cogap
              f g cocone-inv-inr-pushout-is-equiv-left-map b)) ,
        λ s →
          map-compute-dependent-identification-eq-value-function
            ( inr-pushout f g ∘ map-inv-inr-pushout-is-equiv-left-map)
            ( id)
            ( glue-pushout f g s)
            ( ap (inr-pushout f g)
              ( compute-inl-cogap
                f g cocone-inv-inr-pushout-is-equiv-left-map (f s)) ∙
              inv
                ( glue-pushout f g
                  ( map-inv-equiv equiv-left-map-pushout-is-equiv (f s))) ∙
              ap (inl-pushout f g)
                ( is-section-map-inv-equiv
                  equiv-left-map-pushout-is-equiv (f s)))
            ( ap (inr-pushout f g)
              ( compute-inr-cogap
                f g cocone-inv-inr-pushout-is-equiv-left-map (g s)))
            ( coherence-square-is-section-map-inv-inr-pushout-is-equiv-left-map
              s))

  is-equiv-inr-pushout-is-equiv-left-map :
    is-equiv (inr-pushout f g)
  is-equiv-inr-pushout-is-equiv-left-map =
    is-equiv-is-invertible
      ( map-inv-inr-pushout-is-equiv-left-map)
      ( is-section-map-inv-inr-pushout-is-equiv-left-map)
      ( is-retraction-map-inv-inr-pushout-is-equiv-left-map)

  equiv-inr-pushout-is-equiv-left-map : B ≃ pushout f g
  pr1 equiv-inr-pushout-is-equiv-left-map = inr-pushout f g
  pr2 equiv-inr-pushout-is-equiv-left-map =
    is-equiv-inr-pushout-is-equiv-left-map

module _
  {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B)
  where

  cocone-swap-pushout : cocone f g (pushout g f)
  cocone-swap-pushout =
    swap-cocone g f (pushout g f) (cocone-pushout g f)

  map-swap-pushout : pushout f g → pushout g f
  map-swap-pushout =
    cogap f g cocone-swap-pushout

  compute-inl-map-swap-pushout :
    map-swap-pushout ∘ inl-pushout f g ~ inr-pushout g f
  compute-inl-map-swap-pushout =
    compute-inl-cogap f g cocone-swap-pushout

  compute-inr-map-swap-pushout :
    map-swap-pushout ∘ inr-pushout f g ~ inl-pushout g f
  compute-inr-map-swap-pushout =
    compute-inr-cogap f g cocone-swap-pushout

  universal-property-pushout-cocone-swap-pushout :
    universal-property-pushout f g cocone-swap-pushout
  universal-property-pushout-cocone-swap-pushout =
    universal-property-pushout-swap-cocone-universal-property-pushout
      ( g)
      ( f)
      ( pushout g f)
      ( cocone-pushout g f)
      ( up-pushout g f)

  is-equiv-map-swap-pushout : is-equiv map-swap-pushout
  is-equiv-map-swap-pushout =
    is-equiv-up-pushout-up-pushout
      ( f)
      ( g)
      ( cocone-pushout f g)
      ( cocone-swap-pushout)
      ( map-swap-pushout)
      ( htpy-compute-cogap f g cocone-swap-pushout)
      ( up-pushout f g)
      ( universal-property-pushout-cocone-swap-pushout)

  equiv-swap-pushout : pushout f g ≃ pushout g f
  pr1 equiv-swap-pushout = map-swap-pushout
  pr2 equiv-swap-pushout = is-equiv-map-swap-pushout

module _
  {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (is-equiv-g : is-equiv g)
  where

  equiv-inl-pushout-is-equiv-right-map-comparison :
    A ≃ pushout f g
  equiv-inl-pushout-is-equiv-right-map-comparison =
    equiv-swap-pushout g f ∘e
    equiv-inr-pushout-is-equiv-left-map g f is-equiv-g

  is-equiv-inl-pushout-is-equiv-right-map :
    is-equiv (inl-pushout f g)
  is-equiv-inl-pushout-is-equiv-right-map =
    is-equiv-htpy-equiv
      ( equiv-inl-pushout-is-equiv-right-map-comparison)
      ( λ a →
        inv
          ( compute-inr-map-swap-pushout g f a))

  equiv-inl-pushout-is-equiv-right-map : A ≃ pushout f g
  pr1 equiv-inl-pushout-is-equiv-right-map = inl-pushout f g
  pr2 equiv-inl-pushout-is-equiv-right-map =
    is-equiv-inl-pushout-is-equiv-right-map
```

## Pushouts under equivalences of spans

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3}
  { S' : UU l4} {A' : UU l5} {B' : UU l6}
  ( f : S → A) (g : S → B) (f' : S' → A') (g' : S' → B')
  ( i : A' → A) (j : B' → B) (k : S' → S)
  ( coh-l : coherence-square-maps k f' f i)
  ( coh-r : coherence-square-maps g' k j g)
  ( is-equiv-i : is-equiv i) (is-equiv-j : is-equiv j)
  ( is-equiv-k : is-equiv k)
  where

  cocone-pushout-extension-by-equivalences :
    cocone f' g' (pushout f g)
  cocone-pushout-extension-by-equivalences =
    comp-cocone-hom-span
      ( f)
      ( g)
      ( f')
      ( g')
      ( i)
      ( j)
      ( k)
      ( cocone-pushout f g)
      ( coh-l)
      ( coh-r)

  universal-property-pushout-cocone-pushout-extension-by-equivalences :
    universal-property-pushout f' g' cocone-pushout-extension-by-equivalences
  universal-property-pushout-cocone-pushout-extension-by-equivalences =
    universal-property-pushout-extended-by-equivalences
      ( f)
      ( g)
      ( f')
      ( g')
      ( i)
      ( j)
      ( k)
      ( cocone-pushout f g)
      ( up-pushout f g)
      ( coh-l)
      ( coh-r)
      ( is-equiv-i)
      ( is-equiv-j)
      ( is-equiv-k)

  map-pushout-extension-by-equivalences :
    pushout f' g' → pushout f g
  map-pushout-extension-by-equivalences =
    cogap f' g' cocone-pushout-extension-by-equivalences

  is-equiv-map-pushout-extension-by-equivalences :
    is-equiv map-pushout-extension-by-equivalences
  is-equiv-map-pushout-extension-by-equivalences =
    is-equiv-up-pushout-up-pushout
      ( f')
      ( g')
      ( cocone-pushout f' g')
      ( cocone-pushout-extension-by-equivalences)
      ( map-pushout-extension-by-equivalences)
      ( htpy-compute-cogap f' g' cocone-pushout-extension-by-equivalences)
      ( up-pushout f' g')
      ( universal-property-pushout-cocone-pushout-extension-by-equivalences)

  equiv-pushout-extension-by-equivalences :
    pushout f' g' ≃ pushout f g
  pr1 equiv-pushout-extension-by-equivalences =
    map-pushout-extension-by-equivalences
  pr2 equiv-pushout-extension-by-equivalences =
    is-equiv-map-pushout-extension-by-equivalences
```

## Associating iterated pushouts

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A₁ : UU l1} {B : UU l2} {C : UU l3} {A₂ : UU l4} {D : UU l5}
  (f₁ : A₁ → B) (g₁ : A₁ → C) (f₂ : A₂ → C) (g₂ : A₂ → D)
  where

  left-associated-pushout-pushout : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  left-associated-pushout-pushout =
    pushout (inr-pushout f₁ g₁ ∘ f₂) g₂

  right-associated-pushout-pushout : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  right-associated-pushout-pushout =
    pushout f₁ (inl-pushout f₂ g₂ ∘ g₁)

  cocone-left-pushout-right-associated-pushout-pushout :
    cocone f₁ g₁ right-associated-pushout-pushout
  pr1 cocone-left-pushout-right-associated-pushout-pushout =
    inl-pushout f₁ (inl-pushout f₂ g₂ ∘ g₁)
  pr1 (pr2 cocone-left-pushout-right-associated-pushout-pushout) =
    inr-pushout f₁ (inl-pushout f₂ g₂ ∘ g₁) ∘ inl-pushout f₂ g₂
  pr2 (pr2 cocone-left-pushout-right-associated-pushout-pushout) =
    glue-pushout f₁ (inl-pushout f₂ g₂ ∘ g₁)

  map-left-pushout-right-associated-pushout-pushout :
    pushout f₁ g₁ → right-associated-pushout-pushout
  map-left-pushout-right-associated-pushout-pushout =
    cogap f₁ g₁ cocone-left-pushout-right-associated-pushout-pushout

  compute-inl-map-left-pushout-right-associated-pushout-pushout :
    map-left-pushout-right-associated-pushout-pushout ∘
    inl-pushout f₁ g₁ ~
    inl-pushout f₁ (inl-pushout f₂ g₂ ∘ g₁)
  compute-inl-map-left-pushout-right-associated-pushout-pushout =
    compute-inl-cogap
      f₁ g₁ cocone-left-pushout-right-associated-pushout-pushout

  compute-inr-map-left-pushout-right-associated-pushout-pushout :
    map-left-pushout-right-associated-pushout-pushout ∘
    inr-pushout f₁ g₁ ~
    inr-pushout f₁ (inl-pushout f₂ g₂ ∘ g₁) ∘ inl-pushout f₂ g₂
  compute-inr-map-left-pushout-right-associated-pushout-pushout =
    compute-inr-cogap
      f₁ g₁ cocone-left-pushout-right-associated-pushout-pushout

  cocone-middle-right-associated-pushout-pushout :
    cocone
      ( inr-pushout f₁ g₁)
      ( inl-pushout f₂ g₂)
      ( right-associated-pushout-pushout)
  pr1 cocone-middle-right-associated-pushout-pushout =
    map-left-pushout-right-associated-pushout-pushout
  pr1 (pr2 cocone-middle-right-associated-pushout-pushout) =
    inr-pushout f₁ (inl-pushout f₂ g₂ ∘ g₁)
  pr2 (pr2 cocone-middle-right-associated-pushout-pushout) =
    compute-inr-map-left-pushout-right-associated-pushout-pushout

  cocone-left-associated-span-right-associated-pushout-pushout :
    cocone
      ( inr-pushout f₁ g₁ ∘ f₂)
      ( g₂)
      ( right-associated-pushout-pushout)
  cocone-left-associated-span-right-associated-pushout-pushout =
    cocone-comp-vertical
      ( f₂)
      ( g₂)
      ( inr-pushout f₁ g₁)
      ( cocone-pushout f₂ g₂)
      ( cocone-middle-right-associated-pushout-pushout)

  map-left-associated-right-associated-pushout-pushout :
    left-associated-pushout-pushout → right-associated-pushout-pushout
  map-left-associated-right-associated-pushout-pushout =
    cogap
      ( inr-pushout f₁ g₁ ∘ f₂)
      ( g₂)
      ( cocone-left-associated-span-right-associated-pushout-pushout)

  htpy-cocone-outer-right-associated-pushout-pushout :
    htpy-cocone
      ( f₁)
      ( inl-pushout f₂ g₂ ∘ g₁)
      ( cocone-map
        ( f₁)
        ( inl-pushout f₂ g₂ ∘ g₁)
        ( cocone-pushout f₁ (inl-pushout f₂ g₂ ∘ g₁))
        ( id))
      ( cocone-comp-horizontal
        ( f₁)
        ( g₁)
        ( inl-pushout f₂ g₂)
        ( cocone-pushout f₁ g₁)
        ( cocone-middle-right-associated-pushout-pushout))
  pr1 htpy-cocone-outer-right-associated-pushout-pushout =
    inv-htpy compute-inl-map-left-pushout-right-associated-pushout-pushout
  pr1 (pr2 htpy-cocone-outer-right-associated-pushout-pushout) =
    refl-htpy
  pr2 (pr2 htpy-cocone-outer-right-associated-pushout-pushout) a₁ =
    ap (_∙ refl) (ap-id G) ∙
    right-unit ∙
    inv
      ( ap (inv H ∙_) glue-h ∙
        inv (assoc (inv H) H G) ∙
        ap (_∙ G) (left-inv H) ∙
        left-unit)
    where
    H =
      compute-inl-map-left-pushout-right-associated-pushout-pushout
        ( f₁ a₁)

    G =
      glue-pushout f₁ (inl-pushout f₂ g₂ ∘ g₁) a₁

    glue-h =
      compute-glue-cogap
        f₁ g₁ cocone-left-pushout-right-associated-pushout-pushout a₁

  universal-property-pushout-outer-right-associated-pushout-pushout :
    universal-property-pushout
      ( f₁)
      ( inl-pushout f₂ g₂ ∘ g₁)
      ( cocone-comp-horizontal
        ( f₁)
        ( g₁)
        ( inl-pushout f₂ g₂)
        ( cocone-pushout f₁ g₁)
        ( cocone-middle-right-associated-pushout-pushout))
  universal-property-pushout-outer-right-associated-pushout-pushout =
    up-pushout-up-pushout-is-equiv
      ( f₁)
      ( inl-pushout f₂ g₂ ∘ g₁)
      ( cocone-pushout f₁ (inl-pushout f₂ g₂ ∘ g₁))
      ( cocone-comp-horizontal
        ( f₁)
        ( g₁)
        ( inl-pushout f₂ g₂)
        ( cocone-pushout f₁ g₁)
        ( cocone-middle-right-associated-pushout-pushout))
      ( id)
      ( htpy-cocone-outer-right-associated-pushout-pushout)
      ( is-equiv-id)
      ( up-pushout f₁ (inl-pushout f₂ g₂ ∘ g₁))

  universal-property-pushout-cocone-middle-right-associated-pushout-pushout :
    universal-property-pushout
      ( inr-pushout f₁ g₁)
      ( inl-pushout f₂ g₂)
      ( cocone-middle-right-associated-pushout-pushout)
  universal-property-pushout-cocone-middle-right-associated-pushout-pushout =
    universal-property-pushout-right-universal-property-pushout-rectangle
      ( f₁)
      ( g₁)
      ( inl-pushout f₂ g₂)
      ( cocone-pushout f₁ g₁)
      ( cocone-middle-right-associated-pushout-pushout)
      ( up-pushout f₁ g₁)
      ( universal-property-pushout-outer-right-associated-pushout-pushout)

  universal-property-pushout-cocone-left-associated-span-right-associated-pushout-pushout :
    universal-property-pushout
      ( inr-pushout f₁ g₁ ∘ f₂)
      ( g₂)
      ( cocone-left-associated-span-right-associated-pushout-pushout)
  universal-property-pushout-cocone-left-associated-span-right-associated-pushout-pushout =
    universal-property-pushout-rectangle-universal-property-pushout-top
      ( f₂)
      ( g₂)
      ( inr-pushout f₁ g₁)
      ( cocone-pushout f₂ g₂)
      ( cocone-middle-right-associated-pushout-pushout)
      ( up-pushout f₂ g₂)
      ( universal-property-pushout-cocone-middle-right-associated-pushout-pushout)

  is-equiv-map-left-associated-right-associated-pushout-pushout :
    is-equiv map-left-associated-right-associated-pushout-pushout
  is-equiv-map-left-associated-right-associated-pushout-pushout =
    is-equiv-up-pushout-up-pushout
      ( inr-pushout f₁ g₁ ∘ f₂)
      ( g₂)
      ( cocone-pushout (inr-pushout f₁ g₁ ∘ f₂) g₂)
      ( cocone-left-associated-span-right-associated-pushout-pushout)
      ( map-left-associated-right-associated-pushout-pushout)
      ( htpy-compute-cogap
        ( inr-pushout f₁ g₁ ∘ f₂)
        ( g₂)
        ( cocone-left-associated-span-right-associated-pushout-pushout))
      ( up-pushout (inr-pushout f₁ g₁ ∘ f₂) g₂)
      ( universal-property-pushout-cocone-left-associated-span-right-associated-pushout-pushout)

  equiv-left-associated-right-associated-pushout-pushout :
    left-associated-pushout-pushout ≃ right-associated-pushout-pushout
  pr1 equiv-left-associated-right-associated-pushout-pushout =
    map-left-associated-right-associated-pushout-pushout
  pr2 equiv-left-associated-right-associated-pushout-pushout =
    is-equiv-map-left-associated-right-associated-pushout-pushout
```

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

  map-frobnicate-span-pushout :
    (x0 x1 : X) (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (s : x0 ＝ x1) (y : Y) (q1 : Q x1 y) →
    Σ (Q x0 y)
      ( λ q0 →
        Σ (tr (λ x → Q x y) s q0 ＝ q1)
          ( λ _ →
            glue-span-pushout Q x0 y q0 ∙
            inv (glue-span-pushout Q x1 y q1) ＝ r)) →
    ap (inl-span-pushout Q) s ＝ r
  map-frobnicate-span-pushout x0 .x0 r refl y q1 (.q1 , refl , u) =
    inv (right-inv (glue-span-pushout Q x0 y q1)) ∙ u

  map-inv-frobnicate-span-pushout :
    (x0 x1 : X) (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (s : x0 ＝ x1) (y : Y) (q1 : Q x1 y) →
    ap (inl-span-pushout Q) s ＝ r →
    Σ (Q x0 y)
      ( λ q0 →
        Σ (tr (λ x → Q x y) s q0 ＝ q1)
          ( λ _ →
            glue-span-pushout Q x0 y q0 ∙
            inv (glue-span-pushout Q x1 y q1) ＝ r))
  map-inv-frobnicate-span-pushout x0 .x0 r refl y q1 v =
    q1 ,
    refl ,
    right-inv (glue-span-pushout Q x0 y q1) ∙ v

  is-section-map-inv-frobnicate-span-pushout :
    (x0 x1 : X) (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (s : x0 ＝ x1) (y : Y) (q1 : Q x1 y) →
    ( map-frobnicate-span-pushout x0 x1 r s y q1 ∘
      map-inv-frobnicate-span-pushout x0 x1 r s y q1) ~
    id
  is-section-map-inv-frobnicate-span-pushout x0 .x0 r refl y q1 v =
    inv (assoc (inv R) R v) ∙ ap (_∙ v) (left-inv R)
    where
    R : glue-span-pushout Q x0 y q1 ∙
        inv (glue-span-pushout Q x0 y q1) ＝ refl
    R = right-inv (glue-span-pushout Q x0 y q1)

  is-retraction-map-inv-frobnicate-span-pushout :
    (x0 x1 : X) (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (s : x0 ＝ x1) (y : Y) (q1 : Q x1 y) →
    ( map-inv-frobnicate-span-pushout x0 x1 r s y q1 ∘
      map-frobnicate-span-pushout x0 x1 r s y q1) ~
    id
  is-retraction-map-inv-frobnicate-span-pushout
    x0 .x0 r refl y q1 (.q1 , refl , u) =
    eq-pair-Σ refl
      ( eq-pair-Σ refl
        ( inv (assoc R (inv R) u) ∙ ap (_∙ u) (right-inv R)))
    where
    R : glue-span-pushout Q x0 y q1 ∙
        inv (glue-span-pushout Q x0 y q1) ＝ refl
    R = right-inv (glue-span-pushout Q x0 y q1)

  is-equiv-map-frobnicate-span-pushout :
    (x0 x1 : X) (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (s : x0 ＝ x1) (y : Y) (q1 : Q x1 y) →
    is-equiv (map-frobnicate-span-pushout x0 x1 r s y q1)
  is-equiv-map-frobnicate-span-pushout x0 x1 r s y q1 =
    is-equiv-is-invertible
      ( map-inv-frobnicate-span-pushout x0 x1 r s y q1)
      ( is-section-map-inv-frobnicate-span-pushout x0 x1 r s y q1)
      ( is-retraction-map-inv-frobnicate-span-pushout x0 x1 r s y q1)

  equiv-frobnicate-span-pushout :
    (x0 x1 : X) (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (s : x0 ＝ x1) (y : Y) (q1 : Q x1 y) →
    Σ (Q x0 y)
      ( λ q0 →
        Σ (tr (λ x → Q x y) s q0 ＝ q1)
          ( λ _ →
            glue-span-pushout Q x0 y q0 ∙
            inv (glue-span-pushout Q x1 y q1) ＝ r)) ≃
    ( ap (inl-span-pushout Q) s ＝ r)
  pr1 (equiv-frobnicate-span-pushout x0 x1 r s y q1) =
    map-frobnicate-span-pushout x0 x1 r s y q1
  pr2 (equiv-frobnicate-span-pushout x0 x1 r s y q1) =
    is-equiv-map-frobnicate-span-pushout x0 x1 r s y q1

  code-left-0-span-pushout :
    (x0 x1 : X) →
    inl-span-pushout Q x0 ＝ inl-span-pushout Q x1 →
    UU (l1 ⊔ l2 ⊔ l3)
  code-left-0-span-pushout x0 x1 r =
    Σ (x0 ＝ x1)
      ( λ s →
        Σ Y
          ( λ y0 →
            Σ (ap (inl-span-pushout Q) s ＝ r)
              ( λ v →
                Σ (Q x0 y0)
                  ( λ q00 →
                    Σ (Q x1 y0)
                      ( λ q10 →
                        Σ (tr (λ x → Q x y0) s q00 ＝ q10)
                          ( λ w →
                            Σ (glue-span-pushout Q x0 y0 q00 ∙
                               inv (glue-span-pushout Q x1 y0 q10) ＝ r)
                              ( λ u →
                                map-frobnicate-span-pushout
                                  x0 x1 r s y0 q10
                                  ( q00 , w , u) ＝ v)))))))

  map-code-left-0-code-left-1-span-pushout :
    (x0 x1 : X) (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-0-span-pushout x0 x1 r →
    code-left-1-span-pushout x0 x1 r
  map-code-left-0-code-left-1-span-pushout
    x0 x1 r (s , y0 , v , q00 , q10 , w , u , d) =
    s , v

  map-code-left-0-code-left-2-span-pushout :
    (x0 x1 : X) (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-0-span-pushout x0 x1 r →
    code-left-2-span-pushout x0 x1 r
  map-code-left-0-code-left-2-span-pushout
    x0 x1 r (s , y0 , v , q00 , q10 , w , u , d) =
    y0 , q00 , q10 , u

  code-left-span-pushout :
    (m : 𝕋) (x0 x1 : X) →
    inl-span-pushout Q x0 ＝ inl-span-pushout Q x1 →
    UU (l1 ⊔ l2 ⊔ l3)
  code-left-span-pushout m x0 x1 r =
    type-trunc m
      ( pushout
        ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
        ( map-code-left-0-code-left-2-span-pushout x0 x1 r))

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

  map-code-left-0-code-left-2b-span-pushout :
    (x0 x1 : X) (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-0-span-pushout x0 x1 r →
    code-left-2b-span-pushout x0 x1 r
  map-code-left-0-code-left-2b-span-pushout
    x0 x1 r (s , y0 , v , q00 , q10 , w , u , d) =
    s , y0 , q00 , q10 , w , u

  map-inv-code-left-0-code-left-2b-span-pushout :
    (x0 x1 : X) (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-2b-span-pushout x0 x1 r →
    code-left-0-span-pushout x0 x1 r
  map-inv-code-left-0-code-left-2b-span-pushout
    x0 x1 r (s , y0 , q00 , q10 , w , u) =
    s ,
    y0 ,
    map-frobnicate-span-pushout x0 x1 r s y0 q10 (q00 , w , u) ,
    q00 ,
    q10 ,
    w ,
    u ,
    refl

  is-section-map-inv-code-left-0-code-left-2b-span-pushout :
    (x0 x1 : X) (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    ( map-code-left-0-code-left-2b-span-pushout x0 x1 r ∘
      map-inv-code-left-0-code-left-2b-span-pushout x0 x1 r) ~
    id
  is-section-map-inv-code-left-0-code-left-2b-span-pushout
    x0 x1 r (s , y0 , q00 , q10 , w , u) =
    refl

  is-retraction-map-inv-code-left-0-code-left-2b-span-pushout :
    (x0 x1 : X) (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    ( map-inv-code-left-0-code-left-2b-span-pushout x0 x1 r ∘
      map-code-left-0-code-left-2b-span-pushout x0 x1 r) ~
    id
  is-retraction-map-inv-code-left-0-code-left-2b-span-pushout
    x0 x1 r (s , y0 , v , q00 , q10 , w , u , refl) =
    refl

  is-equiv-map-code-left-0-code-left-2b-span-pushout :
    (x0 x1 : X) (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    is-equiv (map-code-left-0-code-left-2b-span-pushout x0 x1 r)
  is-equiv-map-code-left-0-code-left-2b-span-pushout x0 x1 r =
    is-equiv-is-invertible
      ( map-inv-code-left-0-code-left-2b-span-pushout x0 x1 r)
      ( is-section-map-inv-code-left-0-code-left-2b-span-pushout x0 x1 r)
      ( is-retraction-map-inv-code-left-0-code-left-2b-span-pushout x0 x1 r)

  equiv-code-left-0-code-left-2b-span-pushout :
    (x0 x1 : X) (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-0-span-pushout x0 x1 r ≃
    code-left-2b-span-pushout x0 x1 r
  pr1 (equiv-code-left-0-code-left-2b-span-pushout x0 x1 r) =
    map-code-left-0-code-left-2b-span-pushout x0 x1 r
  pr2 (equiv-code-left-0-code-left-2b-span-pushout x0 x1 r) =
    is-equiv-map-code-left-0-code-left-2b-span-pushout x0 x1 r

  map-code-left-2a-code-left-1-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-2a-span-pushout x0 x1 y1 q11 r →
    code-left-1-span-pushout x0 x1 r
  map-code-left-2a-code-left-1-span-pushout
    x0 x1 y1 q11 r (s , q01 , w , u) =
    s ,
    map-frobnicate-span-pushout x0 x1 r s y1 q11 (q01 , w , u)

  map-inv-code-left-2a-code-left-1-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-1-span-pushout x0 x1 r →
    code-left-2a-span-pushout x0 x1 y1 q11 r
  map-inv-code-left-2a-code-left-1-span-pushout
    x0 x1 y1 q11 r (s , v) =
    s ,
    pr1 w ,
    pr1 (pr2 w) ,
    pr2 (pr2 w)
    where
    w =
      map-inv-frobnicate-span-pushout x0 x1 r s y1 q11 v

  is-section-map-inv-code-left-2a-code-left-1-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    ( map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r ∘
      map-inv-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r) ~
    id
  is-section-map-inv-code-left-2a-code-left-1-span-pushout
    x0 x1 y1 q11 r (s , v) =
    eq-pair-Σ refl
      ( is-section-map-inv-frobnicate-span-pushout
        x0 x1 r s y1 q11 v)

  is-retraction-map-inv-code-left-2a-code-left-1-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    ( map-inv-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r ∘
      map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r) ~
    id
  is-retraction-map-inv-code-left-2a-code-left-1-span-pushout
    x0 x1 y1 q11 r (s , q01 , w , u) =
    eq-pair-Σ refl
      ( is-retraction-map-inv-frobnicate-span-pushout
        x0 x1 r s y1 q11
        ( q01 , w , u))

  is-equiv-map-code-left-2a-code-left-1-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    is-equiv (map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r)
  is-equiv-map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r =
    is-equiv-is-invertible
      ( map-inv-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r)
      ( is-section-map-inv-code-left-2a-code-left-1-span-pushout
        x0 x1 y1 q11 r)
      ( is-retraction-map-inv-code-left-2a-code-left-1-span-pushout
        x0 x1 y1 q11 r)

  equiv-code-left-2a-code-left-1-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-2a-span-pushout x0 x1 y1 q11 r ≃
    code-left-1-span-pushout x0 x1 r
  pr1 (equiv-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r) =
    map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r
  pr2 (equiv-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r) =
    is-equiv-map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r

  htpy-map-code-left-2a-code-left-1-through-code-left-2b-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r ~
    ( map-code-left-0-code-left-1-span-pushout x0 x1 r ∘
      map-inv-code-left-0-code-left-2b-span-pushout x0 x1 r ∘
      map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
  htpy-map-code-left-2a-code-left-1-through-code-left-2b-span-pushout
    x0 x1 y1 q11 r (s , q01 , w , u) =
    refl

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

  compute-glue-map-code-left-2-decomposition-code-left-2-with-join-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (a : code-left-2a-span-pushout x0 x1 y1 q11 r) →
    ( ap
      ( map-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x1 y1 q11 r)
      ( glue-pushout
        ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
        ( a)) ∙
      compute-inr-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x1 y1 q11 r
        ( map-code-left-2a-code-left-2c-span-pushout
          x0 x1 y1 q11 r a)) ＝
    ( compute-inl-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
      x0 x1 y1 q11 r
      ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r a) ∙
      eq-pair-Σ refl
        ( glue-join
          ( eq-pair-Σ (pr1 a) (pr1 (pr2 (pr2 a))) ,
            refl)))
  compute-glue-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
    x0 x1 y1 q11 r =
    compute-glue-cogap
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

  compute-glue-map-code-left-2-with-join-code-left-2-decomposition-span-pushout :
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
    ( ap
      ( map-code-left-2-with-join-code-left-2-decomposition-span-pushout
        x0 x1 y1 q11 r)
      ( eq-pair-Σ refl (glue-join (p , q))) ∙
      compute-inr-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
        x0 x1 y1 q11 r c q) ＝
    ( compute-inl-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
      x0 x1 y1 q11 r c p ∙
      coherence-column-row-path-code-left-2-decomposition-span-pushout
        x0 x1 y1 q11 r c p q)
  compute-glue-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
    x0 x1 y1 q11 r c p q =
    ap
      ( _∙
        compute-inr-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
          x0 x1 y1 q11 r c q)
      ( compute-ap-eq-pair-Σ
        ( map-code-left-2-with-join-code-left-2-decomposition-span-pushout
          x0 x1 y1 q11 r)
        ( refl)
        ( glue-join (p , q))) ∙
    compute-glue-cogap-join
      ( map-column-path-code-left-2-decomposition-span-pushout
        x0 x1 y1 q11 r c ,
        map-row-path-code-left-2-decomposition-span-pushout
        x0 x1 y1 q11 r c ,
        λ (p , q) →
          coherence-column-row-path-code-left-2-decomposition-span-pushout
            x0 x1 y1 q11 r c p q)
      ( p , q)

  is-retraction-map-code-left-2-with-join-code-left-2-decomposition-span-pushout-inl :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (b : code-left-2b-span-pushout x0 x1 r) →
    ( map-code-left-2-with-join-code-left-2-decomposition-span-pushout
      x0 x1 y1 q11 r ∘
      map-code-left-2-decomposition-code-left-2-with-join-span-pushout
      x0 x1 y1 q11 r)
      ( inl-pushout
        ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
        ( b)) ＝
    inl-pushout
      ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
      ( b)
  is-retraction-map-code-left-2-with-join-code-left-2-decomposition-span-pushout-inl
    x0 x1 y1 q11 r (s , y0 , q00 , q10 , w , u) =
    ap
      ( map-code-left-2-with-join-code-left-2-decomposition-span-pushout
        x0 x1 y1 q11 r)
      ( compute-inl-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x1 y1 q11 r
        ( s , y0 , q00 , q10 , w , u)) ∙
    compute-inl-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
      x0 x1 y1 q11 r
      ( y0 , q00 , q10 , u)
      ( eq-pair-Σ s w) ∙
    ap
      ( inl-pushout
        ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r))
      ( ap
        ( λ sw → pr1 sw , y0 , q00 , q10 , pr2 sw , u)
        ( is-retraction-pair-eq-Σ
          ( x0 , q00)
          ( x1 , q10)
          ( s , w)))

  is-retraction-map-code-left-2-with-join-code-left-2-decomposition-span-pushout-inr :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (c : code-left-2c-span-pushout x0 x1 y1 q11 r) →
    ( map-code-left-2-with-join-code-left-2-decomposition-span-pushout
      x0 x1 y1 q11 r ∘
      map-code-left-2-decomposition-code-left-2-with-join-span-pushout
      x0 x1 y1 q11 r)
      ( inr-pushout
        ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
        ( c)) ＝
    inr-pushout
      ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
      ( c)
  is-retraction-map-code-left-2-with-join-code-left-2-decomposition-span-pushout-inr
    x0 x1 y1 q11 r (q01 , u) =
    ap
      ( map-code-left-2-with-join-code-left-2-decomposition-span-pushout
        x0 x1 y1 q11 r)
      ( compute-inr-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x1 y1 q11 r
        ( q01 , u)) ∙
    compute-inr-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
      x0 x1 y1 q11 r
      ( y1 , q01 , q11 , u)
      ( refl)

  coherence-square-is-retraction-map-code-left-2-with-join-code-left-2-decomposition-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (a : code-left-2a-span-pushout x0 x1 y1 q11 r) →
    ( ap
      ( map-code-left-2-with-join-code-left-2-decomposition-span-pushout
        x0 x1 y1 q11 r ∘
        map-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x1 y1 q11 r)
      ( glue-pushout
        ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
        ( a)) ∙
      is-retraction-map-code-left-2-with-join-code-left-2-decomposition-span-pushout-inr
        x0 x1 y1 q11 r
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r a)) ＝
    ( is-retraction-map-code-left-2-with-join-code-left-2-decomposition-span-pushout-inl
      x0 x1 y1 q11 r
      ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r a) ∙
      ap id
        ( glue-pushout
          ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
          ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
          ( a)))
  coherence-square-is-retraction-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
    x0 .x0 y1 .q01 r (refl , q01 , refl , u) =
    equational-reasoning
      ap F pD ∙ Rinr
      ＝ ap n (ap m pD) ∙ Rinr
        by ap (_∙ Rinr) (ap-comp n m pD)
      ＝ (ap n (ap m pD) ∙ ap n cinr-m) ∙ cinr-n
        by inv (assoc (ap n (ap m pD)) (ap n cinr-m) cinr-n)
      ＝ ap n (ap m pD ∙ cinr-m) ∙ cinr-n
        by ap (_∙ cinr-n) (inv (ap-concat n (ap m pD) cinr-m))
      ＝ ap n (cinl-m ∙ jglue) ∙ cinr-n
        by ap (λ p → ap n p ∙ cinr-n) glue-m
      ＝ (ap n cinl-m ∙ ap n jglue) ∙ cinr-n
        by ap (_∙ cinr-n) (ap-concat n cinl-m jglue)
      ＝ ap n cinl-m ∙ (ap n jglue ∙ cinr-n)
        by assoc (ap n cinl-m) (ap n jglue) cinr-n
      ＝ ap n cinl-m ∙ (cinl-n ∙ pD)
        by ap (ap n cinl-m ∙_) glue-n
      ＝ (ap n cinl-m ∙ cinl-n) ∙ pD
        by inv (assoc (ap n cinl-m) cinl-n pD)
      ＝ ((ap n cinl-m ∙ cinl-n) ∙ refl) ∙ pD
        by ap (_∙ pD) (inv right-unit)
      ＝ ((ap n cinl-m ∙ cinl-n) ∙ refl) ∙ ap id pD
        by ap (((ap n cinl-m ∙ cinl-n) ∙ refl) ∙_) (inv (ap-id pD))
    where
    fD =
      map-code-left-2a-code-left-2b-span-pushout x0 x0 y1 q01 r

    gD =
      map-code-left-2a-code-left-2c-span-pushout x0 x0 y1 q01 r

    aD : code-left-2a-span-pushout x0 x0 y1 q01 r
    aD = refl , q01 , refl , u

    bD : code-left-2b-span-pushout x0 x0 r
    bD = fD aD

    cD : code-left-2c-span-pushout x0 x0 y1 q01 r
    cD = gD aD

    c : code-left-2-span-pushout x0 x0 r
    c = y1 , q01 , q01 , u

    m :
      code-left-2-decomposition-span-pushout x0 x0 y1 q01 r →
      code-left-2-with-join-span-pushout x0 x0 y1 q01 r
    m =
      map-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x0 y1 q01 r

    n :
      code-left-2-with-join-span-pushout x0 x0 y1 q01 r →
      code-left-2-decomposition-span-pushout x0 x0 y1 q01 r
    n =
      map-code-left-2-with-join-code-left-2-decomposition-span-pushout
        x0 x0 y1 q01 r

    F :
      code-left-2-decomposition-span-pushout x0 x0 y1 q01 r →
      code-left-2-decomposition-span-pushout x0 x0 y1 q01 r
    F = n ∘ m

    pD :
      inl-pushout fD gD bD ＝
      inr-pushout fD gD cD
    pD = glue-pushout fD gD aD

    cinl-m : m (inl-pushout fD gD bD) ＝
      map-code-left-2b-code-left-2-with-join-span-pushout
        x0 x0 y1 q01 r bD
    cinl-m =
      compute-inl-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x0 y1 q01 r bD

    cinr-m : m (inr-pushout fD gD cD) ＝
      map-code-left-2c-code-left-2-with-join-span-pushout
        x0 x0 y1 q01 r cD
    cinr-m =
      compute-inr-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x0 y1 q01 r cD

    jglue :
      map-code-left-2b-code-left-2-with-join-span-pushout
        x0 x0 y1 q01 r bD ＝
      map-code-left-2c-code-left-2-with-join-span-pushout
        x0 x0 y1 q01 r cD
    jglue = eq-pair-Σ refl (glue-join (refl , refl))

    cinl-n :
      n
        ( map-code-left-2b-code-left-2-with-join-span-pushout
          x0 x0 y1 q01 r bD) ＝
      inl-pushout fD gD bD
    cinl-n =
      compute-inl-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
        x0 x0 y1 q01 r c refl

    cinr-n :
      n
        ( map-code-left-2c-code-left-2-with-join-span-pushout
          x0 x0 y1 q01 r cD) ＝
      inr-pushout fD gD cD
    cinr-n =
      compute-inr-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
        x0 x0 y1 q01 r c refl

    Rinr : F (inr-pushout fD gD cD) ＝ inr-pushout fD gD cD
    Rinr =
      is-retraction-map-code-left-2-with-join-code-left-2-decomposition-span-pushout-inr
        x0 x0 y1 q01 r cD

    glue-m : ap m pD ∙ cinr-m ＝ cinl-m ∙ jglue
    glue-m =
      compute-glue-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x0 y1 q01 r aD

    glue-n : ap n jglue ∙ cinr-n ＝ cinl-n ∙ pD
    glue-n =
      compute-glue-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
        x0 x0 y1 q01 r c refl refl

  is-retraction-map-code-left-2-with-join-code-left-2-decomposition-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    ( map-code-left-2-with-join-code-left-2-decomposition-span-pushout
      x0 x1 y1 q11 r ∘
      map-code-left-2-decomposition-code-left-2-with-join-span-pushout
      x0 x1 y1 q11 r) ~
    id
  is-retraction-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
    x0 x1 y1 q11 r =
    dependent-cogap
      ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
      ( is-retraction-map-code-left-2-with-join-code-left-2-decomposition-span-pushout-inl
          x0 x1 y1 q11 r ,
        is-retraction-map-code-left-2-with-join-code-left-2-decomposition-span-pushout-inr
          x0 x1 y1 q11 r ,
        λ a →
          map-compute-dependent-identification-eq-value-function
            ( map-code-left-2-with-join-code-left-2-decomposition-span-pushout
              x0 x1 y1 q11 r ∘
              map-code-left-2-decomposition-code-left-2-with-join-span-pushout
              x0 x1 y1 q11 r)
            ( id)
            ( glue-pushout
              ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
              ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
              ( a))
            ( is-retraction-map-code-left-2-with-join-code-left-2-decomposition-span-pushout-inl
              x0 x1 y1 q11 r
              ( map-code-left-2a-code-left-2b-span-pushout
                x0 x1 y1 q11 r a))
            ( is-retraction-map-code-left-2-with-join-code-left-2-decomposition-span-pushout-inr
              x0 x1 y1 q11 r
              ( map-code-left-2a-code-left-2c-span-pushout
                x0 x1 y1 q11 r a))
            ( coherence-square-is-retraction-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
              x0 x1 y1 q11 r a))

  is-section-map-code-left-2-decomposition-code-left-2-with-join-span-pushout-inl :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (c : code-left-2-span-pushout x0 x1 r)
    (p :
      _＝_
        { A = column-total-space-span-pushout
                ( y-code-left-2-span-pushout c)}
        ( x0 , q00-code-left-2-span-pushout c)
        ( x1 , q10-code-left-2-span-pushout c)) →
    ( map-code-left-2-decomposition-code-left-2-with-join-span-pushout
      x0 x1 y1 q11 r ∘
      map-code-left-2-with-join-code-left-2-decomposition-span-pushout
      x0 x1 y1 q11 r)
      ( c , inl-join p) ＝
    ( c , inl-join p)
  is-section-map-code-left-2-decomposition-code-left-2-with-join-span-pushout-inl
    x0 x1 y1 q11 r (y0 , q00 , q10 , u) p =
    ap
      ( map-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x1 y1 q11 r)
      ( compute-inl-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
        x0 x1 y1 q11 r
        ( y0 , q00 , q10 , u)
        ( p)) ∙
    compute-inl-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
      x0 x1 y1 q11 r
      ( pr1 (pair-eq-Σ p) ,
        y0 ,
        q00 ,
        q10 ,
        pr2 (pair-eq-Σ p) ,
        u) ∙
    eq-pair-Σ refl
      ( ap
        ( inl-join)
        ( is-section-pair-eq-Σ
          ( x0 , q00)
          ( x1 , q10)
          ( p)))

  is-section-map-code-left-2-decomposition-code-left-2-with-join-span-pushout-inr :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (c : code-left-2-span-pushout x0 x1 r)
    (q :
      _＝_
        { A = row-total-space-span-pushout x1}
        ( y-code-left-2-span-pushout c , q10-code-left-2-span-pushout c)
        ( y1 , q11)) →
    ( map-code-left-2-decomposition-code-left-2-with-join-span-pushout
      x0 x1 y1 q11 r ∘
      map-code-left-2-with-join-code-left-2-decomposition-span-pushout
      x0 x1 y1 q11 r)
      ( c , inr-join q) ＝
    ( c , inr-join q)
  is-section-map-code-left-2-decomposition-code-left-2-with-join-span-pushout-inr
    x0 x1 .y0 .q10 r (y0 , q00 , q10 , u) refl =
    ap
      ( map-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x1 y0 q10 r)
      ( compute-inr-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
        x0 x1 y0 q10 r
        ( y0 , q00 , q10 , u)
        ( refl)) ∙
    compute-inr-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
      x0 x1 y0 q10 r
      ( q00 , u)

  coherence-square-is-section-map-code-left-2-decomposition-code-left-2-with-join-span-pushout :
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
    ( ap
      ( λ j →
        ( map-code-left-2-decomposition-code-left-2-with-join-span-pushout
          x0 x1 y1 q11 r ∘
          map-code-left-2-with-join-code-left-2-decomposition-span-pushout
          x0 x1 y1 q11 r)
          ( c , j))
      ( glue-join (p , q)) ∙
      is-section-map-code-left-2-decomposition-code-left-2-with-join-span-pushout-inr
        x0 x1 y1 q11 r c q) ＝
    ( is-section-map-code-left-2-decomposition-code-left-2-with-join-span-pushout-inl
      x0 x1 y1 q11 r c p ∙
      ap (pair c) (glue-join (p , q)))
  coherence-square-is-section-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
    x0 .x0 .y0 .q00 r (y0 , q00 , .q00 , u) refl refl =
    equational-reasoning
      ap FJ jD ∙ Sinr
      ＝ ap F pW ∙ Sinr
        by ap (_∙ Sinr) (ap-comp F pairc jD)
      ＝ ap m (ap n pW) ∙ Sinr
        by ap (_∙ Sinr) (ap-comp m n pW)
      ＝ (ap m (ap n pW) ∙ ap m cinr-n) ∙ cinr-m
        by inv (assoc (ap m (ap n pW)) (ap m cinr-n) cinr-m)
      ＝ ap m (ap n pW ∙ cinr-n) ∙ cinr-m
        by ap (_∙ cinr-m) (inv (ap-concat m (ap n pW) cinr-n))
      ＝ ap m (cinl-n ∙ pD) ∙ cinr-m
        by ap (λ p → ap m p ∙ cinr-m) glue-n
      ＝ (ap m cinl-n ∙ ap m pD) ∙ cinr-m
        by ap (_∙ cinr-m) (ap-concat m cinl-n pD)
      ＝ ap m cinl-n ∙ (ap m pD ∙ cinr-m)
        by assoc (ap m cinl-n) (ap m pD) cinr-m
      ＝ ap m cinl-n ∙ (cinl-m ∙ pW)
        by ap (ap m cinl-n ∙_) glue-m
      ＝ (ap m cinl-n ∙ cinl-m) ∙ pW
        by inv (assoc (ap m cinl-n) cinl-m pW)
      ＝ ((ap m cinl-n ∙ cinl-m) ∙ refl) ∙ pW
        by ap (_∙ pW) (inv right-unit)
    where
    fD =
      map-code-left-2a-code-left-2b-span-pushout x0 x0 y0 q00 r

    gD =
      map-code-left-2a-code-left-2c-span-pushout x0 x0 y0 q00 r

    aD : code-left-2a-span-pushout x0 x0 y0 q00 r
    aD = refl , q00 , refl , u

    bD : code-left-2b-span-pushout x0 x0 r
    bD = fD aD

    cD : code-left-2c-span-pushout x0 x0 y0 q00 r
    cD = gD aD

    c : code-left-2-span-pushout x0 x0 r
    c = y0 , q00 , q00 , u

    m :
      code-left-2-decomposition-span-pushout x0 x0 y0 q00 r →
      code-left-2-with-join-span-pushout x0 x0 y0 q00 r
    m =
      map-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x0 y0 q00 r

    n :
      code-left-2-with-join-span-pushout x0 x0 y0 q00 r →
      code-left-2-decomposition-span-pushout x0 x0 y0 q00 r
    n =
      map-code-left-2-with-join-code-left-2-decomposition-span-pushout
        x0 x0 y0 q00 r

    F :
      code-left-2-with-join-span-pushout x0 x0 y0 q00 r →
      code-left-2-with-join-span-pushout x0 x0 y0 q00 r
    F = m ∘ n

    pairc :
      ( _＝_
        { A = column-total-space-span-pushout y0}
        ( x0 , q00)
        ( x0 , q00)) *
      ( _＝_
        { A = row-total-space-span-pushout x0}
        ( y0 , q00)
        ( y0 , q00)) →
      code-left-2-with-join-span-pushout x0 x0 y0 q00 r
    pairc = pair c

    FJ :
      ( _＝_
        { A = column-total-space-span-pushout y0}
        ( x0 , q00)
        ( x0 , q00)) *
      ( _＝_
        { A = row-total-space-span-pushout x0}
        ( y0 , q00)
        ( y0 , q00)) →
      code-left-2-with-join-span-pushout x0 x0 y0 q00 r
    FJ = F ∘ pairc

    jD :
      inl-join refl ＝ inr-join refl
    jD = glue-join (refl , refl)

    pW :
      pairc (inl-join refl) ＝ pairc (inr-join refl)
    pW = ap pairc jD

    pD :
      inl-pushout fD gD bD ＝
      inr-pushout fD gD cD
    pD = glue-pushout fD gD aD

    cinl-n :
      n (pairc (inl-join refl)) ＝ inl-pushout fD gD bD
    cinl-n =
      compute-inl-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
        x0 x0 y0 q00 r c refl

    cinr-n :
      n (pairc (inr-join refl)) ＝ inr-pushout fD gD cD
    cinr-n =
      compute-inr-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
        x0 x0 y0 q00 r c refl

    cinl-m :
      m (inl-pushout fD gD bD) ＝ pairc (inl-join refl)
    cinl-m =
      compute-inl-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x0 y0 q00 r bD

    cinr-m :
      m (inr-pushout fD gD cD) ＝ pairc (inr-join refl)
    cinr-m =
      compute-inr-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x0 y0 q00 r cD

    Sinr : F (pairc (inr-join refl)) ＝ pairc (inr-join refl)
    Sinr =
      is-section-map-code-left-2-decomposition-code-left-2-with-join-span-pushout-inr
        x0 x0 y0 q00 r c refl

    glue-n : ap n pW ∙ cinr-n ＝ cinl-n ∙ pD
    glue-n =
      compute-glue-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
        x0 x0 y0 q00 r c refl refl

    glue-m : ap m pD ∙ cinr-m ＝ cinl-m ∙ pW
    glue-m =
      compute-glue-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x0 y0 q00 r aD

  is-section-map-code-left-2-decomposition-code-left-2-with-join-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    ( map-code-left-2-decomposition-code-left-2-with-join-span-pushout
      x0 x1 y1 q11 r ∘
      map-code-left-2-with-join-code-left-2-decomposition-span-pushout
      x0 x1 y1 q11 r) ~
    id
  is-section-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
    x0 x1 y1 q11 r (c , j) =
    dependent-cogap-join
      ( is-section-map-code-left-2-decomposition-code-left-2-with-join-span-pushout-inl
          x0 x1 y1 q11 r c ,
        is-section-map-code-left-2-decomposition-code-left-2-with-join-span-pushout-inr
          x0 x1 y1 q11 r c ,
        λ (p , q) →
          map-compute-dependent-identification-eq-value-function
            ( λ j →
              ( map-code-left-2-decomposition-code-left-2-with-join-span-pushout
                x0 x1 y1 q11 r ∘
                map-code-left-2-with-join-code-left-2-decomposition-span-pushout
                x0 x1 y1 q11 r)
                ( c , j))
            ( pair c)
            ( glue-join (p , q))
            ( is-section-map-code-left-2-decomposition-code-left-2-with-join-span-pushout-inl
              x0 x1 y1 q11 r c p)
            ( is-section-map-code-left-2-decomposition-code-left-2-with-join-span-pushout-inr
              x0 x1 y1 q11 r c q)
            ( coherence-square-is-section-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
              x0 x1 y1 q11 r c p q))
      ( j)

  is-equiv-map-code-left-2-decomposition-code-left-2-with-join-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    is-equiv
      ( map-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x1 y1 q11 r)
  is-equiv-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
    x0 x1 y1 q11 r =
    is-equiv-is-invertible
      ( map-code-left-2-with-join-code-left-2-decomposition-span-pushout
        x0 x1 y1 q11 r)
      ( is-section-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x1 y1 q11 r)
      ( is-retraction-map-code-left-2-with-join-code-left-2-decomposition-span-pushout
        x0 x1 y1 q11 r)

  equiv-code-left-2-decomposition-code-left-2-with-join-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-2-decomposition-span-pushout x0 x1 y1 q11 r ≃
    code-left-2-with-join-span-pushout x0 x1 y1 q11 r
  pr1
    ( equiv-code-left-2-decomposition-code-left-2-with-join-span-pushout
      x0 x1 y1 q11 r) =
    map-code-left-2-decomposition-code-left-2-with-join-span-pushout
      x0 x1 y1 q11 r
  pr2
    ( equiv-code-left-2-decomposition-code-left-2-with-join-span-pushout
      x0 x1 y1 q11 r) =
    is-equiv-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
      x0 x1 y1 q11 r

  equiv-trunc-code-left-2-decomposition-code-left-2-span-pushout :
    (m : 𝕋) →
    connected-join-hypothesis-span-pushout m →
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    type-trunc m
      ( code-left-2-decomposition-span-pushout x0 x1 y1 q11 r) ≃
    type-trunc m (code-left-2-span-pushout x0 x1 r)
  equiv-trunc-code-left-2-decomposition-code-left-2-span-pushout
    m H x0 x1 y1 q11 r =
    equiv-trunc-projection-code-left-2-with-join-span-pushout
      ( m)
      ( H)
      ( x0)
      ( x1)
      ( y1)
      ( q11)
      ( r) ∘e
    equiv-trunc
      ( m)
      ( equiv-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x1 y1 q11 r)

  map-code-left-0-code-left-2-decomposition-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-0-span-pushout x0 x1 r →
    code-left-2-decomposition-span-pushout x0 x1 y1 q11 r
  map-code-left-0-code-left-2-decomposition-span-pushout
    x0 x1 y1 q11 r =
    inl-pushout
      ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r) ∘
    map-code-left-0-code-left-2b-span-pushout x0 x1 r

  compute-equiv-trunc-code-left-2-decomposition-code-left-2-inl-span-pushout :
    (m : 𝕋) →
    (H : connected-join-hypothesis-span-pushout m) →
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (b : code-left-2b-span-pushout x0 x1 r) →
    map-equiv
      ( equiv-trunc-code-left-2-decomposition-code-left-2-span-pushout
        m H x0 x1 y1 q11 r)
      ( unit-trunc
        ( inl-pushout
          ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
          ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
          ( b))) ＝
    unit-trunc (map-code-left-2b-code-left-2-span-pushout x0 x1 r b)
  compute-equiv-trunc-code-left-2-decomposition-code-left-2-inl-span-pushout
    m H x0 x1 y1 q11 r b =
    ( ap
      ( map-equiv
        ( equiv-trunc-projection-code-left-2-with-join-span-pushout
          m H x0 x1 y1 q11 r))
      ( naturality-unit-trunc
        ( m)
        ( map-equiv
          ( equiv-code-left-2-decomposition-code-left-2-with-join-span-pushout
            x0 x1 y1 q11 r))
        ( inl-pushout
          ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
          ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
          ( b)))) ∙
    ( ap
      ( map-equiv
        ( equiv-trunc-projection-code-left-2-with-join-span-pushout
          m H x0 x1 y1 q11 r) ∘
        unit-trunc)
      ( compute-inl-map-code-left-2-decomposition-code-left-2-with-join-span-pushout
        x0 x1 y1 q11 r b)) ∙
    ( naturality-unit-trunc
      ( m)
      ( projection-code-left-2-with-join-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2b-code-left-2-with-join-span-pushout
        x0 x1 y1 q11 r b))

  coherence-trunc-code-left-0-code-left-2-decomposition-code-left-2-span-pushout :
    (m : 𝕋) →
    (H : connected-join-hypothesis-span-pushout m) →
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    map-trunc m (map-code-left-0-code-left-2-span-pushout x0 x1 r) ~
    ( map-equiv
      ( equiv-trunc-code-left-2-decomposition-code-left-2-span-pushout
        m H x0 x1 y1 q11 r) ∘
      map-trunc
        ( m)
        ( map-code-left-0-code-left-2-decomposition-span-pushout
          x0 x1 y1 q11 r))
  coherence-trunc-code-left-0-code-left-2-decomposition-code-left-2-span-pushout
    m H x0 x1 y1 q11 r =
    function-dependent-universal-property-trunc
      ( λ t →
        Id-Truncated-Type'
          ( trunc m (code-left-2-span-pushout x0 x1 r))
          ( map-trunc
            ( m)
            ( map-code-left-0-code-left-2-span-pushout x0 x1 r)
            ( t))
          ( map-equiv
            ( equiv-trunc-code-left-2-decomposition-code-left-2-span-pushout
              m H x0 x1 y1 q11 r)
            ( map-trunc
              ( m)
              ( map-code-left-0-code-left-2-decomposition-span-pushout
                x0 x1 y1 q11 r)
              ( t))))
      ( λ c0 →
        naturality-unit-trunc
          ( m)
          ( map-code-left-0-code-left-2-span-pushout x0 x1 r)
          ( c0) ∙
        inv
          ( compute-equiv-trunc-code-left-2-decomposition-code-left-2-inl-span-pushout
            ( m)
            ( H)
            ( x0)
            ( x1)
            ( y1)
            ( q11)
            ( r)
            ( map-code-left-0-code-left-2b-span-pushout x0 x1 r c0)) ∙
        ap
          ( map-equiv
            ( equiv-trunc-code-left-2-decomposition-code-left-2-span-pushout
              m H x0 x1 y1 q11 r))
          ( inv
            ( naturality-unit-trunc
              ( m)
              ( map-code-left-0-code-left-2-decomposition-span-pushout
                x0 x1 y1 q11 r)
              ( c0))))

  equiv-code-left-2-decomposition-trunc-pushout-code-left-2-trunc-pushout-span-pushout :
    (m : 𝕋) →
    (H : connected-join-hypothesis-span-pushout m) →
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    pushout
      ( map-trunc m (map-code-left-0-code-left-1-span-pushout x0 x1 r))
      ( map-trunc
        ( m)
        ( map-code-left-0-code-left-2-decomposition-span-pushout
          x0 x1 y1 q11 r)) ≃
    pushout
      ( map-trunc m (map-code-left-0-code-left-1-span-pushout x0 x1 r))
      ( map-trunc m (map-code-left-0-code-left-2-span-pushout x0 x1 r))
  equiv-code-left-2-decomposition-trunc-pushout-code-left-2-trunc-pushout-span-pushout
    m H x0 x1 y1 q11 r =
    equiv-pushout-extension-by-equivalences
      ( map-trunc m (map-code-left-0-code-left-1-span-pushout x0 x1 r))
      ( map-trunc m (map-code-left-0-code-left-2-span-pushout x0 x1 r))
      ( map-trunc m (map-code-left-0-code-left-1-span-pushout x0 x1 r))
      ( map-trunc
        ( m)
        ( map-code-left-0-code-left-2-decomposition-span-pushout
          x0 x1 y1 q11 r))
      ( id)
      ( map-equiv
        ( equiv-trunc-code-left-2-decomposition-code-left-2-span-pushout
          m H x0 x1 y1 q11 r))
      ( id)
      ( refl-htpy)
      ( coherence-trunc-code-left-0-code-left-2-decomposition-code-left-2-span-pushout
        m H x0 x1 y1 q11 r)
      ( is-equiv-id)
      ( is-equiv-map-equiv
        ( equiv-trunc-code-left-2-decomposition-code-left-2-span-pushout
          m H x0 x1 y1 q11 r))
      ( is-equiv-id)

  equiv-trunc-code-left-2-trunc-pushout-code-left-2-decomposition-trunc-pushout-span-pushout :
    (m : 𝕋) →
    (H : connected-join-hypothesis-span-pushout m) →
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    type-trunc m
      ( pushout
        ( map-trunc m (map-code-left-0-code-left-1-span-pushout x0 x1 r))
        ( map-trunc m (map-code-left-0-code-left-2-span-pushout x0 x1 r))) ≃
    type-trunc m
      ( pushout
        ( map-trunc m (map-code-left-0-code-left-1-span-pushout x0 x1 r))
        ( map-trunc
          ( m)
          ( map-code-left-0-code-left-2-decomposition-span-pushout
            x0 x1 y1 q11 r)))
  equiv-trunc-code-left-2-trunc-pushout-code-left-2-decomposition-trunc-pushout-span-pushout
    m H x0 x1 y1 q11 r =
    inv-equiv
      ( equiv-trunc m
        ( equiv-code-left-2-decomposition-trunc-pushout-code-left-2-trunc-pushout-span-pushout
          m H x0 x1 y1 q11 r))

  code-left-1-code-left-2-decomposition-pushout-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1) →
    inl-span-pushout Q x0 ＝ inl-span-pushout Q x1 →
    UU (l1 ⊔ l2 ⊔ l3)
  code-left-1-code-left-2-decomposition-pushout-span-pushout
    x0 x1 y1 q11 r =
    pushout
      ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
      ( map-code-left-0-code-left-2-decomposition-span-pushout
        x0 x1 y1 q11 r)

  equiv-code-left-code-left-1-code-left-2-decomposition-pushout-span-pushout :
    (m : 𝕋) →
    (H : connected-join-hypothesis-span-pushout m) →
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-span-pushout m x0 x1 r ≃
    type-trunc m
      ( code-left-1-code-left-2-decomposition-pushout-span-pushout
        x0 x1 y1 q11 r)
  equiv-code-left-code-left-1-code-left-2-decomposition-pushout-span-pushout
    m H x0 x1 y1 q11 r =
    inv-equiv
      ( equiv-trunc-pushout-pushout-trunc-span
        ( m)
        ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
        ( map-code-left-0-code-left-2-decomposition-span-pushout
          x0 x1 y1 q11 r)) ∘e
    equiv-trunc-code-left-2-trunc-pushout-code-left-2-decomposition-trunc-pushout-span-pushout
      ( m)
      ( H)
      ( x0)
      ( x1)
      ( y1)
      ( q11)
      ( r) ∘e
    equiv-trunc-pushout-pushout-trunc-span
      ( m)
      ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
      ( map-code-left-0-code-left-2-span-pushout x0 x1 r)

  code-left-1-code-left-2b-pushout-span-pushout :
    (x0 x1 : X) →
    inl-span-pushout Q x0 ＝ inl-span-pushout Q x1 →
    UU (l1 ⊔ l2 ⊔ l3)
  code-left-1-code-left-2b-pushout-span-pushout x0 x1 r =
    pushout
      ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
      ( map-code-left-0-code-left-2b-span-pushout x0 x1 r)

  cocone-code-left-1-code-left-2b-pushout-code-left-1-span-pushout :
    (x0 x1 : X)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    cocone
      ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
      ( map-code-left-0-code-left-2b-span-pushout x0 x1 r)
      ( code-left-1-span-pushout x0 x1 r)
  pr1
    ( cocone-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
      x0 x1 r) =
    id
  pr1
    ( pr2
      ( cocone-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
        x0 x1 r)) =
    map-code-left-0-code-left-1-span-pushout x0 x1 r ∘
    map-inv-code-left-0-code-left-2b-span-pushout x0 x1 r
  pr2
    ( pr2
      ( cocone-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
        x0 x1 r)) c0 =
    inv
      ( ap
        ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
        ( is-retraction-map-inv-code-left-0-code-left-2b-span-pushout
          x0 x1 r c0))

  map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout :
    (x0 x1 : X)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-1-code-left-2b-pushout-span-pushout x0 x1 r →
    code-left-1-span-pushout x0 x1 r
  map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
    x0 x1 r =
    cogap
      ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
      ( map-code-left-0-code-left-2b-span-pushout x0 x1 r)
      ( cocone-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
        x0 x1 r)

  compute-inl-map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout :
    (x0 x1 : X)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
      x0 x1 r ∘
    inl-pushout
      ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
      ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ~
    id
  compute-inl-map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
    x0 x1 r =
    compute-inl-cogap
      ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
      ( map-code-left-0-code-left-2b-span-pushout x0 x1 r)
      ( cocone-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
        x0 x1 r)

  compute-inr-map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout :
    (x0 x1 : X)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
      x0 x1 r ∘
    inr-pushout
      ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
      ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ~
    map-code-left-0-code-left-1-span-pushout x0 x1 r ∘
    map-inv-code-left-0-code-left-2b-span-pushout x0 x1 r
  compute-inr-map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
    x0 x1 r =
    compute-inr-cogap
      ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
      ( map-code-left-0-code-left-2b-span-pushout x0 x1 r)
      ( cocone-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
        x0 x1 r)

  is-equiv-map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout :
    (x0 x1 : X)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    is-equiv
      ( map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
        x0 x1 r)
  is-equiv-map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
    x0 x1 r =
    is-equiv-is-retraction
      ( is-equiv-inl-pushout-is-equiv-right-map
        ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
        ( map-code-left-0-code-left-2b-span-pushout x0 x1 r)
        ( is-equiv-map-code-left-0-code-left-2b-span-pushout x0 x1 r))
      ( compute-inl-map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
        x0 x1 r)

  equiv-code-left-1-code-left-2b-pushout-code-left-1-span-pushout :
    (x0 x1 : X)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-1-code-left-2b-pushout-span-pushout x0 x1 r ≃
    code-left-1-span-pushout x0 x1 r
  pr1
    ( equiv-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
      x0 x1 r) =
    map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout x0 x1 r
  pr2
    ( equiv-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
      x0 x1 r) =
    is-equiv-map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
      x0 x1 r

  code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1) →
    inl-span-pushout Q x0 ＝ inl-span-pushout Q x1 →
    UU (l1 ⊔ l2 ⊔ l3)
  code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout
    x0 x1 y1 q11 r =
    pushout
      ( inr-pushout
        ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
        ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ∘
        map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)

  equiv-code-left-1-code-left-2-decomposition-pushout-code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-1-code-left-2-decomposition-pushout-span-pushout
      x0 x1 y1 q11 r ≃
    code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout
      x0 x1 y1 q11 r
  equiv-code-left-1-code-left-2-decomposition-pushout-code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout
    x0 x1 y1 q11 r =
    inv-equiv
      ( equiv-left-associated-right-associated-pushout-pushout
        ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
        ( map-code-left-0-code-left-2b-span-pushout x0 x1 r)
        ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r))

  equiv-trunc-code-left-1-code-left-2-decomposition-pushout-code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout :
    (m : 𝕋) (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    type-trunc m
      ( code-left-1-code-left-2-decomposition-pushout-span-pushout
        x0 x1 y1 q11 r) ≃
    type-trunc m
      ( code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout
        x0 x1 y1 q11 r)
  equiv-trunc-code-left-1-code-left-2-decomposition-pushout-code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout
    m x0 x1 y1 q11 r =
    equiv-trunc m
      ( equiv-code-left-1-code-left-2-decomposition-pushout-code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout
        x0 x1 y1 q11 r)

  code-left-2a1-code-left-2c-pushout-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1) →
    inl-span-pushout Q x0 ＝ inl-span-pushout Q x1 →
    UU (l1 ⊔ l2 ⊔ l3)
  code-left-2a1-code-left-2c-pushout-span-pushout x0 x1 y1 q11 r =
    pushout
      ( map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)

  coherence-left-square-code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    coherence-square-maps
      ( id)
      ( inr-pushout
        ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
        ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ∘
        map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
        x0 x1 r)
  coherence-left-square-code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout
    x0 x1 y1 q11 r a =
    compute-inr-map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
      ( x0)
      ( x1)
      ( r)
      ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r a) ∙
    inv
      ( htpy-map-code-left-2a-code-left-1-through-code-left-2b-span-pushout
        x0 x1 y1 q11 r a)

  coherence-right-square-code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    coherence-square-maps
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
      ( id)
      ( id)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
  coherence-right-square-code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout
    x0 x1 y1 q11 r =
    refl-htpy

  cocone-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    cocone
      ( inr-pushout
        ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
        ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ∘
        map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
      ( code-left-2a1-code-left-2c-pushout-span-pushout
        x0 x1 y1 q11 r)
  cocone-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
    x0 x1 y1 q11 r =
    comp-cocone-hom-span
      ( map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
      ( inr-pushout
        ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
        ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ∘
        map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
        x0 x1 r)
      ( id)
      ( id)
      ( cocone-pushout
        ( map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r))
      ( coherence-left-square-code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout
        x0 x1 y1 q11 r)
      ( coherence-right-square-code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout
        x0 x1 y1 q11 r)

  universal-property-pushout-cocone-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    universal-property-pushout
      ( inr-pushout
        ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
        ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ∘
        map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
      ( cocone-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
        x0 x1 y1 q11 r)
  universal-property-pushout-cocone-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
    x0 x1 y1 q11 r =
    universal-property-pushout-extended-by-equivalences
      ( map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
      ( inr-pushout
        ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
        ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ∘
        map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
        x0 x1 r)
      ( id)
      ( id)
      ( cocone-pushout
        ( map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r))
      ( up-pushout
        ( map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r))
      ( coherence-left-square-code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout
        x0 x1 y1 q11 r)
      ( coherence-right-square-code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout
        x0 x1 y1 q11 r)
      ( is-equiv-map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
        x0 x1 r)
      ( is-equiv-id)
      ( is-equiv-id)

  map-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout
      x0 x1 y1 q11 r →
    code-left-2a1-code-left-2c-pushout-span-pushout x0 x1 y1 q11 r
  map-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
    x0 x1 y1 q11 r =
    cogap
      ( inr-pushout
        ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
        ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ∘
        map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
      ( cocone-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
        x0 x1 y1 q11 r)

  is-equiv-map-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    is-equiv
      ( map-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
        x0 x1 y1 q11 r)
  is-equiv-map-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
    x0 x1 y1 q11 r =
    is-equiv-up-pushout-up-pushout
      ( inr-pushout
        ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
        ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ∘
        map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
      ( cocone-pushout
        ( inr-pushout
          ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
          ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ∘
          map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r))
      ( cocone-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
        x0 x1 y1 q11 r)
      ( map-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
        x0 x1 y1 q11 r)
      ( htpy-compute-cogap
        ( inr-pushout
          ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
          ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ∘
          map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
        ( cocone-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
          x0 x1 y1 q11 r))
      ( up-pushout
        ( inr-pushout
          ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
          ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ∘
          map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r))
      ( universal-property-pushout-cocone-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
        x0 x1 y1 q11 r)

  equiv-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout
      x0 x1 y1 q11 r ≃
    code-left-2a1-code-left-2c-pushout-span-pushout x0 x1 y1 q11 r
  pr1
    ( equiv-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
      x0 x1 y1 q11 r) =
    map-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
      x0 x1 y1 q11 r
  pr2
    ( equiv-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
      x0 x1 y1 q11 r) =
    is-equiv-map-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
      x0 x1 y1 q11 r

  equiv-trunc-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout :
    (m : 𝕋) (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    type-trunc m
      ( code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout
        x0 x1 y1 q11 r) ≃
    type-trunc m
      ( code-left-2a1-code-left-2c-pushout-span-pushout
        x0 x1 y1 q11 r)
  equiv-trunc-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
    m x0 x1 y1 q11 r =
    equiv-trunc m
      ( equiv-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
        x0 x1 y1 q11 r)

  equiv-code-left-2a1-code-left-2c-pushout-code-left-2c-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-2a1-code-left-2c-pushout-span-pushout x0 x1 y1 q11 r ≃
    code-left-2c-span-pushout x0 x1 y1 q11 r
  equiv-code-left-2a1-code-left-2c-pushout-code-left-2c-span-pushout
    x0 x1 y1 q11 r =
    inv-equiv
      ( equiv-inr-pushout-is-equiv-left-map
        ( map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
        ( is-equiv-map-code-left-2a-code-left-1-span-pushout
          x0 x1 y1 q11 r))

  equiv-trunc-code-left-2a1-code-left-2c-pushout-code-left-2c-span-pushout :
    (m : 𝕋) (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    type-trunc m
      ( code-left-2a1-code-left-2c-pushout-span-pushout x0 x1 y1 q11 r) ≃
    type-trunc m (code-left-2c-span-pushout x0 x1 y1 q11 r)
  equiv-trunc-code-left-2a1-code-left-2c-pushout-code-left-2c-span-pushout
    m x0 x1 y1 q11 r =
    equiv-trunc m
      ( equiv-code-left-2a1-code-left-2c-pushout-code-left-2c-span-pushout
        x0 x1 y1 q11 r)

  equiv-code-left-2c-fiber-glue-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-2c-span-pushout x0 x1 y1 q11 r ≃
    fiber
      ( glue-span-pushout Q x0 y1)
      ( r ∙ glue-span-pushout Q x1 y1 q11)
  equiv-code-left-2c-fiber-glue-span-pushout x0 x1 y1 q11 r =
    equiv-tot
      ( λ q01 →
        equiv-concat'
          ( glue-span-pushout Q x0 y1 q01)
          ( ap (r ∙_) (inv-inv (glue-span-pushout Q x1 y1 q11))) ∘e
        equiv-right-transpose-eq-concat
          ( glue-span-pushout Q x0 y1 q01)
          ( inv (glue-span-pushout Q x1 y1 q11))
          ( r))

  equiv-trunc-code-left-2c-code-right-span-pushout :
    (m : 𝕋) (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    type-trunc m (code-left-2c-span-pushout x0 x1 y1 q11 r) ≃
    code-right-span-pushout
      ( m)
      ( x0)
      ( y1)
      ( r ∙ glue-span-pushout Q x1 y1 q11)
  equiv-trunc-code-left-2c-code-right-span-pushout m x0 x1 y1 q11 r =
    equiv-trunc m
      ( equiv-code-left-2c-fiber-glue-span-pushout x0 x1 y1 q11 r)

  compute-equiv-trunc-code-left-2c-code-right-span-pushout :
    (m : 𝕋) (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (c : code-left-2c-span-pushout x0 x1 y1 q11 r) →
    map-equiv
      ( equiv-trunc-code-left-2c-code-right-span-pushout
        m x0 x1 y1 q11 r)
      ( unit-trunc c) ＝
    unit-trunc
      ( map-equiv
        ( equiv-code-left-2c-fiber-glue-span-pushout x0 x1 y1 q11 r)
        ( c))
  compute-equiv-trunc-code-left-2c-code-right-span-pushout
    m x0 x1 y1 q11 r =
    naturality-unit-trunc
      ( m)
      ( map-equiv
        ( equiv-code-left-2c-fiber-glue-span-pushout x0 x1 y1 q11 r))

  equiv-trunc-code-left-1-code-left-2-decomposition-pushout-code-right-span-pushout :
    (m : 𝕋) (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    type-trunc m
      ( code-left-1-code-left-2-decomposition-pushout-span-pushout
        x0 x1 y1 q11 r) ≃
    code-right-span-pushout
      ( m)
      ( x0)
      ( y1)
      ( r ∙ glue-span-pushout Q x1 y1 q11)
  equiv-trunc-code-left-1-code-left-2-decomposition-pushout-code-right-span-pushout
    m x0 x1 y1 q11 r =
    equiv-trunc-code-left-2c-code-right-span-pushout m x0 x1 y1 q11 r ∘e
    equiv-trunc-code-left-2a1-code-left-2c-pushout-code-left-2c-span-pushout
      m x0 x1 y1 q11 r ∘e
    equiv-trunc-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
      m x0 x1 y1 q11 r ∘e
    equiv-trunc-code-left-1-code-left-2-decomposition-pushout-code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout
      m x0 x1 y1 q11 r

  equiv-code-left-code-right-span-pushout :
    (m : 𝕋) →
    (H : connected-join-hypothesis-span-pushout m) →
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-span-pushout m x0 x1 r ≃
    code-right-span-pushout
      ( m)
      ( x0)
      ( y1)
      ( r ∙ glue-span-pushout Q x1 y1 q11)
  equiv-code-left-code-right-span-pushout m H x0 x1 y1 q11 r =
    equiv-trunc-code-left-1-code-left-2-decomposition-pushout-code-right-span-pushout
      m x0 x1 y1 q11 r ∘e
    equiv-code-left-code-left-1-code-left-2-decomposition-pushout-span-pushout
      m H x0 x1 y1 q11 r

  code-motive-span-pushout :
    (x0 : X) → span-pushout Q → UU (lsuc (l1 ⊔ l2 ⊔ l3))
  code-motive-span-pushout x0 p =
    inl-span-pushout Q x0 ＝ p → UU (l1 ⊔ l2 ⊔ l3)

  dependent-identification-code-glue-span-pushout :
    (m : 𝕋) →
    (H : connected-join-hypothesis-span-pushout m) →
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1) →
    dependent-identification
      ( code-motive-span-pushout x0)
      ( glue-span-pushout Q x1 y1 q11)
      ( code-left-span-pushout m x0 x1)
      ( code-right-span-pushout m x0 y1)
  pointwise-dependent-identification-code-glue-span-pushout :
    (m : 𝕋) →
    (H : connected-join-hypothesis-span-pushout m) →
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1) →
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1) →
    code-left-span-pushout m x0 x1 r ＝
    code-right-span-pushout
      ( m)
      ( x0)
      ( y1)
      ( tr
        ( λ p → inl-span-pushout Q x0 ＝ p)
        ( glue-span-pushout Q x1 y1 q11)
        ( r))
  pointwise-dependent-identification-code-glue-span-pushout
    m H x0 x1 y1 q11 r =
    eq-equiv
      ( equiv-tr
        ( code-right-span-pushout m x0 y1)
        ( inv
          ( tr-Id-right
            ( glue-span-pushout Q x1 y1 q11)
            ( r))) ∘e
        equiv-code-left-code-right-span-pushout
          ( m)
          ( H)
          ( x0)
          ( x1)
          ( y1)
          ( q11)
          ( r))

  dependent-identification-code-glue-span-pushout m H x0 x1 y1 q11 =
    map-compute-dependent-identification-function-type-fixed-codomain
      ( λ p → inl-span-pushout Q x0 ＝ p)
      ( UU (l1 ⊔ l2 ⊔ l3))
      ( glue-span-pushout Q x1 y1 q11)
      ( code-left-span-pushout m x0 x1)
      ( code-right-span-pushout m x0 y1)
      ( pointwise-dependent-identification-code-glue-span-pushout
        m H x0 x1 y1 q11)

  code-span-pushout :
    (m : 𝕋) →
    connected-join-hypothesis-span-pushout m →
    (x0 : X) (p : span-pushout Q) →
    inl-span-pushout Q x0 ＝ p → UU (l1 ⊔ l2 ⊔ l3)
  code-span-pushout m H x0 =
    ind-span-pushout
      ( Q)
      ( code-left-span-pushout m x0)
      ( code-right-span-pushout m x0)
      ( dependent-identification-code-glue-span-pushout m H x0)

  compute-inl-code-span-pushout :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 x1 : X) →
    code-span-pushout m H x0 (inl-span-pushout Q x1) ＝
    code-left-span-pushout m x0 x1
  compute-inl-code-span-pushout m H x0 =
    compute-inl-ind-span-pushout
      ( Q)
      ( code-left-span-pushout m x0)
      ( code-right-span-pushout m x0)
      ( dependent-identification-code-glue-span-pushout m H x0)

  compute-inr-code-span-pushout :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 : X) (y1 : Y) →
    code-span-pushout m H x0 (inr-span-pushout Q y1) ＝
    code-right-span-pushout m x0 y1
  compute-inr-code-span-pushout m H x0 =
    compute-inr-ind-span-pushout
      ( Q)
      ( code-left-span-pushout m x0)
      ( code-right-span-pushout m x0)
      ( dependent-identification-code-glue-span-pushout m H x0)

  compute-glue-code-span-pushout :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1) →
    ( apd
      ( code-span-pushout m H x0)
      ( glue-span-pushout Q x1 y1 q11) ∙
      compute-inr-code-span-pushout m H x0 y1) ＝
    ( ap
      ( tr
        ( code-motive-span-pushout x0)
        ( glue-span-pushout Q x1 y1 q11))
      ( compute-inl-code-span-pushout m H x0 x1) ∙
      dependent-identification-code-glue-span-pushout m H x0 x1 y1 q11)
  compute-glue-code-span-pushout m H x0 x1 y1 q11 =
    compute-glue-ind-span-pushout
      ( Q)
      ( code-left-span-pushout m x0)
      ( code-right-span-pushout m x0)
      ( dependent-identification-code-glue-span-pushout m H x0)
      ( x1 , y1 , q11)

  center-code-left-span-pushout :
    (m : 𝕋) (x0 : X) →
    code-left-span-pushout m x0 x0 refl
  center-code-left-span-pushout m x0 =
    unit-trunc
      ( inl-pushout
        ( map-code-left-0-code-left-1-span-pushout x0 x0 refl)
        ( map-code-left-0-code-left-2-span-pushout x0 x0 refl)
        ( refl , refl))

  center-code-span-pushout-base :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 : X) →
    code-span-pushout m H x0 (inl-span-pushout Q x0) refl
  center-code-span-pushout-base m H x0 =
    tr
      ( λ C → C refl)
      ( inv (compute-inl-code-span-pushout m H x0 x0))
      ( center-code-left-span-pushout m x0)

  center-code-span-pushout :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 : X) (p : span-pushout Q)
    (r : inl-span-pushout Q x0 ＝ p) →
    code-span-pushout m H x0 p r
  center-code-span-pushout m H x0 .(inl-span-pushout Q x0) refl =
    center-code-span-pushout-base m H x0

  center-code-right-span-pushout :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 : X) (y1 : Y)
    (r : inl-span-pushout Q x0 ＝ inr-span-pushout Q y1) →
    code-right-span-pushout m x0 y1 r
  center-code-right-span-pushout m H x0 y1 r =
    tr
      ( λ C → C r)
      ( compute-inr-code-span-pushout m H x0 y1)
      ( center-code-span-pushout m H x0 (inr-span-pushout Q y1) r)

  eq-based-path-span-pushout :
    (x0 : X) (p : span-pushout Q)
    (r : inl-span-pushout Q x0 ＝ p) →
    ( inl-span-pushout Q x0 , refl) ＝ (p , r)
  eq-based-path-span-pushout x0 p r =
    eq-pair-Σ r (tr-Id-right r refl)

  compute-center-code-span-pushout-total :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 : X) (p : span-pushout Q)
    (r : inl-span-pushout Q x0 ＝ p) →
    center-code-span-pushout m H x0 p r ＝
    tr
      ( λ z → code-span-pushout m H x0 (pr1 z) (pr2 z))
      ( eq-based-path-span-pushout x0 p r)
      ( center-code-span-pushout-base m H x0)
  compute-center-code-span-pushout-total m H x0 .(inl-span-pushout Q x0) refl =
    refl

  compute-equiv-trunc-pushout-pushout-trunc-span-inl :
    {l4 l5 l6 : Level} {S : UU l4} {A : UU l5} {B : UU l6}
    (m : 𝕋) (f : S → A) (g : S → B) (a : A) →
    map-equiv
      ( equiv-trunc-pushout-pushout-trunc-span m f g)
      ( unit-trunc (inl-pushout f g a)) ＝
    unit-trunc
      ( inl-pushout (map-trunc m f) (map-trunc m g) (unit-trunc a))
  compute-equiv-trunc-pushout-pushout-trunc-span-inl m f g a =
    naturality-unit-trunc
      ( m)
      ( map-pushout-trunc-span m f g)
      ( inl-pushout f g a) ∙
    ap unit-trunc (compute-inl-map-pushout-trunc-span m f g a)

  compute-inv-equiv-trunc-pushout-pushout-trunc-span-inl :
    {l4 l5 l6 : Level} {S : UU l4} {A : UU l5} {B : UU l6}
    (m : 𝕋) (f : S → A) (g : S → B) (a : A) →
    map-equiv
      ( inv-equiv (equiv-trunc-pushout-pushout-trunc-span m f g))
      ( unit-trunc
        ( inl-pushout (map-trunc m f) (map-trunc m g) (unit-trunc a))) ＝
    unit-trunc (inl-pushout f g a)
  compute-inv-equiv-trunc-pushout-pushout-trunc-span-inl m f g a =
    is-injective-equiv
      ( equiv-trunc-pushout-pushout-trunc-span m f g)
      ( is-section-map-inv-equiv
        ( equiv-trunc-pushout-pushout-trunc-span m f g)
        ( unit-trunc
          ( inl-pushout (map-trunc m f) (map-trunc m g) (unit-trunc a))) ∙
        inv (compute-equiv-trunc-pushout-pushout-trunc-span-inl m f g a))

  compute-section-equiv-trunc-inv-equiv-unit :
    {l4 l5 : Level} {A : UU l4} {B : UU l5}
    (m : 𝕋) (e : A ≃ B) (b : B) →
    map-equiv (equiv-trunc m e)
      ( map-equiv (equiv-trunc m (inv-equiv e)) (unit-trunc b)) ＝
    unit-trunc b
  compute-section-equiv-trunc-inv-equiv-unit m e b =
    ap
      ( map-equiv (equiv-trunc m e))
      ( naturality-unit-trunc m (map-inv-equiv e) b) ∙
    naturality-unit-trunc m (map-equiv e) (map-inv-equiv e b) ∙
    ap unit-trunc (is-section-map-inv-equiv e b)

  compute-tr-eq-equiv :
    {l4 : Level} {A B : UU l4}
    (e : A ≃ B) (a : A) →
    tr (λ X → X) (eq-equiv e) a ＝ map-equiv e a
  compute-tr-eq-equiv e a =
    ap (λ e' → map-equiv e' a) (is-section-eq-equiv e)

  compute-tr-eq-pair-Σ-map-inv-compute-dependent-identification-function-type-fixed-codomain :
    {l4 l5 l6 : Level} {A : UU l4} {a0 a1 : A}
    (B : A → UU l5) (F : (a : A) → B a → UU l6)
    (p : a0 ＝ a1) {b0 : B a0} {b1 : B a1}
    (q : tr B p b0 ＝ b1) (u : F a0 b0) →
    tr (λ z → F (pr1 z) (pr2 z)) (eq-pair-Σ p q) u ＝
    tr
      ( λ b → F a1 b)
      ( q)
      ( tr
        ( λ (C : UU l6) → C)
        ( map-inv-equiv
          ( compute-dependent-identification-function-type-fixed-codomain
            ( B)
            ( UU l6)
            ( p)
            ( F a0)
            ( F a1))
          ( apd F p)
          ( b0))
        ( u))
  compute-tr-eq-pair-Σ-map-inv-compute-dependent-identification-function-type-fixed-codomain
    B F refl refl u =
    refl

  compute-tr-eq-pair-Σ-map-inv-compute-dependent-identification-function-type-fixed-codomain-concat :
    {l4 l5 l6 : Level} {A : UU l4} {a0 a1 : A}
    (B : A → UU l5) (F : (a : A) → B a → UU l6)
    (p : a0 ＝ a1) {b0 : B a0} {b1 : B a1}
    (q : tr B p b0 ＝ b1) (G : B a1 → UU l6)
    (e : F a1 ＝ G) (u : F a0 b0) →
    tr
      ( λ C → C b1)
      ( e)
      ( tr (λ z → F (pr1 z) (pr2 z)) (eq-pair-Σ p q) u) ＝
    tr
      ( G)
      ( q)
      ( tr
        ( λ (C : UU l6) → C)
        ( map-inv-equiv
          ( compute-dependent-identification-function-type-fixed-codomain
            ( B)
            ( UU l6)
            ( p)
            ( F a0)
            ( G))
          ( apd F p ∙ e)
          ( b0))
        ( u))
  compute-tr-eq-pair-Σ-map-inv-compute-dependent-identification-function-type-fixed-codomain-concat
    B F refl refl G refl u =
    refl

  compute-tr-map-inv-compute-dependent-identification-function-type-fixed-codomain-ap :
    {l4 l5 l6 : Level} {A : UU l4} {a0 a1 : A}
    (B : A → UU l5) (p : a0 ＝ a1)
    (F F' : B a0 → UU l6) (G : B a1 → UU l6)
    (e : F ＝ F')
    (h : (b : B a0) → F' b ＝ G (tr B p b))
    (b0 : B a0) (u : F' b0) →
    tr
      ( λ (C : UU l6) → C)
      ( map-inv-equiv
        ( compute-dependent-identification-function-type-fixed-codomain
          ( B)
          ( UU l6)
          ( p)
          ( F)
          ( G))
        ( ap
          ( tr (λ a → B a → UU l6) p)
          ( e) ∙
          map-compute-dependent-identification-function-type-fixed-codomain
            ( B)
            ( UU l6)
            ( p)
            ( F')
            ( G)
            ( h))
        ( b0))
      ( tr (λ C → C b0) (inv e) u) ＝
    tr
      ( λ (C : UU l6) → C)
      ( h b0)
      ( u)
  compute-tr-map-inv-compute-dependent-identification-function-type-fixed-codomain-ap
    B refl F .F G refl h b0 u =
    ap
      ( λ α → tr (λ (C : UU _) → C) α u)
      ( htpy-eq (is-section-eq-htpy h) b0)

  compute-left-associated-right-associated-pushout-pushout-inl-inl :
    {l4 l5 l6 l7 l8 : Level}
    {A₁ : UU l4} {B : UU l5} {C : UU l6} {A₂ : UU l7} {D : UU l8}
    (f₁ : A₁ → B) (g₁ : A₁ → C) (f₂ : A₂ → C) (g₂ : A₂ → D)
    (b : B) →
    map-equiv
      ( equiv-left-associated-right-associated-pushout-pushout f₁ g₁ f₂ g₂)
      ( inl-pushout
        ( inr-pushout f₁ g₁ ∘ f₂)
        ( g₂)
        ( inl-pushout f₁ g₁ b)) ＝
    inl-pushout f₁ (inl-pushout f₂ g₂ ∘ g₁) b
  compute-left-associated-right-associated-pushout-pushout-inl-inl
    f₁ g₁ f₂ g₂ b =
    compute-inl-cogap
      ( inr-pushout f₁ g₁ ∘ f₂)
      ( g₂)
      ( cocone-left-associated-span-right-associated-pushout-pushout
        f₁ g₁ f₂ g₂)
      ( inl-pushout f₁ g₁ b) ∙
    compute-inl-map-left-pushout-right-associated-pushout-pushout
      f₁ g₁ f₂ g₂ b

  compute-equiv-code-left-2-decomposition-trunc-pushout-code-left-2-trunc-pushout-inl-span-pushout :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (a : code-left-1-span-pushout x0 x1 r) →
    map-equiv
      ( equiv-code-left-2-decomposition-trunc-pushout-code-left-2-trunc-pushout-span-pushout
        ( m)
        ( H)
        ( x0)
        ( x1)
        ( y1)
        ( q11)
        ( r))
      ( inl-pushout
        ( map-trunc m (map-code-left-0-code-left-1-span-pushout x0 x1 r))
        ( map-trunc
          ( m)
          ( map-code-left-0-code-left-2-decomposition-span-pushout
            x0 x1 y1 q11 r))
        ( unit-trunc a)) ＝
    inl-pushout
      ( map-trunc m (map-code-left-0-code-left-1-span-pushout x0 x1 r))
      ( map-trunc m (map-code-left-0-code-left-2-span-pushout x0 x1 r))
      ( unit-trunc a)

  compute-equiv-trunc-code-left-2-trunc-pushout-code-left-2-decomposition-trunc-pushout-inl-span-pushout :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (a : code-left-1-span-pushout x0 x1 r) →
    map-equiv
      ( equiv-trunc-code-left-2-trunc-pushout-code-left-2-decomposition-trunc-pushout-span-pushout
        ( m)
        ( H)
        ( x0)
        ( x1)
        ( y1)
        ( q11)
        ( r))
      ( unit-trunc
        ( inl-pushout
          ( map-trunc m (map-code-left-0-code-left-1-span-pushout x0 x1 r))
          ( map-trunc m (map-code-left-0-code-left-2-span-pushout x0 x1 r))
          ( unit-trunc a))) ＝
    unit-trunc
      ( inl-pushout
        ( map-trunc m (map-code-left-0-code-left-1-span-pushout x0 x1 r))
        ( map-trunc
          ( m)
          ( map-code-left-0-code-left-2-decomposition-span-pushout
            x0 x1 y1 q11 r))
        ( unit-trunc a))
  compute-equiv-trunc-code-left-2-trunc-pushout-code-left-2-decomposition-trunc-pushout-inl-span-pushout
    m H x0 x1 y1 q11 r a =
    is-injective-equiv
      ( equiv-trunc m
        ( equiv-code-left-2-decomposition-trunc-pushout-code-left-2-trunc-pushout-span-pushout
          m H x0 x1 y1 q11 r))
      ( is-section-map-inv-equiv
        ( equiv-trunc m
          ( equiv-code-left-2-decomposition-trunc-pushout-code-left-2-trunc-pushout-span-pushout
            m H x0 x1 y1 q11 r))
        ( unit-trunc
          ( inl-pushout
            ( map-trunc m (map-code-left-0-code-left-1-span-pushout x0 x1 r))
            ( map-trunc m (map-code-left-0-code-left-2-span-pushout x0 x1 r))
            ( unit-trunc a))) ∙
        inv
          ( naturality-unit-trunc
            ( m)
            ( map-equiv
              ( equiv-code-left-2-decomposition-trunc-pushout-code-left-2-trunc-pushout-span-pushout
                m H x0 x1 y1 q11 r))
            ( inl-pushout
              ( map-trunc m
                ( map-code-left-0-code-left-1-span-pushout x0 x1 r))
              ( map-trunc
                ( m)
                ( map-code-left-0-code-left-2-decomposition-span-pushout
                  x0 x1 y1 q11 r))
              ( unit-trunc a)) ∙
            ap
              ( unit-trunc)
              ( compute-equiv-code-left-2-decomposition-trunc-pushout-code-left-2-trunc-pushout-inl-span-pushout
                m H x0 x1 y1 q11 r a)))

  compute-equiv-code-left-decomposition-center-glue-span-pushout :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 : X) (y1 : Y) (q01 : Q x0 y1) →
    map-equiv
      ( equiv-code-left-code-left-1-code-left-2-decomposition-pushout-span-pushout
        ( m)
        ( H)
        ( x0)
        ( x0)
        ( y1)
        ( q01)
        ( refl))
      ( center-code-left-span-pushout m x0) ＝
    unit-trunc
      ( inl-pushout
        ( map-code-left-0-code-left-1-span-pushout x0 x0 refl)
        ( map-code-left-0-code-left-2-decomposition-span-pushout
          x0 x0 y1 q01 refl)
        ( refl , refl))
  compute-equiv-code-left-decomposition-center-glue-span-pushout
    m H x0 y1 q01 =
    equational-reasoning
      map-equiv
        ( equiv-code-left-code-left-1-code-left-2-decomposition-pushout-span-pushout
          m H x0 x0 y1 q01 refl)
        ( center-code-left-span-pushout m x0)
      ＝
      map-equiv
        ( inv-equiv
          ( equiv-trunc-pushout-pushout-trunc-span
            ( m)
            ( map-code-left-0-code-left-1-span-pushout x0 x0 refl)
            ( map-code-left-0-code-left-2-decomposition-span-pushout
              x0 x0 y1 q01 refl)))
        ( map-equiv
          ( equiv-trunc-code-left-2-trunc-pushout-code-left-2-decomposition-trunc-pushout-span-pushout
            m H x0 x0 y1 q01 refl)
          ( map-equiv
            ( equiv-trunc-pushout-pushout-trunc-span
              ( m)
              ( map-code-left-0-code-left-1-span-pushout x0 x0 refl)
              ( map-code-left-0-code-left-2-span-pushout x0 x0 refl))
            ( center-code-left-span-pushout m x0)))
        by refl
      ＝
      map-equiv
        ( inv-equiv
          ( equiv-trunc-pushout-pushout-trunc-span
            ( m)
            ( map-code-left-0-code-left-1-span-pushout x0 x0 refl)
            ( map-code-left-0-code-left-2-decomposition-span-pushout
              x0 x0 y1 q01 refl)))
        ( map-equiv
          ( equiv-trunc-code-left-2-trunc-pushout-code-left-2-decomposition-trunc-pushout-span-pushout
            m H x0 x0 y1 q01 refl)
          ( unit-trunc
            ( inl-pushout
              ( map-trunc m
                ( map-code-left-0-code-left-1-span-pushout x0 x0 refl))
              ( map-trunc m
                ( map-code-left-0-code-left-2-span-pushout x0 x0 refl))
              ( unit-trunc (refl , refl)))))
        by
        ap
          ( map-equiv
            ( inv-equiv
              ( equiv-trunc-pushout-pushout-trunc-span
                ( m)
                ( map-code-left-0-code-left-1-span-pushout x0 x0 refl)
                ( map-code-left-0-code-left-2-decomposition-span-pushout
                  x0 x0 y1 q01 refl))) ∘
            map-equiv
              ( equiv-trunc-code-left-2-trunc-pushout-code-left-2-decomposition-trunc-pushout-span-pushout
                m H x0 x0 y1 q01 refl))
          ( compute-equiv-trunc-pushout-pushout-trunc-span-inl
            ( m)
            ( map-code-left-0-code-left-1-span-pushout x0 x0 refl)
            ( map-code-left-0-code-left-2-span-pushout x0 x0 refl)
            ( refl , refl))
      ＝
      map-equiv
        ( inv-equiv
          ( equiv-trunc-pushout-pushout-trunc-span
            ( m)
            ( map-code-left-0-code-left-1-span-pushout x0 x0 refl)
            ( map-code-left-0-code-left-2-decomposition-span-pushout
              x0 x0 y1 q01 refl)))
        ( unit-trunc
          ( inl-pushout
            ( map-trunc m
              ( map-code-left-0-code-left-1-span-pushout x0 x0 refl))
            ( map-trunc
              ( m)
              ( map-code-left-0-code-left-2-decomposition-span-pushout
                x0 x0 y1 q01 refl))
            ( unit-trunc (refl , refl))))
        by
        ap
          ( map-equiv
            ( inv-equiv
              ( equiv-trunc-pushout-pushout-trunc-span
                ( m)
                ( map-code-left-0-code-left-1-span-pushout x0 x0 refl)
                ( map-code-left-0-code-left-2-decomposition-span-pushout
                  x0 x0 y1 q01 refl))))
          ( compute-equiv-trunc-code-left-2-trunc-pushout-code-left-2-decomposition-trunc-pushout-inl-span-pushout
            m H x0 x0 y1 q01 refl (refl , refl))
      ＝
      unit-trunc
        ( inl-pushout
          ( map-code-left-0-code-left-1-span-pushout x0 x0 refl)
          ( map-code-left-0-code-left-2-decomposition-span-pushout
            x0 x0 y1 q01 refl)
          ( refl , refl))
        by
        compute-inv-equiv-trunc-pushout-pushout-trunc-span-inl
          ( m)
          ( map-code-left-0-code-left-1-span-pushout x0 x0 refl)
          ( map-code-left-0-code-left-2-decomposition-span-pushout
            x0 x0 y1 q01 refl)
          ( refl , refl)

  compute-equiv-trunc-code-left-1-code-left-2-decomposition-pushout-code-left-1-code-left-2b-code-left-2c-iterated-pushout-inl-span-pushout :
    (m : 𝕋) (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (a : code-left-1-span-pushout x0 x1 r) →
    map-equiv
      ( equiv-trunc-code-left-1-code-left-2-decomposition-pushout-code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout
        ( m)
        ( x0)
        ( x1)
        ( y1)
        ( q11)
        ( r))
      ( unit-trunc
        ( inl-pushout
          ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
          ( map-code-left-0-code-left-2-decomposition-span-pushout
            x0 x1 y1 q11 r)
          ( a))) ＝
    unit-trunc
      ( inl-pushout
        ( inr-pushout
          ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
          ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ∘
          map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
        ( inl-pushout
          ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
          ( map-code-left-0-code-left-2b-span-pushout x0 x1 r)
          ( a)))
  compute-equiv-trunc-code-left-1-code-left-2-decomposition-pushout-code-left-1-code-left-2b-code-left-2c-iterated-pushout-inl-span-pushout
    m x0 x1 y1 q11 r a =
    is-injective-equiv
      ( equiv-trunc m
        ( equiv-left-associated-right-associated-pushout-pushout
          ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
          ( map-code-left-0-code-left-2b-span-pushout x0 x1 r)
          ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
          ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)))
      ( compute-section-equiv-trunc-inv-equiv-unit
        ( m)
        ( equiv-left-associated-right-associated-pushout-pushout
          ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
          ( map-code-left-0-code-left-2b-span-pushout x0 x1 r)
          ( map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
          ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r))
        ( inl-pushout
          ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
          ( map-code-left-0-code-left-2-decomposition-span-pushout
            x0 x1 y1 q11 r)
          ( a)) ∙
        inv
          ( naturality-unit-trunc
            ( m)
            ( map-equiv
              ( equiv-left-associated-right-associated-pushout-pushout
                ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
                ( map-code-left-0-code-left-2b-span-pushout x0 x1 r)
                ( map-code-left-2a-code-left-2b-span-pushout
                  x0 x1 y1 q11 r)
                ( map-code-left-2a-code-left-2c-span-pushout
                  x0 x1 y1 q11 r)))
            ( inl-pushout
              ( inr-pushout
                ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
                ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ∘
                map-code-left-2a-code-left-2b-span-pushout
                  x0 x1 y1 q11 r)
              ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
              ( inl-pushout
                ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
                ( map-code-left-0-code-left-2b-span-pushout x0 x1 r)
                ( a))) ∙
            ap
              ( unit-trunc)
              ( compute-left-associated-right-associated-pushout-pushout-inl-inl
                ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
                ( map-code-left-0-code-left-2b-span-pushout x0 x1 r)
                ( map-code-left-2a-code-left-2b-span-pushout
                  x0 x1 y1 q11 r)
                ( map-code-left-2a-code-left-2c-span-pushout
                  x0 x1 y1 q11 r)
                ( a))))

  compute-map-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-inl-inl-span-pushout :
    (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (a : code-left-1-span-pushout x0 x1 r) →
    map-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
      ( x0)
      ( x1)
      ( y1)
      ( q11)
      ( r)
      ( inl-pushout
        ( inr-pushout
          ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
          ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ∘
          map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
        ( inl-pushout
          ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
          ( map-code-left-0-code-left-2b-span-pushout x0 x1 r)
          ( a))) ＝
    inl-pushout
      ( map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
      ( a)
  compute-map-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-inl-inl-span-pushout
    x0 x1 y1 q11 r a =
    compute-inl-cogap
      ( inr-pushout
        ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
        ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ∘
        map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
      ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
      ( cocone-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
        x0 x1 y1 q11 r)
      ( inl-pushout
        ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
        ( map-code-left-0-code-left-2b-span-pushout x0 x1 r)
        ( a)) ∙
    ap
      ( inl-pushout
        ( map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r))
      ( compute-inl-map-code-left-1-code-left-2b-pushout-code-left-1-span-pushout
        x0 x1 r a)

  compute-equiv-trunc-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-inl-inl-span-pushout :
    (m : 𝕋) (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (a : code-left-1-span-pushout x0 x1 r) →
    map-equiv
      ( equiv-trunc-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
        ( m)
        ( x0)
        ( x1)
        ( y1)
        ( q11)
        ( r))
      ( unit-trunc
        ( inl-pushout
          ( inr-pushout
            ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
            ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ∘
            map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
          ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
          ( inl-pushout
            ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
            ( map-code-left-0-code-left-2b-span-pushout x0 x1 r)
            ( a)))) ＝
    unit-trunc
      ( inl-pushout
        ( map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
        ( a))
  compute-equiv-trunc-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-inl-inl-span-pushout
    m x0 x1 y1 q11 r a =
    naturality-unit-trunc
      ( m)
      ( map-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
        x0 x1 y1 q11 r)
      ( inl-pushout
        ( inr-pushout
          ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
          ( map-code-left-0-code-left-2b-span-pushout x0 x1 r) ∘
          map-code-left-2a-code-left-2b-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
        ( inl-pushout
          ( map-code-left-0-code-left-1-span-pushout x0 x1 r)
          ( map-code-left-0-code-left-2b-span-pushout x0 x1 r)
          ( a))) ∙
    ap
      ( unit-trunc)
      ( compute-map-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-inl-inl-span-pushout
        x0 x1 y1 q11 r a)

  compute-equiv-trunc-code-left-2a1-code-left-2c-pushout-code-left-2c-inl-span-pushout :
    (m : 𝕋) (x0 x1 : X) (y1 : Y) (q11 : Q x1 y1)
    (r : inl-span-pushout Q x0 ＝ inl-span-pushout Q x1)
    (a : code-left-1-span-pushout x0 x1 r) →
    map-equiv
      ( equiv-trunc-code-left-2a1-code-left-2c-pushout-code-left-2c-span-pushout
        ( m)
        ( x0)
        ( x1)
        ( y1)
        ( q11)
        ( r))
      ( unit-trunc
        ( inl-pushout
          ( map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r)
          ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
          ( a))) ＝
    unit-trunc
      ( map-code-left-2a-code-left-2c-span-pushout
        ( x0)
        ( x1)
        ( y1)
        ( q11)
        ( r)
        ( map-inv-code-left-2a-code-left-1-span-pushout
          x0 x1 y1 q11 r a))
  compute-equiv-trunc-code-left-2a1-code-left-2c-pushout-code-left-2c-inl-span-pushout
    m x0 x1 y1 q11 r a =
    naturality-unit-trunc
      ( m)
      ( map-inv-inr-pushout-is-equiv-left-map
        ( map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
        ( is-equiv-map-code-left-2a-code-left-1-span-pushout
          x0 x1 y1 q11 r))
      ( inl-pushout
        ( map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
        ( a)) ∙
    ap
      ( unit-trunc)
      ( compute-inl-cogap
        ( map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r)
        ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
        ( cocone-inv-inr-pushout-is-equiv-left-map
          ( map-code-left-2a-code-left-1-span-pushout x0 x1 y1 q11 r)
          ( map-code-left-2a-code-left-2c-span-pushout x0 x1 y1 q11 r)
          ( is-equiv-map-code-left-2a-code-left-1-span-pushout
            x0 x1 y1 q11 r))
        ( a))
  compute-equiv-code-left-2-decomposition-trunc-pushout-code-left-2-trunc-pushout-inl-span-pushout
    m H x0 x1 y1 q11 r a =
    compute-inl-cogap
      ( map-trunc m (map-code-left-0-code-left-1-span-pushout x0 x1 r))
      ( map-trunc
        ( m)
        ( map-code-left-0-code-left-2-decomposition-span-pushout
          x0 x1 y1 q11 r))
      ( cocone-pushout-extension-by-equivalences
        ( map-trunc m (map-code-left-0-code-left-1-span-pushout x0 x1 r))
        ( map-trunc m (map-code-left-0-code-left-2-span-pushout x0 x1 r))
        ( map-trunc m (map-code-left-0-code-left-1-span-pushout x0 x1 r))
        ( map-trunc
          ( m)
          ( map-code-left-0-code-left-2-decomposition-span-pushout
            x0 x1 y1 q11 r))
        ( id)
        ( map-equiv
          ( equiv-trunc-code-left-2-decomposition-code-left-2-span-pushout
            m H x0 x1 y1 q11 r))
        ( id)
        ( refl-htpy)
        ( coherence-trunc-code-left-0-code-left-2-decomposition-code-left-2-span-pushout
          m H x0 x1 y1 q11 r)
        ( is-equiv-id)
        ( is-equiv-map-equiv
          ( equiv-trunc-code-left-2-decomposition-code-left-2-span-pushout
            m H x0 x1 y1 q11 r))
        ( is-equiv-id))
      ( unit-trunc a)

  compute-right-transpose-right-inv-inv-inv :
    {l4 : Level} {A : UU l4} {a b : A} (p : a ＝ b) →
    right-transpose-eq-concat p (inv p) refl (right-inv p ∙ refl) ∙
    ap (refl ∙_) (inv-inv p) ＝
    refl
  compute-right-transpose-right-inv-inv-inv refl = refl

  compute-equiv-code-left-2c-fiber-glue-center-span-pushout :
    (x0 : X) (y1 : Y) (q01 : Q x0 y1) →
    map-equiv
      ( equiv-code-left-2c-fiber-glue-span-pushout x0 x0 y1 q01 refl)
      ( map-code-left-2a-code-left-2c-span-pushout
        ( x0)
        ( x0)
        ( y1)
        ( q01)
        ( refl)
        ( map-inv-code-left-2a-code-left-1-span-pushout
          x0 x0 y1 q01 refl (refl , refl))) ＝
    ( q01 , refl)
  compute-equiv-code-left-2c-fiber-glue-center-span-pushout x0 y1 q01 =
    eq-pair-Σ refl
      ( compute-right-transpose-right-inv-inv-inv
        ( glue-span-pushout Q x0 y1 q01))

  compute-equiv-decomposition-code-right-center-glue-span-pushout :
    (m : 𝕋)
    (x0 : X) (y1 : Y) (q01 : Q x0 y1) →
    map-equiv
      ( equiv-trunc-code-left-1-code-left-2-decomposition-pushout-code-right-span-pushout
        ( m)
        ( x0)
        ( x0)
        ( y1)
        ( q01)
        ( refl))
      ( unit-trunc
        ( inl-pushout
          ( map-code-left-0-code-left-1-span-pushout x0 x0 refl)
          ( map-code-left-0-code-left-2-decomposition-span-pushout
            x0 x0 y1 q01 refl)
          ( refl , refl))) ＝
    unit-trunc (q01 , refl)
  compute-equiv-decomposition-code-right-center-glue-span-pushout
    m x0 y1 q01 =
    equational-reasoning
      map-equiv
        ( equiv-trunc-code-left-1-code-left-2-decomposition-pushout-code-right-span-pushout
          ( m)
          ( x0)
          ( x0)
          ( y1)
          ( q01)
          ( refl))
        ( unit-trunc
          ( inl-pushout
            ( map-code-left-0-code-left-1-span-pushout x0 x0 refl)
            ( map-code-left-0-code-left-2-decomposition-span-pushout
              x0 x0 y1 q01 refl)
            ( refl , refl)))
      ＝
      map-equiv
        ( equiv-trunc-code-left-2c-code-right-span-pushout
          m x0 x0 y1 q01 refl)
        ( map-equiv
          ( equiv-trunc-code-left-2a1-code-left-2c-pushout-code-left-2c-span-pushout
            m x0 x0 y1 q01 refl)
          ( map-equiv
            ( equiv-trunc-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
              m x0 x0 y1 q01 refl)
            ( map-equiv
              ( equiv-trunc-code-left-1-code-left-2-decomposition-pushout-code-left-1-code-left-2b-code-left-2c-iterated-pushout-span-pushout
                m x0 x0 y1 q01 refl)
              ( unit-trunc
                ( inl-pushout
                  ( map-code-left-0-code-left-1-span-pushout x0 x0 refl)
                  ( map-code-left-0-code-left-2-decomposition-span-pushout
                    x0 x0 y1 q01 refl)
                  ( refl , refl))))))
        by refl
      ＝
      map-equiv
        ( equiv-trunc-code-left-2c-code-right-span-pushout
          m x0 x0 y1 q01 refl)
        ( map-equiv
          ( equiv-trunc-code-left-2a1-code-left-2c-pushout-code-left-2c-span-pushout
            m x0 x0 y1 q01 refl)
          ( map-equiv
            ( equiv-trunc-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
              m x0 x0 y1 q01 refl)
            ( unit-trunc
              ( inl-pushout
                ( inr-pushout
                  ( map-code-left-0-code-left-1-span-pushout x0 x0 refl)
                  ( map-code-left-0-code-left-2b-span-pushout x0 x0 refl) ∘
                  map-code-left-2a-code-left-2b-span-pushout
                    x0 x0 y1 q01 refl)
                ( map-code-left-2a-code-left-2c-span-pushout
                  x0 x0 y1 q01 refl)
                ( inl-pushout
                  ( map-code-left-0-code-left-1-span-pushout x0 x0 refl)
                  ( map-code-left-0-code-left-2b-span-pushout x0 x0 refl)
                  ( refl , refl))))))
        by
        ap
          ( λ t →
            map-equiv
              ( equiv-trunc-code-left-2c-code-right-span-pushout
                m x0 x0 y1 q01 refl)
              ( map-equiv
                ( equiv-trunc-code-left-2a1-code-left-2c-pushout-code-left-2c-span-pushout
                  m x0 x0 y1 q01 refl)
                ( map-equiv
                  ( equiv-trunc-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-span-pushout
                    m x0 x0 y1 q01 refl)
                  ( t))))
          ( compute-equiv-trunc-code-left-1-code-left-2-decomposition-pushout-code-left-1-code-left-2b-code-left-2c-iterated-pushout-inl-span-pushout
            m x0 x0 y1 q01 refl (refl , refl))
      ＝
      map-equiv
        ( equiv-trunc-code-left-2c-code-right-span-pushout
          m x0 x0 y1 q01 refl)
        ( map-equiv
          ( equiv-trunc-code-left-2a1-code-left-2c-pushout-code-left-2c-span-pushout
            m x0 x0 y1 q01 refl)
          ( unit-trunc
            ( inl-pushout
              ( map-code-left-2a-code-left-1-span-pushout
                x0 x0 y1 q01 refl)
              ( map-code-left-2a-code-left-2c-span-pushout
                x0 x0 y1 q01 refl)
              ( refl , refl))))
        by
        ap
          ( λ t →
            map-equiv
              ( equiv-trunc-code-left-2c-code-right-span-pushout
                m x0 x0 y1 q01 refl)
              ( map-equiv
                ( equiv-trunc-code-left-2a1-code-left-2c-pushout-code-left-2c-span-pushout
                  m x0 x0 y1 q01 refl)
                ( t)))
          ( compute-equiv-trunc-code-left-1-code-left-2b-code-left-2c-iterated-pushout-code-left-2a1-code-left-2c-pushout-inl-inl-span-pushout
            m x0 x0 y1 q01 refl (refl , refl))
      ＝
      map-equiv
        ( equiv-trunc-code-left-2c-code-right-span-pushout
          m x0 x0 y1 q01 refl)
        ( unit-trunc
          ( map-code-left-2a-code-left-2c-span-pushout
            ( x0)
            ( x0)
            ( y1)
            ( q01)
            ( refl)
            ( map-inv-code-left-2a-code-left-1-span-pushout
              x0 x0 y1 q01 refl (refl , refl))))
        by
        ap
          ( map-equiv
            ( equiv-trunc-code-left-2c-code-right-span-pushout
              m x0 x0 y1 q01 refl))
          ( compute-equiv-trunc-code-left-2a1-code-left-2c-pushout-code-left-2c-inl-span-pushout
            m x0 x0 y1 q01 refl (refl , refl))
      ＝
      unit-trunc
        ( map-equiv
          ( equiv-code-left-2c-fiber-glue-span-pushout x0 x0 y1 q01 refl)
          ( map-code-left-2a-code-left-2c-span-pushout
            ( x0)
            ( x0)
            ( y1)
            ( q01)
            ( refl)
            ( map-inv-code-left-2a-code-left-1-span-pushout
              x0 x0 y1 q01 refl (refl , refl))))
        by
        compute-equiv-trunc-code-left-2c-code-right-span-pushout
          ( m)
          ( x0)
          ( x0)
          ( y1)
          ( q01)
          ( refl)
          ( map-code-left-2a-code-left-2c-span-pushout
            ( x0)
            ( x0)
            ( y1)
            ( q01)
            ( refl)
            ( map-inv-code-left-2a-code-left-1-span-pushout
              x0 x0 y1 q01 refl (refl , refl)))
      ＝
      unit-trunc (q01 , refl)
        by
        ap
          ( unit-trunc)
          ( compute-equiv-code-left-2c-fiber-glue-center-span-pushout
            x0 y1 q01)

  compute-equiv-code-left-code-right-center-glue-span-pushout :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 : X) (y1 : Y) (q01 : Q x0 y1) →
    map-equiv
      ( equiv-code-left-code-right-span-pushout
        ( m)
        ( H)
        ( x0)
        ( x0)
        ( y1)
        ( q01)
        ( refl))
      ( center-code-left-span-pushout m x0) ＝
    unit-trunc (q01 , refl)
  compute-equiv-code-left-code-right-center-glue-span-pushout m H x0 y1 q01 =
    ap
      ( map-equiv
        ( equiv-trunc-code-left-1-code-left-2-decomposition-pushout-code-right-span-pushout
          m x0 x0 y1 q01 refl))
      ( compute-equiv-code-left-decomposition-center-glue-span-pushout
        m H x0 y1 q01) ∙
    compute-equiv-decomposition-code-right-center-glue-span-pushout
      m x0 y1 q01

  compute-tr-pointwise-dependent-identification-code-glue-center-span-pushout :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 : X) (y1 : Y) (q01 : Q x0 y1) →
    tr
      ( λ (C : UU (l1 ⊔ l2 ⊔ l3)) → C)
      ( pointwise-dependent-identification-code-glue-span-pushout
        m H x0 x0 y1 q01 refl)
      ( center-code-left-span-pushout m x0) ＝
    tr
      ( code-right-span-pushout m x0 y1)
      ( inv
        ( tr-Id-right
          ( glue-span-pushout Q x0 y1 q01)
          ( refl)))
      ( map-equiv
        ( equiv-code-left-code-right-span-pushout
          ( m)
          ( H)
          ( x0)
          ( x0)
          ( y1)
          ( q01)
          ( refl))
        ( center-code-left-span-pushout m x0))
  compute-tr-pointwise-dependent-identification-code-glue-center-span-pushout
    m H x0 y1 q01 =
    compute-tr-eq-equiv
      ( equiv-tr
        ( code-right-span-pushout m x0 y1)
        ( inv
          ( tr-Id-right
            ( glue-span-pushout Q x0 y1 q01)
            ( refl))) ∘e
        equiv-code-left-code-right-span-pushout
          ( m)
          ( H)
          ( x0)
          ( x0)
          ( y1)
          ( q01)
          ( refl))
      ( center-code-left-span-pushout m x0)

  compute-tr-tr-pointwise-dependent-identification-code-glue-center-span-pushout :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 : X) (y1 : Y) (q01 : Q x0 y1) →
    tr
      ( code-right-span-pushout m x0 y1)
      ( tr-Id-right
        ( glue-span-pushout Q x0 y1 q01)
        ( refl))
      ( tr
        ( λ (C : UU (l1 ⊔ l2 ⊔ l3)) → C)
        ( pointwise-dependent-identification-code-glue-span-pushout
          m H x0 x0 y1 q01 refl)
        ( center-code-left-span-pushout m x0)) ＝
    map-equiv
      ( equiv-code-left-code-right-span-pushout
        ( m)
        ( H)
        ( x0)
        ( x0)
        ( y1)
        ( q01)
        ( refl))
      ( center-code-left-span-pushout m x0)
  compute-tr-tr-pointwise-dependent-identification-code-glue-center-span-pushout
    m H x0 y1 q01 =
    ap
      ( tr
        ( code-right-span-pushout m x0 y1)
        ( tr-Id-right
          ( glue-span-pushout Q x0 y1 q01)
          ( refl)))
      ( compute-tr-pointwise-dependent-identification-code-glue-center-span-pushout
        m H x0 y1 q01) ∙
    inv
      ( tr-concat
        ( inv
          ( tr-Id-right
            ( glue-span-pushout Q x0 y1 q01)
            ( refl)))
        ( tr-Id-right
          ( glue-span-pushout Q x0 y1 q01)
          ( refl))
        ( map-equiv
          ( equiv-code-left-code-right-span-pushout
            ( m)
            ( H)
            ( x0)
            ( x0)
            ( y1)
            ( q01)
            ( refl))
          ( center-code-left-span-pushout m x0))) ∙
    ap
      ( λ p →
        tr
          ( code-right-span-pushout m x0 y1)
          ( p)
          ( map-equiv
            ( equiv-code-left-code-right-span-pushout
              ( m)
              ( H)
              ( x0)
              ( x0)
              ( y1)
              ( q01)
              ( refl))
            ( center-code-left-span-pushout m x0)))
      ( left-inv
        ( tr-Id-right
          ( glue-span-pushout Q x0 y1 q01)
          ( refl)))

  pointwise-compute-glue-code-span-pushout :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 : X) (y1 : Y) (q01 : Q x0 y1) →
    map-inv-equiv
      ( compute-dependent-identification-function-type-fixed-codomain
        ( λ p → inl-span-pushout Q x0 ＝ p)
        ( UU (l1 ⊔ l2 ⊔ l3))
        ( glue-span-pushout Q x0 y1 q01)
        ( code-span-pushout m H x0 (inl-span-pushout Q x0))
        ( code-right-span-pushout m x0 y1))
      ( apd
        ( code-span-pushout m H x0)
        ( glue-span-pushout Q x0 y1 q01) ∙
        compute-inr-code-span-pushout m H x0 y1)
      ( refl) ＝
    map-inv-equiv
      ( compute-dependent-identification-function-type-fixed-codomain
        ( λ p → inl-span-pushout Q x0 ＝ p)
        ( UU (l1 ⊔ l2 ⊔ l3))
        ( glue-span-pushout Q x0 y1 q01)
        ( code-span-pushout m H x0 (inl-span-pushout Q x0))
        ( code-right-span-pushout m x0 y1))
      ( ap
        ( tr
          ( code-motive-span-pushout x0)
          ( glue-span-pushout Q x0 y1 q01))
        ( compute-inl-code-span-pushout m H x0 x0) ∙
        dependent-identification-code-glue-span-pushout m H x0 x0 y1 q01)
      ( refl)
  pointwise-compute-glue-code-span-pushout m H x0 y1 q01 =
    ap
      ( λ e →
        map-inv-equiv
          ( compute-dependent-identification-function-type-fixed-codomain
            ( λ p → inl-span-pushout Q x0 ＝ p)
            ( UU (l1 ⊔ l2 ⊔ l3))
            ( glue-span-pushout Q x0 y1 q01)
            ( code-span-pushout m H x0 (inl-span-pushout Q x0))
            ( code-right-span-pushout m x0 y1))
          ( e)
          ( refl))
      ( compute-glue-code-span-pushout m H x0 x0 y1 q01)

  compute-tr-left-pointwise-compute-glue-code-span-pushout :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 : X) (y1 : Y) (q01 : Q x0 y1) →
    tr
      ( λ C → C (glue-span-pushout Q x0 y1 q01))
      ( compute-inr-code-span-pushout m H x0 y1)
      ( tr
        ( λ z → code-span-pushout m H x0 (pr1 z) (pr2 z))
        ( eq-based-path-span-pushout
          x0
          ( inr-span-pushout Q y1)
          ( glue-span-pushout Q x0 y1 q01))
        ( center-code-span-pushout-base m H x0)) ＝
    tr
      ( code-right-span-pushout m x0 y1)
      ( tr-Id-right
        ( glue-span-pushout Q x0 y1 q01)
        ( refl))
      ( tr
        ( λ (C : UU (l1 ⊔ l2 ⊔ l3)) → C)
        ( map-inv-equiv
          ( compute-dependent-identification-function-type-fixed-codomain
            ( λ p → inl-span-pushout Q x0 ＝ p)
            ( UU (l1 ⊔ l2 ⊔ l3))
            ( glue-span-pushout Q x0 y1 q01)
            ( code-span-pushout m H x0 (inl-span-pushout Q x0))
            ( code-right-span-pushout m x0 y1))
          ( apd
            ( code-span-pushout m H x0)
            ( glue-span-pushout Q x0 y1 q01) ∙
            compute-inr-code-span-pushout m H x0 y1)
          ( refl))
        ( center-code-span-pushout-base m H x0))
  compute-tr-left-pointwise-compute-glue-code-span-pushout m H x0 y1 q01 =
    compute-tr-eq-pair-Σ-map-inv-compute-dependent-identification-function-type-fixed-codomain-concat
      ( λ p → inl-span-pushout Q x0 ＝ p)
      ( code-span-pushout m H x0)
      ( glue-span-pushout Q x0 y1 q01)
      ( tr-Id-right
        ( glue-span-pushout Q x0 y1 q01)
        ( refl))
      ( code-right-span-pushout m x0 y1)
      ( compute-inr-code-span-pushout m H x0 y1)
      ( center-code-span-pushout-base m H x0)

  compute-tr-right-pointwise-compute-glue-code-span-pushout :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 : X) (y1 : Y) (q01 : Q x0 y1) →
    tr
      ( λ (C : UU (l1 ⊔ l2 ⊔ l3)) → C)
      ( map-inv-equiv
        ( compute-dependent-identification-function-type-fixed-codomain
          ( λ p → inl-span-pushout Q x0 ＝ p)
          ( UU (l1 ⊔ l2 ⊔ l3))
          ( glue-span-pushout Q x0 y1 q01)
          ( code-span-pushout m H x0 (inl-span-pushout Q x0))
          ( code-right-span-pushout m x0 y1))
        ( ap
          ( tr
            ( code-motive-span-pushout x0)
            ( glue-span-pushout Q x0 y1 q01))
          ( compute-inl-code-span-pushout m H x0 x0) ∙
          dependent-identification-code-glue-span-pushout m H x0 x0 y1 q01)
        ( refl))
      ( center-code-span-pushout-base m H x0) ＝
    tr
      ( λ (C : UU (l1 ⊔ l2 ⊔ l3)) → C)
      ( pointwise-dependent-identification-code-glue-span-pushout
        m H x0 x0 y1 q01 refl)
      ( center-code-left-span-pushout m x0)
  compute-tr-right-pointwise-compute-glue-code-span-pushout m H x0 y1 q01 =
    compute-tr-map-inv-compute-dependent-identification-function-type-fixed-codomain-ap
      ( λ p → inl-span-pushout Q x0 ＝ p)
      ( glue-span-pushout Q x0 y1 q01)
      ( code-span-pushout m H x0 (inl-span-pushout Q x0))
      ( code-left-span-pushout m x0 x0)
      ( code-right-span-pushout m x0 y1)
      ( compute-inl-code-span-pushout m H x0 x0)
      ( pointwise-dependent-identification-code-glue-span-pushout
        m H x0 x0 y1 q01)
      ( refl)
      ( center-code-left-span-pushout m x0)

  compute-tr-center-code-span-pushout-pointwise-glue-span-pushout :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 : X) (y1 : Y) (q01 : Q x0 y1) →
    tr
      ( λ C → C (glue-span-pushout Q x0 y1 q01))
      ( compute-inr-code-span-pushout m H x0 y1)
      ( tr
        ( λ z → code-span-pushout m H x0 (pr1 z) (pr2 z))
        ( eq-based-path-span-pushout
          x0
          ( inr-span-pushout Q y1)
          ( glue-span-pushout Q x0 y1 q01))
        ( center-code-span-pushout-base m H x0)) ＝
    tr
      ( code-right-span-pushout m x0 y1)
      ( tr-Id-right
        ( glue-span-pushout Q x0 y1 q01)
        ( refl))
      ( tr
        ( λ (C : UU (l1 ⊔ l2 ⊔ l3)) → C)
        ( pointwise-dependent-identification-code-glue-span-pushout
          m H x0 x0 y1 q01 refl)
        ( center-code-left-span-pushout m x0))
  compute-tr-center-code-span-pushout-pointwise-glue-span-pushout
    m H x0 y1 q01 =
    compute-tr-left-pointwise-compute-glue-code-span-pushout m H x0 y1 q01 ∙
    ap
      ( λ e →
        tr
          ( code-right-span-pushout m x0 y1)
          ( tr-Id-right
            ( glue-span-pushout Q x0 y1 q01)
            ( refl))
          ( tr
            ( λ (C : UU (l1 ⊔ l2 ⊔ l3)) → C)
            ( e)
            ( center-code-span-pushout-base m H x0)))
      ( pointwise-compute-glue-code-span-pushout m H x0 y1 q01) ∙
    ap
      ( tr
        ( code-right-span-pushout m x0 y1)
        ( tr-Id-right
          ( glue-span-pushout Q x0 y1 q01)
          ( refl)))
      ( compute-tr-right-pointwise-compute-glue-code-span-pushout
        m H x0 y1 q01)

  compute-tr-center-code-span-pushout-glue-span-pushout :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 : X) (y1 : Y) (q01 : Q x0 y1) →
    tr
      ( λ C → C (glue-span-pushout Q x0 y1 q01))
      ( compute-inr-code-span-pushout m H x0 y1)
      ( tr
        ( λ z → code-span-pushout m H x0 (pr1 z) (pr2 z))
        ( eq-based-path-span-pushout
          x0
          ( inr-span-pushout Q y1)
          ( glue-span-pushout Q x0 y1 q01))
        ( center-code-span-pushout-base m H x0)) ＝
    map-equiv
      ( equiv-code-left-code-right-span-pushout
        ( m)
        ( H)
        ( x0)
        ( x0)
        ( y1)
        ( q01)
        ( refl))
      ( center-code-left-span-pushout m x0)
  compute-tr-center-code-span-pushout-glue-span-pushout m H x0 y1 q01 =
    compute-tr-center-code-span-pushout-pointwise-glue-span-pushout
      m H x0 y1 q01 ∙
    compute-tr-tr-pointwise-dependent-identification-code-glue-center-span-pushout
      m H x0 y1 q01

  compute-center-code-right-glue-span-pushout :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 : X) (y1 : Y) (q01 : Q x0 y1) →
    center-code-right-span-pushout
      ( m)
      ( H)
      ( x0)
      ( y1)
      ( glue-span-pushout Q x0 y1 q01) ＝
    unit-trunc (q01 , refl)
  compute-center-code-right-glue-span-pushout m H x0 y1 q01 =
    ap
      ( tr
        ( λ C → C (glue-span-pushout Q x0 y1 q01))
        ( compute-inr-code-span-pushout m H x0 y1))
      ( compute-center-code-span-pushout-total
        ( m)
        ( H)
        ( x0)
        ( inr-span-pushout Q y1)
        ( glue-span-pushout Q x0 y1 q01)) ∙
    compute-tr-center-code-span-pushout-glue-span-pushout
      ( m)
      ( H)
      ( x0)
      ( y1)
      ( q01) ∙
    compute-equiv-code-left-code-right-center-glue-span-pushout
      ( m)
      ( H)
      ( x0)
      ( y1)
      ( q01)

  contraction-code-right-span-pushout :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 : X) (y1 : Y)
    (r : inl-span-pushout Q x0 ＝ inr-span-pushout Q y1)
    (c : code-right-span-pushout m x0 y1 r) →
    center-code-right-span-pushout m H x0 y1 r ＝ c
  contraction-code-right-span-pushout m H x0 y1 r =
    function-dependent-universal-property-trunc
      ( λ c →
        Id-Truncated-Type'
          ( trunc m (fiber (glue-span-pushout Q x0 y1) r))
          ( center-code-right-span-pushout m H x0 y1 r)
          ( c))
      ( λ { (q01 , refl) →
        compute-center-code-right-glue-span-pushout m H x0 y1 q01})

  is-contr-code-right-span-pushout-Blakers-Massey :
    (m : 𝕋) (H : connected-join-hypothesis-span-pushout m)
    (x0 : X) (y1 : Y)
    (r : inl-span-pushout Q x0 ＝ inr-span-pushout Q y1) →
    is-contr (code-right-span-pushout m x0 y1 r)
  pr1 (is-contr-code-right-span-pushout-Blakers-Massey m H x0 y1 r) =
    center-code-right-span-pushout m H x0 y1 r
  pr2 (is-contr-code-right-span-pushout-Blakers-Massey m H x0 y1 r) =
    contraction-code-right-span-pushout m H x0 y1 r

  is-connected-map-glue-span-pushout-Blakers-Massey :
    (m : 𝕋) →
    connected-join-hypothesis-span-pushout m →
    (x : X) (y : Y) → is-connected-map m (glue-span-pushout Q x y)
  is-connected-map-glue-span-pushout-Blakers-Massey m H =
    is-connected-map-glue-span-pushout-is-contr-code-right-span-pushout
      ( m)
      ( is-contr-code-right-span-pushout-Blakers-Massey m H)

  is-connected-map-gap-span-pushout-connected-join-hypothesis-Blakers-Massey :
    (m : 𝕋) →
    connected-join-hypothesis-span-pushout m →
    is-connected-map m (gap-span-pushout Q)
  is-connected-map-gap-span-pushout-connected-join-hypothesis-Blakers-Massey
    m H =
    is-connected-map-gap-span-pushout-is-connected-map-glue-span-pushout
      ( Q)
      ( m)
      ( is-connected-map-glue-span-pushout-Blakers-Massey m H)

  is-connected-map-gap-span-pushout-Blakers-Massey :
    (k n : 𝕋) →
    connected-join-hypothesis-span-pushout (add+2-𝕋 n k) →
    is-connected-map (add+2-𝕋 n k) (gap-span-pushout Q)
  is-connected-map-gap-span-pushout-Blakers-Massey k n =
    is-connected-map-gap-span-pushout-connected-join-hypothesis-Blakers-Massey
      ( add+2-𝕋 n k)
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

  is-connected-map-glue-relation-map-span-pushout-Blakers-Massey :
    (k n : 𝕋) →
    is-connected-map (succ-𝕋 k) f →
    is-connected-map (succ-𝕋 n) g →
    (a : A) (b : B) →
    is-connected-map
      ( add+2-𝕋 n k)
      ( glue-span-pushout (relation-map-span-pushout f g) a b)
  is-connected-map-glue-relation-map-span-pushout-Blakers-Massey
    k n H K =
    is-connected-map-glue-span-pushout-Blakers-Massey
      ( relation-map-span-pushout f g)
      ( add+2-𝕋 n k)
      ( is-connected-join-paths-relation-map-span-pushout-is-connected-maps
        k n H K)

  is-connected-map-gap-relation-map-span-pushout-Blakers-Massey :
    (k n : 𝕋) →
    is-connected-map (succ-𝕋 k) f →
    is-connected-map (succ-𝕋 n) g →
    is-connected-map
      ( add+2-𝕋 n k)
      ( gap-span-pushout (relation-map-span-pushout f g))
  is-connected-map-gap-relation-map-span-pushout-Blakers-Massey
    k n H K =
    is-connected-map-gap-span-pushout-Blakers-Massey
      ( relation-map-span-pushout f g)
      ( k)
      ( n)
      ( is-connected-join-paths-relation-map-span-pushout-is-connected-maps
        k n H K)
```
