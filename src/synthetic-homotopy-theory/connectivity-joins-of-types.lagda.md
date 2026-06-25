# Connectivity of joins of types

```agda
module synthetic-homotopy-theory.connectivity-joins-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.fibers-of-maps
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterated-successors-truncation-levels
open import foundation.precomposition-dependent-functions
open import foundation.type-arithmetic-dependent-function-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.truncated-maps
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.function-types
open import foundation-core.truncated-maps

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
```

</details>

## Idea

The proof that joins preserve connectivity uses the join elimination principle
and the dependent universal property of connected maps. This file starts by
recording the reusable exponential form of connectedness needed in that proof:
if `A` is `k`-connected, then the constant-function map

```text
  X → (A → X)
```

is `n`-truncated for every `(k+n+2)`-truncated type `X`.

## Constant functions out of connected types

```agda
module _
  {l1 : Level} (k : 𝕋) {A : UU l1}
  where

  is-connected-map-terminal-map-is-connected :
    is-connected k A → is-connected-map k (terminal-map A)
  is-connected-map-terminal-map-is-connected H u =
    is-connected-equiv (equiv-fiber-terminal-map u) H

module _
  {l1 l2 : Level} (k n : 𝕋) {A : UU l1} {X : UU l2}
  where

  is-trunc-map-precomp-terminal-map-is-connected :
    is-connected k A →
    is-trunc (add+2-𝕋 k n) X →
    is-trunc-map n
      ( precomp-Π (terminal-map A) (λ _ → X))
  is-trunc-map-precomp-terminal-map-is-connected H is-trunc-X =
    is-trunc-map-precomp-Π-is-connected-map k n
      ( is-connected-map-terminal-map-is-connected k H)
      ( λ _ → X , is-trunc-X)

  is-trunc-map-diagonal-exponential-is-connected :
    is-connected k A →
    is-trunc (add+2-𝕋 k n) X →
    is-trunc-map n (diagonal-exponential X A)
  is-trunc-map-diagonal-exponential-is-connected H is-trunc-X =
    is-trunc-map-left-map-triangle n
      ( diagonal-exponential X A)
      ( precomp-Π (terminal-map A) (λ _ → X))
      ( const unit)
      ( refl-htpy)
      ( is-trunc-map-precomp-terminal-map-is-connected H is-trunc-X)
      ( is-trunc-map-is-equiv n (is-equiv-const-unit X))
```

## Cocones into a type as fiberwise constant maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  family-fiber-diagonal-exponential-cocone-join :
    (A → X) → UU (l1 ⊔ l2 ⊔ l3)
  family-fiber-diagonal-exponential-cocone-join i =
    (b : B) → fiber (diagonal-exponential X A) i

  equiv-family-fiber-diagonal-exponential-cocone-join :
    cocone {S = A × B} {A = A} {B = B} pr1 pr2 X ≃
    Σ (A → X) family-fiber-diagonal-exponential-cocone-join
  equiv-family-fiber-diagonal-exponential-cocone-join =
    equivalence-reasoning
      cocone {S = A × B} {A = A} {B = B} pr1 pr2 X
      ≃ Σ ( A → X)
          ( λ i →
            Σ ( B → X)
              ( λ j → (t : A × B) → i (pr1 t) ＝ j (pr2 t)))
        by id-equiv
      ≃ Σ ( A → X)
          ( λ i →
            Σ ( B → X)
              ( λ j → (a : A) (b : B) → i a ＝ j b))
        by equiv-tot (λ i → equiv-tot (λ j → equiv-ev-pair))
      ≃ Σ ( A → X)
          ( λ i →
            Σ ( B → X)
              ( λ j → (b : B) (a : A) → i a ＝ j b))
        by equiv-tot (λ i → equiv-tot (λ j → equiv-swap-Π))
      ≃ Σ ( A → X)
          ( λ i → (b : B) → Σ X (λ x → (a : A) → i a ＝ x))
        by equiv-tot (λ i → inv-distributive-Π-Σ)
      ≃ Σ (A → X) family-fiber-diagonal-exponential-cocone-join
        by
          equiv-tot
            ( λ i →
              equiv-Π-equiv-family
                ( λ b →
                  equiv-tot
                    ( λ x →
                      ( inv-equiv equiv-funext) ∘e
                      ( equiv-Π-equiv-family (λ a → equiv-inv (i a) x)))))

  equiv-cocone-diagonal-exponential-join-is-connected :
    (k n : 𝕋) →
    is-connected k A →
    is-connected n B →
    is-trunc (add+2-𝕋 k n) X →
    X ≃ cocone {S = A × B} {A = A} {B = B} pr1 pr2 X
  equiv-cocone-diagonal-exponential-join-is-connected k n H K is-trunc-X =
    ( inv-equiv equiv-family-fiber-diagonal-exponential-cocone-join) ∘e
    ( equiv-tot
      ( λ i →
        ( diagonal-exponential
          ( fiber (diagonal-exponential X A) i)
          ( B)) ,
        ( is-equiv-diagonal-exponential-is-connected
          ( ( fiber (diagonal-exponential X A) i) ,
            ( is-trunc-map-diagonal-exponential-is-connected k n H is-trunc-X
              ( i)))
          ( K)))) ∘e
    ( inv-equiv-total-fiber (diagonal-exponential X A))

  constant-cocone-join :
    X → cocone {S = A × B} {A = A} {B = B} pr1 pr2 X
  pr1 (constant-cocone-join x) = const A x
  pr1 (pr2 (constant-cocone-join x)) = const B x
  pr2 (pr2 (constant-cocone-join x)) t = refl

  is-equiv-constant-cocone-join-is-connected :
    (k n : 𝕋) →
    (H : is-connected k A) →
    (K : is-connected n B) →
    (is-trunc-X : is-trunc (add+2-𝕋 k n) X) →
    is-equiv constant-cocone-join
  is-equiv-constant-cocone-join-is-connected k n H K is-trunc-X =
    is-equiv-right-factor
      ( map-equiv equiv-family-fiber-diagonal-exponential-cocone-join)
      ( constant-cocone-join)
      ( is-equiv-map-equiv equiv-family-fiber-diagonal-exponential-cocone-join)
      ( is-equiv-htpy-equiv'
        ( ( equiv-tot
            ( λ i →
              ( diagonal-exponential
                ( fiber (diagonal-exponential X A) i)
                ( B)) ,
              ( is-equiv-diagonal-exponential-is-connected
                ( ( fiber (diagonal-exponential X A) i) ,
                  ( is-trunc-map-diagonal-exponential-is-connected
                    ( k)
                    ( n)
                    ( H)
                    ( is-trunc-X)
                    ( i)))
                ( K)))) ∘e
          ( inv-equiv-total-fiber (diagonal-exponential X A)))
        ( λ x →
          eq-pair-eq-fiber
            ( eq-htpy
              ( λ b →
                eq-pair-eq-fiber
                  ( inv (eq-htpy-refl-htpy (const A x)))))))

  htpy-constant-cocone-join-cocone-map-diagonal-exponential :
    constant-cocone-join ~
    ( cocone-map pr1 pr2 cocone-join ∘ diagonal-exponential X (A * B))
  htpy-constant-cocone-join-cocone-map-diagonal-exponential x =
    eq-htpy-cocone pr1 pr2
      ( constant-cocone-join x)
      ( cocone-map pr1 pr2 cocone-join
        ( diagonal-exponential X (A * B) x))
      ( refl-htpy , refl-htpy , λ t → inv-ap-const x (glue-join t))

  is-equiv-cocone-map-diagonal-exponential-join-is-connected :
    (k n : 𝕋) →
    (H : is-connected k A) →
    (K : is-connected n B) →
    (is-trunc-X : is-trunc (add+2-𝕋 k n) X) →
    is-equiv
      ( cocone-map pr1 pr2 cocone-join ∘ diagonal-exponential X (A * B))
  is-equiv-cocone-map-diagonal-exponential-join-is-connected k n H K
    is-trunc-X =
    is-equiv-htpy'
      ( constant-cocone-join)
      ( htpy-constant-cocone-join-cocone-map-diagonal-exponential)
      ( is-equiv-constant-cocone-join-is-connected k n H K is-trunc-X)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-connected-join-is-connected :
    (k n : 𝕋) →
    is-connected k A →
    is-connected n B →
    is-connected (add+2-𝕋 k n) (A * B)
  is-connected-join-is-connected k n H K =
    is-connected-is-equiv-diagonal-exponential
      ( λ T →
        is-equiv-right-factor
          ( cocone-map pr1 pr2 cocone-join)
          ( diagonal-exponential (type-Truncated-Type T) (A * B))
          ( is-equiv-map-equiv (equiv-up-join (type-Truncated-Type T)))
          ( is-equiv-cocone-map-diagonal-exponential-join-is-connected
            ( k)
            ( n)
            ( H)
            ( K)
            ( is-trunc-type-Truncated-Type T)))
```
