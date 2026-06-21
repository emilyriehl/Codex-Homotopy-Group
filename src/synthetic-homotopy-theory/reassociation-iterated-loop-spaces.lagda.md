# Reassociation of iterated loop spaces

```agda
module synthetic-homotopy-theory.reassociation-iterated-loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.iterating-functions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

The public homotopy-group interface writes successor iterated loop spaces as
`Ω^(n+1) X`, while the direct shifted connecting fiber sequence naturally
iterates a looped space, giving `Ω^n(Ω X)`. These pointed types are equal by
the reassociation law for iterating endofunctions.

## Properties

```agda
module _
  {l : Level}
  where

  reassociate-succ-iterated-loop-space :
    (n : ℕ) (A : Pointed-Type l) →
    iterated-loop-space (succ-ℕ n) A ＝
    iterated-loop-space n (Ω A)
  reassociate-succ-iterated-loop-space n A =
    reassociate-iterate-succ-ℕ n Ω A

  inv-reassociate-succ-iterated-loop-space :
    (n : ℕ) (A : Pointed-Type l) →
    iterated-loop-space n (Ω A) ＝
    iterated-loop-space (succ-ℕ n) A
  inv-reassociate-succ-iterated-loop-space n A =
    inv (reassociate-succ-iterated-loop-space n A)

  reassociate-Ω-succ-iterated-loop-space :
    (n : ℕ) (A : Pointed-Type l) →
    Ω (iterated-loop-space (succ-ℕ n) A) ＝
    Ω (iterated-loop-space n (Ω A))
  reassociate-Ω-succ-iterated-loop-space n A =
    ap Ω (reassociate-succ-iterated-loop-space n A)

  inv-reassociate-Ω-succ-iterated-loop-space :
    (n : ℕ) (A : Pointed-Type l) →
    Ω (iterated-loop-space n (Ω A)) ＝
    Ω (iterated-loop-space (succ-ℕ n) A)
  inv-reassociate-Ω-succ-iterated-loop-space n A =
    inv (reassociate-Ω-succ-iterated-loop-space n A)
```

### Transport of loop-space functoriality

```agda
module _
  {l1 l2 : Level}
  {A A' : Pointed-Type l1} {B B' : Pointed-Type l2}
  where

  tr-pointed-map-Ω :
    (p : A ＝ A') (q : B ＝ B') (f : A →∗ B) →
    tr
      (λ X → X →∗ Ω B')
      (ap Ω p)
      ( tr
        (λ Y → Ω A →∗ Y)
        (ap Ω q)
        (pointed-map-Ω f)) ＝
    pointed-map-Ω
      ( tr
        (λ X → X →∗ B')
        (p)
        ( tr
          (λ Y → A →∗ Y)
          (q)
          (f)))
  tr-pointed-map-Ω refl refl f = refl
```

### Reassociation of induced maps on iterated loop spaces

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  reassociate-pointed-map-iterated-loop-space :
    (n : ℕ) (f : A →∗ B) →
    tr
      (λ X → X →∗ iterated-loop-space n (Ω B))
      (reassociate-succ-iterated-loop-space n A)
      ( tr
        (λ Y → iterated-loop-space (succ-ℕ n) A →∗ Y)
        (reassociate-succ-iterated-loop-space n B)
        (pointed-map-iterated-loop-space (succ-ℕ n) f)) ＝
    pointed-map-iterated-loop-space n (pointed-map-Ω f)
  reassociate-pointed-map-iterated-loop-space zero-ℕ f = refl
  reassociate-pointed-map-iterated-loop-space (succ-ℕ n) f =
    tr-pointed-map-Ω
      (reassociate-succ-iterated-loop-space n A)
      (reassociate-succ-iterated-loop-space n B)
      (pointed-map-iterated-loop-space (succ-ℕ n) f) ∙
    ap pointed-map-Ω
      (reassociate-pointed-map-iterated-loop-space n f)

  reassociate-Ω-pointed-map-iterated-loop-space :
    (n : ℕ) (f : A →∗ B) →
    tr
      (λ X → X →∗ Ω (iterated-loop-space n (Ω B)))
      (reassociate-Ω-succ-iterated-loop-space n A)
      ( tr
        (λ Y → Ω (iterated-loop-space (succ-ℕ n) A) →∗ Y)
        (reassociate-Ω-succ-iterated-loop-space n B)
        (pointed-map-Ω (pointed-map-iterated-loop-space (succ-ℕ n) f))) ＝
    pointed-map-Ω
      (pointed-map-iterated-loop-space n (pointed-map-Ω f))
  reassociate-Ω-pointed-map-iterated-loop-space n f =
    tr-pointed-map-Ω
      (reassociate-succ-iterated-loop-space n A)
      (reassociate-succ-iterated-loop-space n B)
      (pointed-map-iterated-loop-space (succ-ℕ n) f) ∙
    ap pointed-map-Ω
      (reassociate-pointed-map-iterated-loop-space n f)
```
