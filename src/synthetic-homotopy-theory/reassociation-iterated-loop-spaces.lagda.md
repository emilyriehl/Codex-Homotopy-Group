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
open import foundation.universe-levels

open import structured-types.pointed-types

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
