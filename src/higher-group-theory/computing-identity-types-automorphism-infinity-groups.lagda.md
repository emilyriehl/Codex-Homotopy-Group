# Computing identity types of automorphism infinity groups

```agda
module higher-group-theory.computing-identity-types-automorphism-infinity-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import higher-group-theory.automorphism-groups

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

The inverse direction of extensionality for classifying types of automorphism
infinity groups constructs a path from an equality of first components. Applying
the extensionality map to that constructed path recovers the original equality.

## Theorem

```agda
module _
  {l : Level} {A : UU l} (a : A)
  where

  compute-Eq-eq-eq-Eq-classifying-type-Automorphism-∞-Group :
    (X Y : classifying-type-Automorphism-∞-Group a) →
    (p : Eq-classifying-type-Automorphism-∞-Group a X Y) →
    Eq-eq-classifying-type-Automorphism-∞-Group
      ( a)
      ( X)
      ( Y)
      ( eq-Eq-classifying-type-Automorphism-∞-Group a X Y p) ＝
    p
  compute-Eq-eq-eq-Eq-classifying-type-Automorphism-∞-Group X Y p =
    is-section-map-inv-equiv
      ( extensionality-classifying-type-Automorphism-∞-Group a X Y)
      ( p)

  preserves-concat-Eq-eq-classifying-type-Automorphism-∞-Group :
    {X Y Z : classifying-type-Automorphism-∞-Group a}
    (p : X ＝ Y) (q : Y ＝ Z) →
    Eq-eq-classifying-type-Automorphism-∞-Group a X Z (p ∙ q) ＝
    ( Eq-eq-classifying-type-Automorphism-∞-Group a X Y p) ∙
    ( Eq-eq-classifying-type-Automorphism-∞-Group a Y Z q)
  preserves-concat-Eq-eq-classifying-type-Automorphism-∞-Group refl refl =
    refl

  preserves-inv-Eq-eq-classifying-type-Automorphism-∞-Group :
    {X Y : classifying-type-Automorphism-∞-Group a} (p : X ＝ Y) →
    Eq-eq-classifying-type-Automorphism-∞-Group a Y X (inv p) ＝
    inv (Eq-eq-classifying-type-Automorphism-∞-Group a X Y p)
  preserves-inv-Eq-eq-classifying-type-Automorphism-∞-Group refl =
    refl

  compute-Eq-eq-tr-type-Ω-classifying-type-Automorphism-∞-Group :
    {X Y : classifying-type-Automorphism-∞-Group a}
    (p : X ＝ Y) (q : X ＝ X) →
    Eq-eq-classifying-type-Automorphism-∞-Group a Y Y
      ( tr-type-Ω p q) ＝
    tr-type-Ω
      ( Eq-eq-classifying-type-Automorphism-∞-Group a X Y p)
      ( Eq-eq-classifying-type-Automorphism-∞-Group a X X q)
  compute-Eq-eq-tr-type-Ω-classifying-type-Automorphism-∞-Group refl q =
    refl
```
