# Spheres as join powers of the two-point type

```agda
module synthetic-homotopy-theory.spheres-as-join-powers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.empty-types
open import foundation.equivalences
open import foundation.universe-levels

open import synthetic-homotopy-theory.functoriality-suspensions
open import synthetic-homotopy-theory.join-powers-of-types
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.spheres
open import synthetic-homotopy-theory.suspensions-as-joins

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The spheres are iterated suspensions of `Fin 2`. Since suspension is equivalent
to joining on the left with `Fin 2`, each sphere is equivalent to the
corresponding nonzero join power of `Fin 2`.

## Theorem

```agda
equiv-sphere-join-power-Fin-2 :
  (n : ℕ) → join-power (succ-ℕ n) (Fin 2) ≃ sphere n
equiv-sphere-join-power-Fin-2 zero-ℕ =
  inv-equiv (right-unit-law-join-is-empty is-empty-raise-empty)
equiv-sphere-join-power-Fin-2 (succ-ℕ n) =
  ( equiv-suspension (equiv-sphere-join-power-Fin-2 n)) ∘e
  ( equiv-suspension-join-Fin-2 (join-power (succ-ℕ n) (Fin 2)))

equiv-sphere-1-join-power-Fin-2 : join-power 2 (Fin 2) ≃ sphere 1
equiv-sphere-1-join-power-Fin-2 =
  equiv-sphere-join-power-Fin-2 1

equiv-sphere-3-join-power-Fin-2 : join-power 4 (Fin 2) ≃ sphere 3
equiv-sphere-3-join-power-Fin-2 =
  equiv-sphere-join-power-Fin-2 3
```
