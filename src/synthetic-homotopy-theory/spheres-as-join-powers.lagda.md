# Spheres as join powers of the two-point type

```agda
module synthetic-homotopy-theory.spheres-as-join-powers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.injective-maps
open import foundation.identity-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.functoriality-joins-of-types
open import synthetic-homotopy-theory.functoriality-suspensions
open import synthetic-homotopy-theory.join-powers-of-types
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.spheres
open import synthetic-homotopy-theory.suspensions-as-joins
open import synthetic-homotopy-theory.type-arithmetic-joins-of-types

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

point-join-power-Fin-2 :
  (n : ℕ) → join-power (succ-ℕ n) (Fin 2)
point-join-power-Fin-2 n =
  inl-join (zero-Fin-2 (join-power n (Fin 2)))

compute-point-equiv-sphere-join-power-Fin-2 :
  (n : ℕ) →
  map-equiv (equiv-sphere-join-power-Fin-2 n)
    ( point-join-power-Fin-2 n) ＝
  north-sphere n
compute-point-equiv-sphere-join-power-Fin-2 zero-ℕ =
  is-retraction-map-inv-equiv
    ( right-unit-law-join-is-empty is-empty-raise-empty)
    ( zero-Fin-2 (raise-empty lzero))
compute-point-equiv-sphere-join-power-Fin-2 (succ-ℕ n) =
  ap
    ( map-suspension (map-equiv (equiv-sphere-join-power-Fin-2 n)))
    ( compute-inl-zero-map-suspension-join-Fin-2
      ( join-power (succ-ℕ n) (Fin 2))) ∙
  compute-north-map-suspension
    ( map-equiv (equiv-sphere-join-power-Fin-2 n))

compute-point-inv-equiv-sphere-1-join-power-Fin-2 :
  map-inv-equiv equiv-sphere-1-join-power-Fin-2 (north-sphere 1) ＝
  point-join-power-Fin-2 1
compute-point-inv-equiv-sphere-1-join-power-Fin-2 =
  is-injective-equiv equiv-sphere-1-join-power-Fin-2
    ( ( is-section-map-inv-equiv
        ( equiv-sphere-1-join-power-Fin-2)
        ( north-sphere 1)) ∙
      ( inv (compute-point-equiv-sphere-join-power-Fin-2 1)))

abstract
  compute-inr-inl-map-twist-tri-join :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
    (b : B) →
    map-twist-tri-join {A = A} {B = B} {C = C}
      ( inr-join (inl-join b)) ＝
    inl-join b
  compute-inr-inl-map-twist-tri-join {A = A} {B = B} {C = C} b =
    ap
      ( λ d → point-2-tri-join-rec-data d b)
      ( is-section-rec-tri-join
        ( twist-tri-join-rec-data
          ( canonical-swapped-tri-join-rec-data {A = A} {B = B} {C = C})))

  compute-inl-inl-equiv-associative-join-twist :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
    (a : A) →
    map-equiv (equiv-associative-join-twist {A = A} {B = B} {C = C})
      ( inl-join (inl-join a)) ＝
    inl-join a
  compute-inl-inl-equiv-associative-join-twist {A = A} {B = B} {C = C} a =
    ( ap
      ( map-equiv (equiv-join id-equiv (commutative-join {A = C} {B = B})) ∘
        map-twist-tri-join {A = C} {B = A} {C = B})
      ( compute-inl-map-commutative-join (inl-join a))) ∙
    ( ap
      ( map-equiv (equiv-join id-equiv (commutative-join {A = C} {B = B})))
      ( compute-inr-inl-map-twist-tri-join {A = C} {B = A} {C = B} a)) ∙
    compute-inl-map-join
      ( id)
      ( map-equiv (commutative-join {A = C} {B = B}))
      ( a)
```

### The join of two 1-spheres as a join of join powers

```agda
map-join-power-two-two :
  {l : Level} (A : UU l) →
  join-power 2 A * join-power 2 A → join-power 4 A
map-join-power-two-two A =
  ( map-join
    ( id)
    ( map-join
      ( id)
      ( map-inv-equiv (left-unit-law-join-is-empty is-empty-raise-empty)))) ∘
  ( map-join
    ( id)
    ( map-associative-join {A = A} {B = raise-empty _} {C = join-power 2 A})) ∘
  ( map-associative-join {A = A} {B = join-power 1 A} {C = join-power 2 A})

map-join-power-two-two-Fin-2 :
  join-power 2 (Fin 2) * join-power 2 (Fin 2) → join-power 4 (Fin 2)
map-join-power-two-two-Fin-2 =
  map-join-power-two-two (Fin 2)

is-equiv-map-join-power-two-two-is-equiv-map-associative-join :
  {l : Level} (A : UU l) →
  is-equiv
    ( map-associative-join
      {A = A}
      {B = join-power 1 A}
      {C = join-power 2 A}) →
  is-equiv
    ( map-associative-join
      {A = A}
      {B = raise-empty _}
      {C = join-power 2 A}) →
  is-equiv (map-join-power-two-two A)
is-equiv-map-join-power-two-two-is-equiv-map-associative-join A H1 H2 =
  is-equiv-comp
    ( map-join
      ( id)
      ( map-join
        ( id)
        ( map-inv-equiv (left-unit-law-join-is-empty is-empty-raise-empty))))
    ( ( map-join
        ( id)
        ( map-associative-join
          {A = A}
          {B = raise-empty _}
          {C = join-power 2 A})) ∘
      ( map-associative-join
        {A = A}
        {B = join-power 1 A}
        {C = join-power 2 A}))
    ( is-equiv-comp
      ( map-join
        ( id)
        ( map-associative-join
          {A = A}
          {B = raise-empty _}
          {C = join-power 2 A}))
      ( map-associative-join
        {A = A}
        {B = join-power 1 A}
        {C = join-power 2 A})
      ( H1)
      ( is-equiv-map-join
        ( id-equiv)
        ( map-associative-join
          {A = A}
          {B = raise-empty _}
          {C = join-power 2 A} ,
          H2)))
    ( is-equiv-map-join
      ( id-equiv)
      ( equiv-join
        ( id-equiv)
        ( inv-equiv (left-unit-law-join-is-empty is-empty-raise-empty))))

equiv-join-power-two-two :
  {l : Level} (A : UU l) →
  (join-power 2 A * join-power 2 A) ≃ join-power 4 A
equiv-join-power-two-two A =
  equiv-join
    ( id-equiv)
    ( equiv-join
      ( id-equiv)
      ( inv-equiv (left-unit-law-join-is-empty is-empty-raise-empty))) ∘e
  equiv-join
    ( id-equiv)
    ( equiv-associative-join-twist
      {A = A}
      {B = raise-empty _}
      {C = join-power 2 A}) ∘e
  equiv-associative-join-twist
    {A = A}
    {B = join-power 1 A}
    {C = join-power 2 A}

compute-point-map-join-power-two-two-Fin-2 :
  map-join-power-two-two-Fin-2
    ( inl-join (point-join-power-Fin-2 1)) ＝
  point-join-power-Fin-2 3
compute-point-map-join-power-two-two-Fin-2 =
  ( ap
    ( map-join
      ( id)
      ( map-join
        ( id)
        ( map-inv-equiv (left-unit-law-join-is-empty is-empty-raise-empty))) ∘
      map-join
        ( id)
        ( map-associative-join
          {A = Fin 2}
          {B = raise-empty lzero}
          {C = join-power 2 (Fin 2)}))
    ( compute-inl-map-associative-join (point-join-power-Fin-2 1) ∙
      compute-inl-map-left-associative-join
        ( zero-Fin-2 (join-power 1 (Fin 2))))) ∙
  ( ap
    ( map-join
      ( id)
      ( map-join
        ( id)
        ( map-inv-equiv (left-unit-law-join-is-empty is-empty-raise-empty))))
    ( compute-inl-map-join
      ( id)
      ( map-associative-join
        {A = Fin 2}
        {B = raise-empty lzero}
        {C = join-power 2 (Fin 2)})
      ( zero-Fin-2 (join-power 1 (Fin 2) * join-power 2 (Fin 2))))) ∙
  compute-inl-map-join
    ( id)
    ( map-join
      ( id)
      ( map-inv-equiv (left-unit-law-join-is-empty is-empty-raise-empty)))
    ( zero-Fin-2
      ( Fin 2 * (raise-empty lzero * join-power 2 (Fin 2))))

is-equiv-map-join-power-two-two-coherence-squares :
  {l : Level} (A : UU l) →
  coherence-square-triangle-map-inv-coherence-product-join
    {A = A}
    {B = join-power 1 A}
    {C = join-power 2 A} →
  coherence-square-triangle-map-associative-coherence-left-product-join
    {A = A}
    {B = join-power 1 A}
    {C = join-power 2 A} →
  coherence-square-triangle-map-inv-coherence-product-join
    {A = A}
    {B = raise-empty _}
    {C = join-power 2 A} →
  coherence-square-triangle-map-associative-coherence-left-product-join
    {A = A}
    {B = raise-empty _}
    {C = join-power 2 A} →
  is-equiv (map-join-power-two-two A)
is-equiv-map-join-power-two-two-coherence-squares
  A H1 K1 H2 K2 =
  is-equiv-map-join-power-two-two-is-equiv-map-associative-join
    ( A)
    ( is-equiv-map-associative-join-coherence-squares H1 K1)
    ( is-equiv-map-associative-join-coherence-squares H2 K2)

equiv-join-power-two-two-coherence-squares :
  {l : Level} (A : UU l) →
  coherence-square-triangle-map-inv-coherence-product-join
    {A = A}
    {B = join-power 1 A}
    {C = join-power 2 A} →
  coherence-square-triangle-map-associative-coherence-left-product-join
    {A = A}
    {B = join-power 1 A}
    {C = join-power 2 A} →
  coherence-square-triangle-map-inv-coherence-product-join
    {A = A}
    {B = raise-empty _}
    {C = join-power 2 A} →
  coherence-square-triangle-map-associative-coherence-left-product-join
    {A = A}
    {B = raise-empty _}
    {C = join-power 2 A} →
  (join-power 2 A * join-power 2 A) ≃ join-power 4 A
pr1 (equiv-join-power-two-two-coherence-squares A H1 K1 H2 K2) =
  map-join-power-two-two A
pr2 (equiv-join-power-two-two-coherence-squares A H1 K1 H2 K2) =
  is-equiv-map-join-power-two-two-coherence-squares A H1 K1 H2 K2

is-equiv-map-join-power-two-two-coherence-squares-first-associator :
  {l : Level} (A : UU l) →
  coherence-square-triangle-map-inv-coherence-product-join
    {A = A}
    {B = join-power 1 A}
    {C = join-power 2 A} →
  coherence-square-triangle-map-associative-coherence-left-product-join
    {A = A}
    {B = join-power 1 A}
    {C = join-power 2 A} →
  is-equiv (map-join-power-two-two A)
is-equiv-map-join-power-two-two-coherence-squares-first-associator A H K =
  is-equiv-map-join-power-two-two-coherence-squares
    ( A)
    ( H)
    ( K)
    ( λ a b c → ex-falso (is-empty-raise-empty b))
    ( λ a b c → ex-falso (is-empty-raise-empty b))

equiv-join-power-two-two-coherence-squares-first-associator :
  {l : Level} (A : UU l) →
  coherence-square-triangle-map-inv-coherence-product-join
    {A = A}
    {B = join-power 1 A}
    {C = join-power 2 A} →
  coherence-square-triangle-map-associative-coherence-left-product-join
    {A = A}
    {B = join-power 1 A}
    {C = join-power 2 A} →
  (join-power 2 A * join-power 2 A) ≃ join-power 4 A
pr1 (equiv-join-power-two-two-coherence-squares-first-associator A H K) =
  map-join-power-two-two A
pr2 (equiv-join-power-two-two-coherence-squares-first-associator A H K) =
  is-equiv-map-join-power-two-two-coherence-squares-first-associator A H K

equiv-first-join-power-two-two-Fin-2 :
  join-power 2 (Fin 2) * join-power 2 (Fin 2) ≃
  Fin 2 * (join-power 1 (Fin 2) * join-power 2 (Fin 2))
equiv-first-join-power-two-two-Fin-2 =
  equiv-associative-join-twist
    {A = Fin 2}
    {B = join-power 1 (Fin 2)}
    {C = join-power 2 (Fin 2)}

compute-point-first-equiv-join-power-two-two-Fin-2 :
  map-equiv
    ( equiv-first-join-power-two-two-Fin-2)
    ( inl-join (point-join-power-Fin-2 1)) ＝
  inl-join (zero-Fin-2 (join-power 1 (Fin 2) * join-power 2 (Fin 2)))
compute-point-first-equiv-join-power-two-two-Fin-2 =
  compute-inl-inl-equiv-associative-join-twist
    {A = Fin 2}
    {B = join-power 1 (Fin 2)}
    {C = join-power 2 (Fin 2)}
    ( zero-Fin-2 (join-power 1 (Fin 2)))

equiv-second-right-join-power-two-two-Fin-2 :
  (join-power 1 (Fin 2) * join-power 2 (Fin 2)) ≃
  (Fin 2 * (raise-empty lzero * join-power 2 (Fin 2)))
equiv-second-right-join-power-two-two-Fin-2 =
  equiv-associative-join-twist
    {A = Fin 2}
    {B = raise-empty lzero}
    {C = join-power 2 (Fin 2)}

equiv-second-join-power-two-two-Fin-2 :
  Fin 2 * (join-power 1 (Fin 2) * join-power 2 (Fin 2)) ≃
  Fin 2 * (Fin 2 * (raise-empty lzero * join-power 2 (Fin 2)))
equiv-second-join-power-two-two-Fin-2 =
  equiv-join id-equiv equiv-second-right-join-power-two-two-Fin-2

equiv-third-right-join-power-two-two-Fin-2 :
  Fin 2 * (raise-empty lzero * join-power 2 (Fin 2)) ≃
  Fin 2 * join-power 2 (Fin 2)
equiv-third-right-join-power-two-two-Fin-2 =
  equiv-join
    ( id-equiv)
    ( inv-equiv (left-unit-law-join-is-empty is-empty-raise-empty))

equiv-third-join-power-two-two-Fin-2 :
  Fin 2 * (Fin 2 * (raise-empty lzero * join-power 2 (Fin 2))) ≃
  Fin 2 * (Fin 2 * join-power 2 (Fin 2))
equiv-third-join-power-two-two-Fin-2 =
  equiv-join id-equiv equiv-third-right-join-power-two-two-Fin-2

compute-point-second-equiv-join-power-two-two-Fin-2 :
  map-equiv equiv-second-join-power-two-two-Fin-2
    ( inl-join
      ( zero-Fin-2 (join-power 1 (Fin 2) * join-power 2 (Fin 2)))) ＝
  inl-join
    ( zero-Fin-2
      ( Fin 2 * (raise-empty lzero * join-power 2 (Fin 2))))
compute-point-second-equiv-join-power-two-two-Fin-2 =
  compute-inl-map-join
    ( id)
    ( map-equiv equiv-second-right-join-power-two-two-Fin-2)
    ( zero-Fin-2 (join-power 1 (Fin 2) * join-power 2 (Fin 2)))

compute-point-third-equiv-join-power-two-two-Fin-2 :
  map-equiv equiv-third-join-power-two-two-Fin-2
    ( inl-join
      ( zero-Fin-2
        ( Fin 2 * (raise-empty lzero * join-power 2 (Fin 2))))) ＝
  point-join-power-Fin-2 3
compute-point-third-equiv-join-power-two-two-Fin-2 =
  compute-inl-map-join
    ( id)
    ( map-equiv equiv-third-right-join-power-two-two-Fin-2)
    ( zero-Fin-2
      ( Fin 2 * (raise-empty lzero * join-power 2 (Fin 2))))

equiv-join-power-two-two-Fin-2 :
  join-power 2 (Fin 2) * join-power 2 (Fin 2) ≃ join-power 4 (Fin 2)
equiv-join-power-two-two-Fin-2 =
  equiv-third-join-power-two-two-Fin-2 ∘e
  equiv-second-join-power-two-two-Fin-2 ∘e
  equiv-first-join-power-two-two-Fin-2

compute-point-equiv-join-power-two-two-Fin-2 :
  map-equiv equiv-join-power-two-two-Fin-2
    ( inl-join (point-join-power-Fin-2 1)) ＝
  point-join-power-Fin-2 3
compute-point-equiv-join-power-two-two-Fin-2 =
  ( ap
    ( map-equiv equiv-third-join-power-two-two-Fin-2 ∘
      map-equiv equiv-second-join-power-two-two-Fin-2)
    ( compute-point-first-equiv-join-power-two-two-Fin-2)) ∙
  ( ap
    ( map-equiv equiv-third-join-power-two-two-Fin-2)
    ( compute-point-second-equiv-join-power-two-two-Fin-2)) ∙
  compute-point-third-equiv-join-power-two-two-Fin-2

equiv-join-sphere-1-join-power-Fin-2 :
  sphere 1 * sphere 1 ≃
  join-power 2 (Fin 2) * join-power 2 (Fin 2)
equiv-join-sphere-1-join-power-Fin-2 =
  equiv-join
    ( inv-equiv equiv-sphere-1-join-power-Fin-2)
    ( inv-equiv equiv-sphere-1-join-power-Fin-2)
```
