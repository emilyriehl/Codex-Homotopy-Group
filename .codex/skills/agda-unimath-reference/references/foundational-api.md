# Foundational API cheatsheet

Quick reference to the foundational types and lemmas in agda-unimath (flags `--without-K --exact-split`), with module paths and key signatures so you import existing constructions instead of re-proving them. Names and types here are copied from source, but the library moves — always `rg` the actual `.lagda.md` under `src/` to confirm the exact current signature before relying on it.

Note on glyphs: the identity type uses the FULL-WIDTH equals `＝` (U+FF1D, typed `\=`), not ASCII `=`. Other unicode: `≃` (`\simeq`), `~` (`\sim`), `∙` (`\.`), `⊔` (`\lub`), `Σ` (`\GS`/`\Sigma`), `Π` (`\GP`), `¬` (`\neg`), `𝕋` (`\bT`), `∘` (`\o`), `∘e`.

## 1. Universes

Module: `foundation.universe-levels` (re-exports `Agda.Primitive`).

- `UU` — universe of types; `Agda.Primitive.Set` renamed to `UU`.
- `UU l : UU (lsuc l)` — the universe at level `l : Level`.
- `Level : Set` — the type of universe levels.
- `lzero : Level`
- `lsuc : Level → Level`
- `_⊔_ : Level → Level → Level` — least upper bound of levels.
- `UUω` — the omega universe (`Setω`), for level-polymorphic things.

## 2. Dependent pair types (Σ)

Module: `foundation.dependent-pair-types`; product in `foundation-core.cartesian-product-types`.

- `record Σ {l1 l2} (A : UU l1) (B : A → UU l2) : UU (l1 ⊔ l2)` — constructor `pair`.
- `pattern _,_ a b = pair a b` — `infixr 3 _,_`; write pairs as `(a , b)`.
- `pr1 : Σ A B → A` — first projection (record field).
- `pr2 : (t : Σ A B) → B (pr1 t)` — second projection.
- `ind-Σ : ((x : A) (y : B x) → C (x , y)) → (t : Σ A B) → C t`
- `triple a b c = (a , b , c)` — iterated pair.
- `_×_ : UU l1 → UU l2 → UU (l1 ⊔ l2)` — `infixr 15`; defined as `product A B = Σ A (λ _ → B)`.

## 3. Dependent function types (Π)

Module: `foundation-core.function-types` (composition, identity); Π is built-in `(x : A) → B x`.

- `id : {A : UU l} → A → A` — identity function.
- `id' : (A : UU l) → A → A`
- `_∘_ : ({a : A} → B a → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)` — `infixr 15`; dependent composition `(g ∘ f) a = g (f a)`.
- `ev-point : (a : A) {P : A → UU l2} → ((x : A) → P x) → P a`
- (Universal properties of Π live in `foundation.dependent-function-types`.)

## 4. Identity types

Module: `foundation-core.identity-types`; `ap` in `foundation.action-on-identifications-functions`; `tr` in `foundation-core.transport-along-identifications`.

- `data Id (x : A) : A → UU l` with constructor `refl : Id x x`.
- `_＝_ : A → A → UU l` — `infix 6`; `(a ＝ b) = Id a b`. FULL-WIDTH `＝`.
- `refl : x ＝ x`
- `_∙_ : x ＝ y → y ＝ z → x ＝ z` — `infixl 15`; concatenation, `refl ∙ q = q`.
- `concat : x ＝ y → (z : A) → y ＝ z → x ＝ z`
- `concat' : (x : A) → y ＝ z → x ＝ y → x ＝ z`
- `inv : x ＝ y → y ＝ x` — inverse.
- `assoc : (p : x ＝ y)(q : y ＝ z)(r : z ＝ w) → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)`
- `left-unit : refl ∙ p ＝ p` (definitional); `right-unit : p ∙ refl ＝ p`
- `left-inv : inv p ∙ p ＝ refl`; `right-inv : p ∙ inv p ＝ refl`
- `inv-inv : inv (inv p) ＝ p`
- `ap : (f : A → B) → x ＝ y → f x ＝ f y` — `ap f refl = refl`.
- `tr : (B : A → UU l2) → x ＝ y → B x → B y` — transport; `tr B refl b = b`.
- `inv-tr : (B : A → UU l2) → y ＝ x → B x → B y`
- `ind-Id : (x : A)(B : (y : A) → x ＝ y → UU l2) → B x refl → (y : A)(p : x ＝ y) → B y p`

Equational reasoning (same module):

```text
equational-reasoning
  x ＝ y by eq-1
    ＝ z by eq-2
```

- `equational-reasoning_ : (x : X) → x ＝ x` — `infixl 1`.
- `step-equational-reasoning : (x ＝ y) → (u : X) → (y ＝ u) → (x ＝ u)`, with `syntax ... = p ＝ z by q`. Result is right-associated: `eq-1 ∙ (eq-2 ∙ ...)`.

## 5. Equivalences

Modules: `foundation-core.equivalences` (core) and `foundation.equivalences` (more).

- `is-equiv : (A → B) → UU (l1 ⊔ l2)` — `is-equiv f = section f × retraction f` (bi-invertible).
- `_≃_ : UU l1 → UU l2 → UU (l1 ⊔ l2)` — `infix 6`; `A ≃ B = Σ (A → B) is-equiv`.
- `map-equiv : A ≃ B → (A → B)` — `pr1 e`.
- `is-equiv-map-equiv : (e : A ≃ B) → is-equiv (map-equiv e)` — `pr2 e`.
- `map-inv-equiv : A ≃ B → (B → A)` — the inverse map.
- `id-equiv : A ≃ A`
- `_∘e_ : B ≃ X → A ≃ B → A ≃ X` — `comp-equiv`, composition of equivalences.
- `is-equiv-is-invertible : (g : B → A) → (f ∘ g ~ id) → (g ∘ f ~ id) → is-equiv f` — build `is-equiv` from a two-sided inverse.
- `is-invertible-is-equiv : is-equiv f → is-invertible f`
- Contractible-map characterization (module `foundation-core.contractible-maps`):
  - `is-contr-map : (A → B) → UU (l1 ⊔ l2)` — `is-contr-map f = (y : B) → is-contr (fiber f y)`.
  - `equiv-is-equiv : (f : A → B) → is-contr-map f ≃ is-equiv f` (in `foundation.contractible-maps`).

## 6. Homotopies

Module: `foundation-core.homotopies`.

- `_~_ : (f g : (x : A) → B x) → UU (l1 ⊔ l2)` — `infix 6`; `f ~ g = (x : A) → f x ＝ g x` (via `eq-value`).
- `refl-htpy : f ~ f`
- `_∙h_` — concatenation of homotopies; `inv-htpy` — inverse; `_·l_`, `_·r_` — left/right whiskering (all in this module).

## 7. Contractible types

Module: `foundation-core.contractible-types`.

- `is-contr : UU l → UU l` — `is-contr A = Σ A (λ a → (x : A) → a ＝ x)`.
- `center : is-contr A → A`
- `contraction : (c : is-contr A) → (x : A) → center c ＝ x`
- `eq-is-contr : is-contr A → {x y : A} → x ＝ y`

## 8. Propositions, sets, truncation levels

Modules: `foundation-core.propositions`, `foundation-core.sets`, `foundation-core.truncated-types`, `foundation-core.truncation-levels` / `foundation.truncation-levels`, `foundation.truncations`.

- `is-prop : (A : UU l) → UU l` — `is-prop A = (x y : A) → is-contr (x ＝ y)`.
- `Prop : (l : Level) → UU (lsuc l)` — `Prop l = Σ (UU l) is-prop`.
- `type-Prop : Prop l → UU l`; `is-prop-type-Prop : (P : Prop l) → is-prop (type-Prop P)`.
- `is-set : UU l → UU l` — `is-set A = (x y : A) → is-prop (x ＝ y)`.
- `Set : (l : Level) → UU (lsuc l)` — `Set l = Σ (UU l) is-set`.
- `type-Set : Set l → UU l`; `is-set-type-Set : is-set type-Set`.
- `data 𝕋 : UU lzero` with `neg-two-𝕋 : 𝕋` and `succ-𝕋 : 𝕋 → 𝕋`. Aliases: `neg-one-𝕋`, `zero-𝕋`, `one-𝕋`, `two-𝕋`.
- `is-trunc : (k : 𝕋) → UU l → UU l` — `is-trunc neg-two-𝕋 A = is-contr A`; `is-trunc (succ-𝕋 k) A = (x y : A) → is-trunc k (x ＝ y)`.
- `Truncated-Type : (l : Level) → 𝕋 → UU (lsuc l)` — `Σ (UU l) (is-trunc k)`.
- Truncations (`foundation.truncations`):
  - `type-trunc : (k : 𝕋) → UU l → UU l`
  - `trunc : (k : 𝕋) → UU l → Truncated-Type l k`
  - `unit-trunc : A → type-trunc k A`

## 9. Coproducts, empty, unit, negation

Modules: `foundation-core.coproduct-types`, `foundation-core.empty-types` / `foundation.empty-types`, `foundation.unit-type`, `foundation-core.negation` / `foundation.negation`.

- `data _+_ (A : UU l1)(B : UU l2) : UU (l1 ⊔ l2)` — `infixr 10`; constructors `inl : A → A + B`, `inr : B → A + B`.
- `ind-coproduct : (C : A + B → UU l3) → ((x : A) → C (inl x)) → ((y : B) → C (inr y)) → (t : A + B) → C t`
- `data empty : UU lzero` (no constructors).
- `ex-falso : {A : UU l} → empty → A` — `ex-falso = ind-empty`.
- `is-empty : UU l → UU l` — `is-empty A = A → empty` (in `foundation-core.empty-types`).
- `record unit : UU lzero` with `instance constructor star`.
- `ind-unit : {P : unit → UU l} → P star → (x : unit) → P x`; `is-contr-unit : is-contr unit`.
- `¬_ : UU l → UU l` — `infix`; `¬ A = A → empty` (in `foundation-core.negation`).
- `is-prop-neg : is-prop (¬ A)`; `neg-Prop : Prop l1 → Prop l1`.

## 10. Function extensionality & univalence

Modules: `foundation.function-extensionality`, `foundation.univalence` (+ core `foundation-core.univalence`).

- `htpy-eq : f ＝ g → f ~ g` — canonical map, `htpy-eq p x = ap (ev x) p`.
- `eq-htpy : f ~ g → f ＝ g` — postulated inverse.
- `funext : function-extensionality` — witnesses `is-equiv htpy-eq` for all `f g`.
- `equiv-funext : (f ＝ g) ≃ (f ~ g)`
- `equiv-eq : A ＝ B → A ≃ B` — `equiv-eq = equiv-tr id` (in `foundation-core.univalence`).
- `map-eq : A ＝ B → (A → B)` — `map-equiv ∘ equiv-eq`.
- `eq-equiv : A ≃ B → A ＝ B` — postulated inverse.
- `univalence : univalence-axiom` — witnesses `is-equiv equiv-eq`.
- `equiv-univalence : (A ＝ B) ≃ (A ≃ B)`

## 11. Fibers and number types

Modules: `foundation-core.fibers-of-maps` / `foundation.fibers-of-maps`, `elementary-number-theory.natural-numbers`, `elementary-number-theory.integers`.

- `fiber : (f : A → B) (b : B) → UU (l1 ⊔ l2)` — `fiber f b = Σ A (λ x → f x ＝ b)`.
- `inclusion-fiber : fiber f b → A`
- `equiv-total-fiber : Σ B (fiber f) ≃ A`
- `data ℕ : UU lzero` with `zero-ℕ : ℕ`, `succ-ℕ : ℕ → ℕ`.
- `is-zero-ℕ : ℕ → UU lzero`
- `ℤ : UU lzero` — `ℤ = ℕ + (unit + ℕ)`.
- `zero-ℤ : ℤ` (`inr (inl star)`); `neg-one-ℤ : ℤ`; `in-neg-ℤ : ℕ → ℤ`.
- `int-ℕ : ℕ → ℤ` — inclusion of naturals (in `elementary-number-theory.integers`).

## 12. Equality In Fibers Of Maps

Module: `foundation.equality-fibers-of-maps`.

Use this file when a proof concerns equality between elements of a fiber
`fiber f b`. It avoids K-like direct pattern matching and gives the path data
needed to move between equality of fiber elements and equality under `ap f`.

Key names:

- `fiber-ap-eq-fiber f s t : s ＝ t → fiber (ap f) (pr2 s ∙ inv (pr2 t))`
- `equiv-fiber-ap-eq-fiber f s t : (s ＝ t) ≃ fiber (ap f) (pr2 s ∙ inv (pr2 t))`
- `map-inv-fiber-ap-eq-fiber f s t : fiber (ap f) (pr2 s ∙ inv (pr2 t)) → s ＝ t`
- `ap-pr1-map-inv-fiber-ap-eq-fiber f s t v : ap pr1 (map-inv-fiber-ap-eq-fiber f s t v) ＝ pr1 v`
- `triangle-fiber-ap-eq-fiber f s t` relates `fiber-ap-eq-fiber` to the `pair-eq-Σ` characterization of equality in a dependent pair.

The last two are especially useful in HoTT fiber-sequence work: the inverse map
constructs the equality in the fiber, while the projection coherence lets you
recover the underlying path needed for loop-space or image-comparison
arguments. If Agda says `pr1 (fiber-ap-eq-fiber ...) != ap pr1 α`, use
`triangle-fiber-ap-eq-fiber` to bridge that propositional equality.

## 13. Set-Truncation Helpers For Image Comparisons

Modules: `foundation.set-truncations`, `foundation.functoriality-set-truncation`,
`foundation.propositional-truncations`, and `foundation.propositions`.

Useful names for exactness proofs after set truncation:

- `unit-trunc-Set : A → type-trunc-Set A`
- `map-trunc-Set f : type-trunc-Set A → type-trunc-Set B`
- `naturality-unit-trunc-Set f : map-trunc-Set f ∘ unit-trunc-Set ~ unit-trunc-Set ∘ f`
- `apply-dependent-universal-property-trunc-Set'` for eliminating from a set truncation into a `Set`
- `apply-universal-property-trunc-Prop` for eliminating image witnesses, which are propositional truncations

A common exactness proof compares image predicates. Eliminate the outer image
witness into the target image proposition, eliminate the set-truncated preimage
into a function set, then build the new witness with `unit-trunc-Prop`. The
path component usually chains `naturality-unit-trunc-Set`, `ap unit-trunc-Set`
of an untruncated homotopy/projection law, and the old image-witness equality.
