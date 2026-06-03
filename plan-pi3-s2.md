# Plan to formalize pi_3(S^2) = Z in agda-unimath

This plan follows the proof strategy described in `email.md` and the HoTT
book's homotopy theory chapter. The workspace currently contains only
`email.md`, so the first concrete implementation step is to work in a checkout
of `UniMath/agda-unimath` and audit the current library state.

## Phase 0: Set up the experiment

1. Check out `UniMath/agda-unimath` locally and create a working branch.
2. Confirm the checking command, usually something like:

   ```sh
   ./check.sh src/synthetic-homotopy-theory/<file>.lagda.md
   ```

3. Add a lightweight experiment log recording:
   - prompt used
   - agent/model
   - files touched
   - Agda check command
   - elapsed time
   - human interventions
   - remaining holes/errors

This supports the reporting goals in `email.md`.

## Phase 1: Source audit

Before proving anything, search the current library for the exact available
infrastructure:

```sh
rg -n "homotopy-group|concrete-homotopy-group|set-homotopy-group" src/
rg -n "Freudenthal|freudenthal|suspension theorem" src/
rg -n "Hopf|hopf|H-space|h-space" src/
rg -n "long exact|exact sequence|fiber sequence" src/
rg -n "circle|universal-cover-circle|loop-homotopy-circle" src/synthetic-homotopy-theory/
rg -n "join|suspension|sphere" src/synthetic-homotopy-theory/
```

Expected relevant namespaces:

- `synthetic-homotopy-theory.homotopy-groups`
- `synthetic-homotopy-theory.spheres`
- `synthetic-homotopy-theory.circle`
- `synthetic-homotopy-theory.universal-cover-circle`
- `synthetic-homotopy-theory.suspensions-of-types`
- `synthetic-homotopy-theory.joins-of-types`
- `synthetic-homotopy-theory.loop-spaces`
- `structured-types`, for pointed types and H-spaces
- `group-theory` and `elementary-number-theory`, for the integer group

The first human review checkpoint should be after this audit. Decide whether
to prove the theorem by Hopf plus Freudenthal exactly as in the HoTT book, or
to use any stronger existing agda-unimath theorem if present.

## Phase 2: Fix the final statement

Choose the formal statement early. The merge-ready target should be an
isomorphism of concrete groups, with a weaker set-level equivalence as an
intermediate milestone.

Possible final shape, subject to current agda-unimath names:

```agda
iso-homotopy-group-sphere-two-three-integers :
  iso-Concrete-Group
    (concrete-homotopy-group 3 sphere-2)
    integer-Concrete-Group
```

or, if homotopy groups are packaged as groups of pointed types:

```agda
iso-homotopy-group-sphere-integers :
  iso-Group
    (homotopy-group 3 sphere-2-pointed-type)
    integer-Group
```

Do not guess this in code. Confirm exact names in
`homotopy-groups.lagda.md`, `spheres.lagda.md`, and the integer group files.

## Phase 3: Prove or reuse pi_1(S^1) = Z

This is probably already largely present via `universal-cover-circle`.

1. Reuse the existing universal cover of the circle.
2. Extract an equivalence `Omega S^1 ~= Z`.
3. Package it as a group isomorphism `pi_1(S^1) ~= Z`.
4. Prove higher homotopy groups of `S^1` vanish, at least the two needed
   later:
   - `pi_2(S^1) = 0`
   - `pi_3(S^1) = 0`

For the Hopf argument, only these vanishings are needed to identify
`pi_3(S^3) -> pi_3(S^2)` as an isomorphism.

## Phase 4: Formalize the Hopf construction

The HoTT book constructs the Hopf fibration from a connected H-space `A`: a
fibration over `susp A` with fiber `A` and total space `join A A`.

Break this into files:

1. `hopf-construction.lagda.md`
   - input: connected H-space `A`
   - output: fibration over `susp A`
   - fiber: `A`
   - total space: `join A A`

2. `h-space-circle.lagda.md`
   - construct the H-space structure on `S^1`
   - likely reuse circle multiplication if present

3. `hopf-fibration.lagda.md`
   - specialize Hopf construction to `S^1`
   - identify base as `S^2`
   - identify total space `S^1 * S^1` as `S^3`

The join-to-sphere identification is a serious subproject:
`S^1 * S^1 ~= S^3` uses associativity of joins and `susp A ~= bool * A`,
as described in the book.

## Phase 5: Formalize the needed exact-sequence consequence

The full long exact sequence is ideal, but for the final theorem a scoped
lemma may be more efficient:

```text
For a pointed fibration F -> E -> B,
if pi_3(F) = 0 and pi_2(F) = 0,
then pi_3(E) -> pi_3(B) is an isomorphism.
```

Apply it to the Hopf fibration:

```text
S^1 -> S^3 -> S^2
```

Since `pi_3(S^1) = 0` and `pi_2(S^1) = 0`, conclude:

```text
pi_3(S^3) ~= pi_3(S^2)
```

This corresponds to the HoTT book's use of the Hopf fibration and long exact
sequence.

## Phase 6: Formalize the diagonal sphere theorem

The HoTT book uses Freudenthal to prove:

```text
pi_n(S^n) ~= Z for n >= 1
```

and then specializes to `n = 3`.

Check whether agda-unimath already has Freudenthal in
`suspensions-of-types.lagda.md`. If yes, prove only the corollaries:

1. stability for spheres
2. `pi_n(S^n) ~= Z`
3. specialization `pi_3(S^3) ~= Z`

If Freudenthal is missing or incomplete, make this a separate milestone. It is
too large to hide inside the `pi_3(S^2)` file.

## Phase 7: Final assembly

Create a final file, probably in `src/synthetic-homotopy-theory/`, for
example:

```text
third-homotopy-group-2-sphere.lagda.md
```

Structure:

1. `## Idea`
   - The Hopf fibration identifies `pi_3(S^2)` with `pi_3(S^3)`.
   - Freudenthal/diagonal sphere theorem identifies `pi_3(S^3)` with `Z`.

2. `## Theorem`
   - final group isomorphism

3. proof:
   - compose `pi_3(S^2) ~= pi_3(S^3)` with `pi_3(S^3) ~= Z`
   - check orientation carefully

## Recommended milestones

1. Library audit and exact theorem statement.
2. `pi_1(S^1) ~= Z` packaged as a group isomorphism.
3. `pi_2(S^1) = 0` and `pi_3(S^1) = 0`.
4. Hopf construction for connected H-spaces.
5. Hopf fibration `S^1 -> S^3 -> S^2`.
6. Exact-sequence consequence giving `pi_3(S^3) ~= pi_3(S^2)`.
7. Diagonal theorem specialization `pi_3(S^3) ~= Z`.
8. Final theorem `pi_3(S^2) ~= Z`.

The highest-risk pieces are the Hopf fibration, join associativity /
`S^1 * S^1 ~= S^3`, and the exact-sequence machinery. The final theorem
itself should be small once those are in place.
