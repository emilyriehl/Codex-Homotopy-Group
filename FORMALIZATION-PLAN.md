# Formalization plan: pi_3(S^2) = Z

This is a planning artifact only. It does not add proofs, postulates, or
modules under `src/`.

## Scope and target statement

The target is the HoTT-book calculation of the third homotopy group of the
2-sphere. In current agda-unimath terminology, the expected final statement
should be an isomorphism from the group underlying the concrete homotopy group
of the pointed 2-sphere to the additive group of integers.

Important indexing note: `synthetic-homotopy-theory.homotopy-groups` documents
an "Obi-wan error" in `concrete-homotopy-group`: the index `n` names the
`(n+1)`-st abstract homotopy group. Therefore pi_3(S^2) should correspond to
`concrete-homotopy-group 2 (sphere-Pointed-Type 2)`, not index `3`.

Candidate final shape:

```agda
iso-Group
  (group-Concrete-Group
    (concrete-homotopy-group 2 (sphere-Pointed-Type 2)))
  ℤ-Group
```

Before proving anything, this target signature should be confirmed with the
maintainers/harness and then treated as pinned.

## Mathematical route

The route in the HoTT book is:

1. Define fiber sequences for pointed maps and prove the long exact sequence of
   homotopy groups. The relevant exact segment for a fibration with fiber `F`,
   total space `E`, and base `B` is:

   ```text
   pi_3(F) -> pi_3(E) -> pi_3(B) -> pi_2(F)
   ```

2. Construct the Hopf fibration:

   ```text
   S^1 -> S^3 -> S^2
   ```

   The book constructs this as a Hopf construction from a connected H-space
   `A`, yielding a fibration over `suspension A` with fiber `A` and total space
   `A * A`. For `A = S^1`, this gives a fibration over `S^2` whose total space
   is `S^1 * S^1`, then proves `S^1 * S^1 ~= S^3`.

3. Use the already-known homotopy groups of the circle. Since `S^1` is a
   1-type and `Omega(S^1) ~= Z`, the higher homotopy groups of `S^1` vanish:

   ```text
   pi_n(S^1) = 0 for n > 1
   ```

   In particular, `pi_3(S^1) = 0` and `pi_2(S^1) = 0`.

4. The long exact sequence for the Hopf fibration then gives an isomorphism:

   ```text
   pi_3(S^3) ~= pi_3(S^2)
   ```

5. Compute the diagonal homotopy groups of spheres:

   ```text
   pi_n(S^n) ~= Z for n >= 1
   ```

   The book proves this using the base case `pi_1(S^1) ~= Z`, the Hopf-derived
   case for `pi_2(S^2)`, and stability from the Freudenthal suspension theorem.
   The instance needed here is `pi_3(S^3) ~= Z`.

6. Compose the Hopf exact-sequence isomorphism with `pi_3(S^3) ~= Z` to obtain:

   ```text
   pi_3(S^2) ~= Z
   ```

Primary mathematical references:

- HoTT book `homotopy.tex`, long exact sequence and Hopf fibration:
  <https://github.com/HoTT/book/blob/master/homotopy.tex#L108-L143>
- HoTT book `homotopy.tex`, Freudenthal stability and final theorem:
  <https://github.com/HoTT/book/blob/master/homotopy.tex#L195-L200>
- Older HoTT-Agda source pointers found by GitHub/code search:
  `theorems/homotopy/HopfConstruction.agda`,
  `theorems/homotopy/HopfJunior.agda`,
  `theorems/homotopy/Hopf.agda`,
  `theorems/homotopy/Freudenthal.agda`,
  `theorems/homotopy/IterSuspensionStable.agda`,
  `theorems/homotopy/PinSn.agda`.

## Comparative formalization references

Coq-HoTT is a useful reference for proof architecture, but this project should
not mechanically port Coq proof scripts or preserve Coq-specific abstractions.
Use Coq-HoTT as a comparative formalization guide: identify the mathematical
decomposition, dependency order, and useful intermediate concepts, then write
native agda-unimath proofs using local APIs, local naming conventions, and the
one-concept-per-file organization.

Relevant Coq-HoTT files to consult for inspiration:

- `theories/Homotopy/ExactSequence.v` suggests the decomposition around
  `IsExact`, fiber sequences, iterated loop exactness, connecting maps, and the
  long exact sequence on homotopy groups.
- `theories/Homotopy/Hopf.v` suggests the main Hopf-construction milestones:
  the total-space join equivalence, Hopf retraction, H-space consequences, and
  the use of Freudenthal for the Licata-Finster calculation.
- `theories/Homotopy/HSpaceS1.v` suggests how the circle H-space structure is
  separated from the Hopf fibration proof.
- `theories/Homotopy/BlakersMassey.v` suggests a Freudenthal route via
  Blakers-Massey rather than a standalone theorem.
- `theories/Homotopy/PinSn.v` suggests the dependency order for the diagonal
  theorem `pi_n(S^n) ~= Z`.

When using these references, search agda-unimath first and implement the result
with agda-unimath definitions. Do not copy Coq proof terms, tactic scripts, or
module structure unless that structure independently fits agda-unimath style.

## Dependency inventory

Inventory status was checked with `rg` over `src/`. `EXISTS` means a concrete
agda-unimath module was found. `MISSING` means no corresponding agda-unimath
module/theorem was found by search.

| # | Prerequisite | Status | agda-unimath module path or proof guide | Notes |
|---|---|---|---|---|
| 1 | Pointed types and pointed maps | EXISTS | `structured-types.pointed-types`, `structured-types.pointed-maps` | Basic pointed infrastructure for loop spaces, fibers, and maps. |
| 2 | Fibers of pointed maps | EXISTS | `structured-types.fibers-of-pointed-maps` | Needed for pointed fibers in a fibration/fiber sequence. |
| 3 | Loop spaces | EXISTS | `synthetic-homotopy-theory.loop-spaces` | Defines `Ω` and `type-Ω`. |
| 4 | Functoriality of loop spaces | EXISTS | `synthetic-homotopy-theory.functoriality-loop-spaces` | Needed for maps induced on loop spaces. |
| 5 | Iterated loop spaces | EXISTS | `synthetic-homotopy-theory.iterated-loop-spaces` | Needed for all homotopy groups. |
| 6 | Homotopy groups as concrete groups | EXISTS | `synthetic-homotopy-theory.homotopy-groups` | Defines `concrete-homotopy-group`; note the off-by-one index convention. |
| 7 | Concrete groups | EXISTS | `group-theory.concrete-groups` | The homotopy group API lands here. |
| 8 | Group homomorphisms, kernels, images, isomorphisms | EXISTS | `group-theory.homomorphisms-groups`, `group-theory.kernels-homomorphisms-groups`, `group-theory.images-of-group-homomorphisms`, `group-theory.isomorphisms-groups` | Useful for exactness once the LES is formalized. |
| 9 | Equivalences/isomorphisms of concrete groups | EXISTS | `group-theory.equivalences-concrete-groups`, `group-theory.isomorphisms-concrete-groups` | Some bridge lemmas may still be absent; avoid depending on unimplemented bridge TODOs if possible. |
| 10 | Trivial groups and trivial concrete groups | EXISTS | `group-theory.trivial-groups`, `group-theory.trivial-concrete-groups` | Needed for zero endpoints in exact sequences. |
| 11 | Integers and additive integer group | EXISTS | `elementary-number-theory.integers`, `elementary-number-theory.addition-integers`, `elementary-number-theory.group-of-integers` | `ℤ-Group` and `ℤ-Ab` exist. |
| 12 | Universal property of integers | EXISTS | `elementary-number-theory.universal-property-integers` | May help for circle/group maps. |
| 13 | Truncation levels and truncated types | EXISTS | `foundation.truncation-levels`, `foundation.truncated-types`, `foundation-core.truncation-levels`, `foundation-core.truncated-types` | Used throughout homotopy groups and exactness. |
| 14 | Set and propositional truncations | EXISTS | `foundation.set-truncations`, `foundation.propositional-truncations` | Needed for homotopy groups and images. |
| 15 | Connected types and connected maps | EXISTS | `foundation.connected-types`, `foundation.connected-maps`, `foundation.0-connected-types` | Needed for Freudenthal and connectedness of spheres. |
| 16 | Circle HIT and `S^1 ~= sphere 1` | EXISTS | `synthetic-homotopy-theory.circle` | Provides `𝕊¹`, universal properties, and `equiv-sphere-1-circle`. |
| 17 | Universal cover of circle and `Omega(S^1) ~= Z` | EXISTS | `synthetic-homotopy-theory.universal-cover-circle` | Provides `compute-loop-space-circle`. |
| 18 | Spheres | EXISTS | `synthetic-homotopy-theory.spheres` | Defines `sphere-Pointed-Type` and `sphere`. |
| 19 | Suspensions and suspension universal properties | EXISTS | `synthetic-homotopy-theory.suspensions-of-types`, `synthetic-homotopy-theory.universal-property-suspensions`, `synthetic-homotopy-theory.dependent-universal-property-suspensions` | Freudenthal and sphere definitions build on suspension. |
| 20 | Pushouts, descent, and flattening | EXISTS | `synthetic-homotopy-theory.pushouts`, `synthetic-homotopy-theory.descent-pushouts`, `synthetic-homotopy-theory.flattening-lemma-pushouts` | Needed for Hopf construction and total-space computations. |
| 21 | Joins and pushout products | EXISTS | `synthetic-homotopy-theory.joins-of-types`, `synthetic-homotopy-theory.joins-of-maps`, `synthetic-homotopy-theory.pushout-products`, `synthetic-homotopy-theory.dependent-pushout-products` | Hopf total space is `S^1 * S^1`. |
| 22 | Codiagonals/fiberwise suspension | EXISTS | `synthetic-homotopy-theory.codiagonals-of-maps` | Likely useful for fiberwise suspension/joins. |
| 23 | Double/triple loop coherence and Eckmann-Hilton | EXISTS | `synthetic-homotopy-theory.double-loop-spaces`, `synthetic-homotopy-theory.triple-loop-spaces`, `synthetic-homotopy-theory.eckmann-hilton-argument` | The book points to Eckmann-Hilton as underlying the Hopf phenomenon. |
| 24 | Cofibers of pointed maps | EXISTS | `synthetic-homotopy-theory.cofibers-of-pointed-maps` | Not central to the main route, but adjacent sequence infrastructure exists. |
| 25 | General pointed fiber sequences | MISSING | Develop natively from HoTT book `homotopy.tex` lines 108-119, guided by Coq-HoTT `ExactSequence.v` for decomposition only. | Needed before the LES can be stated uniformly. |
| 26 | Long exact sequence of homotopy groups | MISSING | Develop natively from HoTT book `homotopy.tex` lines 119-133, using Coq-HoTT `ExactSequence.v` only as proof-architecture guidance. | Major prerequisite; includes maps on homotopy groups and exactness. |
| 27 | Exactness-to-isomorphism lemma with zero endpoints | MISSING | Prove natively from HoTT book lemma `thm:ses` in `homotopy.tex` lines 134-135, adapting to agda-unimath `Group`/`Ab`. | Needed to extract `pi_3(S^3) ~= pi_3(S^2)` from the Hopf LES. |
| 28 | Hopf construction for connected H-spaces | MISSING | Develop natively from HoTT book `sec:hopf`, using Coq-HoTT `Hopf.v` and older HoTT-Agda only for decomposition and lemma order. | Produces fibration over `suspension A` with fiber `A` and total space `A * A`. |
| 29 | Circle as connected H-space | MISSING | Develop natively from HoTT book `lem:hspace-S1`, guided by Coq-HoTT `HSpaceS1.v` for statement separation. | The circle exists, but this packaged H-space structure was not found. |
| 30 | Hopf fibration `S^1 -> S^3 -> S^2` and total-space equivalence | MISSING | Develop natively from HoTT book `thm:hopf-fibration`, using Coq-HoTT `Hopf.v` only to identify conceptual milestones. | Includes proving `S^1 * S^1 ~= S^3`. |
| 31 | Higher homotopy groups of `S^1` vanish | MISSING | Derive from existing `compute-loop-space-circle` plus truncation/set facts; HoTT book `cor:pi1s1`. | The base equivalence exists; packaged group-level vanishing has partial local infrastructure and may need final Hopf-facing packaging. |
| 32 | Freudenthal suspension theorem | MISSING | Develop natively from HoTT book `thm:freudenthal`/`cor:freudenthal-equiv`; Coq-HoTT `BlakersMassey.v` suggests a Blakers-Massey route. | High risk, proof-heavy homotopy-theoretic development. |
| 33 | Stability of homotopy groups of spheres | MISSING | Develop natively from HoTT book `cor:stability-spheres`, using Coq-HoTT `PinSn.v` and older HoTT-Agda only for dependency order. | Depends on Freudenthal and connectedness of spheres. |
| 34 | Diagonal theorem `pi_n(S^n) ~= Z` | MISSING | Develop natively from HoTT book `thm:pinsn`; Coq-HoTT `PinSn.v` is a proof-architecture reference for the induction. | Needed at instance `n = 3`. |
| 35 | Final theorem `pi_3(S^2) ~= Z` | MISSING | New agda-unimath assembly module after prerequisites land. | Should only compose established isomorphisms; do not prove directly. |

Summary counts: `EXISTS = 24`, `MISSING = 11`.

## Searches run

Representative local searches used to classify the inventory:

```sh
rg --files src | rg 'homotopy-groups|spheres|circle|universal-cover-circle'
rg --files src | rg 'suspensions-of-types|pushouts|joins-of-types|joins-of-maps'
rg --files src | rg 'concrete-groups|homomorphisms-groups|group-of-integers'
rg --files src | rg 'connected-types|connected-maps|truncated-types|set-truncations'
rg -n 'Hopf|hopf|Freudenthal|freudenthal|long exact|fiber sequence|exact sequence|PinSn' src
```

The last search found only prose mentions in existing agda-unimath modules, not
formal Hopf/Freudenthal/LES/PinSn modules.

A shallow Coq-HoTT clone was searched separately for comparative references.
The findings are recorded above and should be treated as proof guidance, not
port targets.

## New agda-unimath additions needed

Prefer new leaf modules under `src/synthetic-homotopy-theory/` rather than
extending foundational modules until absolutely necessary.

Likely new modules:

- `src/synthetic-homotopy-theory/fiber-sequences.lagda.md`
- `src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md`
- `src/synthetic-homotopy-theory/higher-homotopy-groups-truncated-types.lagda.md`
- `src/synthetic-homotopy-theory/h-spaces.lagda.md` or a narrower
  `h-space-structure-circle.lagda.md`, depending on existing naming guidance
- `src/synthetic-homotopy-theory/hopf-construction.lagda.md`
- `src/synthetic-homotopy-theory/hopf-fibration.lagda.md`
- `src/synthetic-homotopy-theory/freudenthal-suspension-theorem.lagda.md`
- `src/synthetic-homotopy-theory/stability-homotopy-groups-spheres.lagda.md`
- `src/synthetic-homotopy-theory/homotopy-groups-spheres.lagda.md`
- `src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md`

Potential small supporting modules outside `synthetic-homotopy-theory`:

- `src/group-theory/isomorphisms-from-exact-sequences-groups.lagda.md`, if the
  exactness-to-isomorphism extraction is best stated algebraically.
- A small concrete-group bridge module only if the final theorem must use
  `Concrete-Group` isomorphisms rather than `Group` isomorphisms of underlying
  groups.

High-fan-in/cache-sensitive targets:

- `src/foundation/` and `src/foundation-core/`: avoid edits unless a reusable
  truncation/connectedness lemma clearly belongs there. New leaf modules are
  safer for cache invalidation.
- `src/synthetic-homotopy-theory.lagda.md` and other umbrella/import modules:
  delay adding imports until each leaf module typechecks.
- Existing central modules such as
  `synthetic-homotopy-theory.homotopy-groups`,
  `synthetic-homotopy-theory.spheres`, and
  `synthetic-homotopy-theory.suspensions-of-types`: avoid changing their public
  APIs unless maintainers request it.

## Tractability and risks

This is not a single narrow formalization. The target depends on several large
missing developments: the homotopy LES, the Hopf fibration, Freudenthal, and
the diagonal theorem for spheres. The existing library has good foundations
for the route: circles, spheres, suspensions, pushouts, joins, truncations,
connectedness, loop spaces, homotopy groups, and integers are present. The
missing work is mainly theorem infrastructure and proof packaging, not basic
definitions.

Main risks:

- **Long exact sequence risk:** requires careful pointed-map/fiber-sequence
  bookkeeping, induced maps on homotopy groups, exactness, and group/abelian
  group compatibility.
- **Hopf fibration risk:** constructing the fibration from the H-space circle
  and proving the total space is `S^3` will stress pushout, join, and
  fiberwise-descent infrastructure.
- **Freudenthal risk:** large encode-decode proof with high coherence cost.
  Coq-HoTT suggests a Blakers-Massey route; older HoTT-Agda and Coq-HoTT should
  be used as proof-architecture references rather than code to port.
- **Statement-shape risk:** the library's concrete homotopy-group indexing and
  concrete-group/group bridge must be fixed before any proof work starts.
- **Cache risk:** touching `foundation` or umbrella modules too early will
  invalidate large parts of the library.

Verification note: sanity typechecks were attempted with `./check.sh` on
existing relevant modules, but this sandbox could not reach the Nix daemon or
write Nix fetcher locks, so Agda did not start. The failure was environmental,
not an Agda type error. On the intended environment, every new `.lagda.md` file
should be checked with:

```sh
./check.sh src/synthetic-homotopy-theory/<module>.lagda.md
```

## Recommended order of work

1. **Human checkpoint and go/no-go.** Confirm the final theorem signature,
   especially the `concrete-homotopy-group 2` indexing and whether the desired
   target is a `Group` isomorphism or a `Concrete-Group` equivalence.

2. **Small packaging lemmas first.** Package the existing circle result into
   group-level statements:

   ```text
   pi_1(S^1) ~= Z
   pi_n(S^1) = 0 for n > 1
   ```

   Also build any small exactness-to-isomorphism and trivial-group lemmas needed
   by the later LES extraction.

3. **Define pointed fiber sequences and induced maps on homotopy groups.** Keep
   this generic but minimal: enough to state and use the LES for Hopf.

4. **Develop the long exact sequence of homotopy groups.** Prove the exact
   segment needed for the Hopf application first, then generalize only as far
   as the HoTT-book statement requires. Use Coq-HoTT `ExactSequence.v` only for
   decomposition guidance.

5. **Develop the Hopf construction and Hopf fibration.** Start with the circle
   H-space structure, then the general Hopf construction, then specialize to
   `S^1` and prove the total space equivalent to `S^3`. Use Coq-HoTT
   `Hopf.v`/`HSpaceS1.v` to identify milestones, not to translate code.

6. **Extract `pi_3(S^3) ~= pi_3(S^2)`.** Use the Hopf LES and the vanishing of
   `pi_3(S^1)` and `pi_2(S^1)`.

7. **Develop Freudenthal and sphere stability.** Use the HoTT book as the
   mathematical reference, and use Coq-HoTT `BlakersMassey.v` plus older
   HoTT-Agda only for decomposition and dependency order.

8. **Develop `pi_n(S^n) ~= Z`.** Use the HoTT-book induction and consult
   Coq-HoTT `PinSn.v` plus older HoTT-Agda only for proof architecture and
   dependency order, then instantiate it at `n = 3`.

9. **Assemble the final theorem.** The final module should be a short
   composition of:

   ```text
   pi_3(S^2) ~= pi_3(S^3) ~= Z
   ```

   It should not contain new Hopf/Freudenthal proof work.

10. **Pre-PR verification.** For every new module, run `./check.sh <file>`.
    Before any PR, run `make pre-commit` and ask for human review that the
    literate exposition reads like normal agda-unimath documentation.

