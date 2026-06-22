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

Inventory status was checked with `rg` over the agda-unimath library at the
start of the project. The `Library status` column is historical:
`EXISTS` means a concrete agda-unimath module/theorem was found then, while
`MISSING` means no corresponding agda-unimath module/theorem was found by that
search. The `Local status` column records subsequent progress in this
repository. For the authoritative current proof state, see
[the status report](STATUS-REPORT.md).

| # | Prerequisite | Library status | Local status | Module path or proof guide | Notes |
|---|---|---|---|---|---|
| 1 | Pointed types and pointed maps | EXISTS | Library dependency | `structured-types.pointed-types`, `structured-types.pointed-maps` | Basic pointed infrastructure for loop spaces, fibers, and maps. |
| 2 | Fibers of pointed maps | EXISTS | Library dependency | `structured-types.fibers-of-pointed-maps` | Needed for pointed fibers in a fibration/fiber sequence. |
| 3 | Loop spaces | EXISTS | Library dependency | `synthetic-homotopy-theory.loop-spaces` | Defines `Ω` and `type-Ω`. |
| 4 | Functoriality of loop spaces | EXISTS | Library dependency | `synthetic-homotopy-theory.functoriality-loop-spaces` | Needed for maps induced on loop spaces. |
| 5 | Iterated loop spaces | EXISTS | Library dependency | `synthetic-homotopy-theory.iterated-loop-spaces` | Needed for all homotopy groups. |
| 6 | Homotopy groups as concrete groups | EXISTS | Library dependency | `synthetic-homotopy-theory.homotopy-groups` | Defines `concrete-homotopy-group`; note the off-by-one index convention. |
| 7 | Concrete groups | EXISTS | Library dependency | `group-theory.concrete-groups` | The homotopy group API lands here. |
| 8 | Group homomorphisms, kernels, images, isomorphisms | EXISTS | Library dependency | `group-theory.homomorphisms-groups`, `group-theory.kernels-homomorphisms-groups`, `group-theory.images-of-group-homomorphisms`, `group-theory.isomorphisms-groups` | Useful for exactness once the LES is formalized. |
| 9 | Equivalences/isomorphisms of concrete groups | EXISTS | Library dependency | `group-theory.equivalences-concrete-groups`, `group-theory.isomorphisms-concrete-groups` | Some bridge lemmas may still be absent; avoid depending on unimplemented bridge TODOs if possible. |
| 10 | Trivial groups and trivial concrete groups | EXISTS | Library dependency | `group-theory.trivial-groups`, `group-theory.trivial-concrete-groups` | Needed for zero endpoints in exact sequences. |
| 11 | Integers and additive integer group | EXISTS | Library dependency | `elementary-number-theory.integers`, `elementary-number-theory.addition-integers`, `elementary-number-theory.group-of-integers` | `ℤ-Group` and `ℤ-Ab` exist. |
| 12 | Universal property of integers | EXISTS | Library dependency | `elementary-number-theory.universal-property-integers` | May help for circle/group maps. |
| 13 | Truncation levels and truncated types | EXISTS | Library dependency | `foundation.truncation-levels`, `foundation.truncated-types`, `foundation-core.truncation-levels`, `foundation-core.truncated-types` | Used throughout homotopy groups and exactness. |
| 14 | Set and propositional truncations | EXISTS | Library dependency | `foundation.set-truncations`, `foundation.propositional-truncations` | Needed for homotopy groups and images. |
| 15 | Connected types and connected maps | EXISTS | Library dependency | `foundation.connected-types`, `foundation.connected-maps`, `foundation.0-connected-types` | Needed for Freudenthal and connectedness of spheres. |
| 16 | Circle HIT and `S^1 ~= sphere 1` | EXISTS | Library dependency | `synthetic-homotopy-theory.circle` | Provides `𝕊¹`, universal properties, and `equiv-sphere-1-circle`. |
| 17 | Universal cover of circle and `Omega(S^1) ~= Z` | EXISTS | Library dependency | `synthetic-homotopy-theory.universal-cover-circle` | Provides `compute-loop-space-circle`. |
| 18 | Spheres | EXISTS | Library dependency | `synthetic-homotopy-theory.spheres` | Defines `sphere-Pointed-Type` and `sphere`. |
| 19 | Suspensions and suspension universal properties | EXISTS | Library dependency | `synthetic-homotopy-theory.suspensions-of-types`, `synthetic-homotopy-theory.universal-property-suspensions`, `synthetic-homotopy-theory.dependent-universal-property-suspensions` | Freudenthal and sphere definitions build on suspension. |
| 20 | Pushouts, descent, and flattening | EXISTS | Library dependency | `synthetic-homotopy-theory.pushouts`, `synthetic-homotopy-theory.descent-pushouts`, `synthetic-homotopy-theory.flattening-lemma-pushouts` | Needed for Hopf construction and total-space computations. |
| 21 | Joins and pushout products | EXISTS | Library dependency | `synthetic-homotopy-theory.joins-of-types`, `synthetic-homotopy-theory.joins-of-maps`, `synthetic-homotopy-theory.pushout-products`, `synthetic-homotopy-theory.dependent-pushout-products` | Hopf total space is `S^1 * S^1`. |
| 22 | Codiagonals/fiberwise suspension | EXISTS | Library dependency | `synthetic-homotopy-theory.codiagonals-of-maps` | Likely useful for fiberwise suspension/joins. |
| 23 | Double/triple loop coherence and Eckmann-Hilton | EXISTS | Library dependency | `synthetic-homotopy-theory.double-loop-spaces`, `synthetic-homotopy-theory.triple-loop-spaces`, `synthetic-homotopy-theory.eckmann-hilton-argument` | The book points to Eckmann-Hilton as underlying the Hopf phenomenon. |
| 24 | Cofibers of pointed maps | EXISTS | Library dependency | `synthetic-homotopy-theory.cofibers-of-pointed-maps` | Not central to the main route, but adjacent sequence infrastructure exists. |
| 25 | General pointed fiber sequences | MISSING | Done locally | `src/structured-types/fiber-sequences.lagda.md`; HoTT book `homotopy.tex` lines 108-119 | The local module defines and packages pointed fiber sequences. |
| 26 | Long exact sequence of homotopy groups | MISSING | Partial locally | `src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md`; Coq-HoTT `ExactSequence.v` as decomposition guide only | The local LES bridge covers the Hopf-facing set-truncated and group-exactness segments, including arbitrary-index direct fibration-boundary exactness, but not a full upstream-ready HoTT Book Theorem 8.4.6 package. |
| 27 | Exactness-to-isomorphism lemma with zero endpoints | MISSING | Done locally | `src/group-theory/isomorphisms-from-exact-sequences-groups.lagda.md` | Used to extract Hopf LES comparison isomorphisms. |
| 28 | Hopf construction for connected H-spaces | MISSING | Partial locally | `src/synthetic-homotopy-theory/hopf-construction.lagda.md`, `src/synthetic-homotopy-theory/hopf-construction-fiber-sequence.lagda.md`; HoTT book `sec:hopf` | The generic Hopf map, its pointed form, and the canonical fiber sequence of that pointed map are checked; the geometric fiber identification remains. |
| 29 | Circle as connected H-space | MISSING | Done locally | `src/synthetic-homotopy-theory/h-space-structure-circle.lagda.md`; `synthetic-homotopy-theory.circle` | The local module packages `𝕊¹-H-Space` and the transported `sphere-1-H-Space`, proves that left and right translations on both are equivalences, and packages the Hopf shear equivalence `(x , y) ↦ (y , x · y)` on `S¹ × S¹`; circle connectedness is supplied by the library circle module. |
| 30 | Hopf fibration `S^1 -> S^3 -> S^2` and total-space equivalence | MISSING | Partial locally | `src/synthetic-homotopy-theory/hopf-fiber-sequence.lagda.md`, `src/synthetic-homotopy-theory/hopf-family-circle.lagda.md`, `src/synthetic-homotopy-theory/suspensions-as-joins.lagda.md`, `src/synthetic-homotopy-theory/functoriality-joins-of-types.lagda.md`, `src/synthetic-homotopy-theory/type-arithmetic-joins-of-types.lagda.md`, `src/synthetic-homotopy-theory/spheres-as-join-powers.lagda.md`; HoTT book `thm:hopf-fibration` | The desired packaged sequence is still scaffolded, but the Hopf-family and first total-space layers are checked: `hopf-family-circle` defines the family over `S²` whose meridians are classified by left multiplication on `S¹`, packages its projection as a pointed fiber sequence with fiber `S¹`, proves by the flattening lemma that the actual family total space is a pushout of the family-induced flattened span, names the associated explicit descent data and flattened span, and proves that `S¹ * S¹` is a pushout of that explicit flattened span via the Hopf shear; `h-space-structure-circle` packages the Hopf shear equivalence needed for the span comparison; `suspensions-as-joins` proves `Fin 2 * X ≃ suspension X`; `functoriality-joins-of-types` proves functoriality and preservation of equivalences for joins; `type-arithmetic-joins-of-types` proves `A * B ≃ B * A`; and `spheres-as-join-powers` proves `join-power (succ n) (Fin 2) ≃ sphere n`, including `join-power 4 (Fin 2) ≃ S^3`, plus the bridge from `S^1 * S^1` to `join-power 2 (Fin 2) * join-power 2 (Fin 2)`. Next targets are the comparison between the family-induced flattened span and the explicit flattened descent span, associativity/join-power multiplication from that join to `join-power 4 (Fin 2)`, and transport/packaging of the resulting fiber sequence as `S^1 -> S^3 -> S^2`. |
| 31 | Higher homotopy groups of `S^1` vanish | MISSING | Mostly done locally | `src/synthetic-homotopy-theory/homotopy-groups-circle.lagda.md`; HoTT book `cor:pi1s1` | Positive concrete homotopy groups of the circle and 1-sphere are trivial; further packaging may still be useful. |
| 32 | Freudenthal suspension theorem | MISSING | Not started locally | HoTT book `thm:freudenthal`/`cor:freudenthal-equiv`; Coq-HoTT `BlakersMassey.v` as decomposition guide | High risk, proof-heavy homotopy-theoretic development. |
| 33 | Stability of homotopy groups of spheres | MISSING | Stubbed locally | `src/synthetic-homotopy-theory/stability-third-homotopy-group-sphere-3.lagda.md`; HoTT book `cor:stability-spheres` | The needed comparison `π₂(S²) ≅ π₃(S³)` is recorded as an unfinished theorem. |
| 34 | Diagonal theorem `pi_n(S^n) ~= Z` | MISSING | Reduced locally | `src/synthetic-homotopy-theory/third-homotopy-group-sphere-3.lagda.md`; HoTT book `thm:pinsn` | The `n = 3` calculation is assembled from the stability scaffold, the checked Hopf-derived `π₂(S²)` comparison, and `π₁(S¹) ≅ ℤ`. |
| 35 | Final theorem `pi_3(S^2) ~= Z` | MISSING | Assembled from stubs locally | `src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md` | The final module is a short composition, but remains mathematically unfinished until Hopf and stability scaffolds close. |

Library inventory counts at project start: `EXISTS = 24`, `MISSING = 11`.

## Searches run

Representative searches used to classify the initial library inventory:

```sh
rg --files src | rg 'homotopy-groups|spheres|circle|universal-cover-circle'
rg --files src | rg 'suspensions-of-types|pushouts|joins-of-types|joins-of-maps'
rg --files src | rg 'concrete-groups|homomorphisms-groups|group-of-integers'
rg --files src | rg 'connected-types|connected-maps|truncated-types|set-truncations'
rg -n 'Hopf|hopf|Freudenthal|freudenthal|long exact|fiber sequence|exact sequence|PinSn' src
```

The last search found only prose mentions in agda-unimath modules during the
initial inventory, not formal Hopf/Freudenthal/LES/PinSn modules. Local
progress since then is recorded in the `Local status` column and in the status
report.

A shallow Coq-HoTT clone was searched separately for comparative references.
The findings are recorded above and should be treated as proof guidance, not
port targets.

## New agda-unimath additions needed

Prefer new leaf modules under `src/synthetic-homotopy-theory/` rather than
extending foundational modules until absolutely necessary.

Likely new modules:

- `src/synthetic-homotopy-theory/fiber-sequences.lagda.md`
- `src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md`
- `src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md`
- `src/synthetic-homotopy-theory/underlying-groups-concrete-homotopy-groups.lagda.md`,
  if a separate one-concept bridge module is needed to compare concrete
  homotopy groups with set-truncated loop spaces.
- `src/synthetic-homotopy-theory/higher-homotopy-groups-truncated-types.lagda.md`
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
   segment needed for the Hopf application first, then bridge the existing
   set-truncated pointed-set exactness to ordinary group exactness of concrete
   homotopy groups. The natural comparison target is the underlying set of
   `concrete-homotopy-group n X` against the set truncation of the next
   iterated loop space. Do not route adjacent exactness through a claim that
   the concrete homotopy-group classifying maps form fiber sequences: that
   would impose short-exact-style information, while the long exact sequence
   only gives exactness at the middle group of each adjacent triple. For the
   fibration-boundary part, prioritize direct shifted connecting fiber sequences
   where they match the public iterated-loop indexing. The Hopf `π₃` segment is
   now handled this way, and the arbitrary-index public fibration-boundary
   exactness theorem is checked by transporting the direct `Ω^n(Ω X)` theorem
   through clean reassociation comparisons between `Ω^n(Ω X)` and
   `Ω^(n+1) X`, including the induced maps. Use Coq-HoTT
   `ExactSequence.v` only for decomposition guidance.

5. **Develop the Hopf construction and Hopf fibration.** The circle and
   1-sphere H-space structures are now checked, including equivalence proofs
   for all left and right translations and the Hopf shear equivalence on
   `S¹ × S¹`, as are the generic Hopf map and its `S^1` specialization. The
   Hopf-family and first total-space comparison layers are also checked: the
   family over `S²` classified by left multiplication on `S¹` and its
   projection fiber sequence with fiber `S¹`, the flattening-lemma pushout for
   the actual family total space, the proof that `S¹ * S¹` is a pushout of the
   explicit flattened Hopf-family descent span, `Fin 2 * X ≃ suspension X`,
   `join-power (succ n) (Fin 2) ≃ sphere n`, functoriality of joins under
   equivalences, commutativity of joins, and the bridge from `S^1 * S^1` to
   `join-power 2 (Fin 2) * join-power 2 (Fin 2)`. Next, compare the
   family-induced flattened span with the explicit flattened descent span,
   prove the associativity/join-power multiplication comparison from that join
   to `join-power 4 (Fin 2)`, then use
   `join-power 4 (Fin 2) ≃ S^3` to package the total-space equivalence with
   `S^3` and attack the geometric fiber identification. Use Coq-HoTT
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
