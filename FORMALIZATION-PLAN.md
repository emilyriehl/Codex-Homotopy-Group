# Formalization plan: pi_3(S^2) = Z

This is a planning artifact only. It does not add proofs, postulates, or
modules under `src/`. It was originally written before the local proof route was
completed; the current proof state is summarized here and in
[`STATUS-REPORT.md`](STATUS-REPORT.md).

## Current status

As of 2026-06-28, the local formalization of the target theorem is checked and
unconditional. The exported theorem is
`iso-third-homotopy-group-sphere-2-ℤ` in
[`src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md`](src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md).
No proof obligations remain for the local route. Remaining work is
upstream-facing: module extraction, naming review, prose polish, and deciding
which general components should be proposed to agda-unimath proper.

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

This target signature is now checked in the final theorem module, with index `2`
for the ordinary third homotopy group.

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
| 26 | Long exact sequence of homotopy groups | MISSING | Done locally; upstream extraction review remains | `src/structured-types/long-exact-sequences-pointed-sets.lagda.md`, `src/synthetic-homotopy-theory/set-truncated-long-exact-sequences-fiber-sequences.lagda.md`, `src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups-fiber-sequences.lagda.md`, `src/synthetic-homotopy-theory/abelian-long-exact-sequences-homotopy-groups-fiber-sequences.lagda.md`, `src/synthetic-homotopy-theory/pointed-set-tail-long-exact-sequences-fiber-sequences.lagda.md`; Coq-HoTT `ExactSequence.v` as decomposition guide only | The local LES surface is checked and library-quality: it has a generic pointed-set display, derived adjacent exact triples, the set-truncated fiber-sequence instance, the canonical-boundary group-level package, the abelian-range package, and the pointed-set tail. Remaining LES work is namespace/naming/extraction review, recorded in `LES-STATUS.md`. |
| 27 | Exactness-to-isomorphism lemma with zero endpoints | MISSING | Done locally | `src/group-theory/isomorphisms-from-exact-sequences-groups.lagda.md` | Used to extract Hopf LES comparison isomorphisms. |
| 28 | Hopf construction for connected H-spaces | MISSING | Done locally for the needed `S¹` route | `src/synthetic-homotopy-theory/hopf-construction.lagda.md`, `src/synthetic-homotopy-theory/hopf-construction-circle.lagda.md`, `src/synthetic-homotopy-theory/hopf-construction-fiber-sequence.lagda.md`; HoTT book `sec:hopf` | The generic Hopf construction, the `S¹` specialization, and the source fiber sequence are checked; the project uses the Hopf-family route to identify the total space with `S³`. |
| 29 | Circle as connected H-space | MISSING | Done locally | `src/synthetic-homotopy-theory/h-space-structure-circle.lagda.md`; `synthetic-homotopy-theory.circle` | The local module packages `𝕊¹-H-Space` and the transported `sphere-1-H-Space`, proves that left and right translations on both are equivalences, and packages the Hopf shear equivalence `(x , y) ↦ (y , x · y)` on `S¹ × S¹`; circle connectedness is supplied by the library circle module. |
| 30 | Hopf fibration `S^1 -> S^3 -> S^2` and total-space equivalence | MISSING | Done locally | `src/synthetic-homotopy-theory/hopf-fiber-sequence.lagda.md`, `src/synthetic-homotopy-theory/hopf-family-circle.lagda.md`, `src/synthetic-homotopy-theory/spheres-as-join-powers.lagda.md`, `src/synthetic-homotopy-theory/type-arithmetic-joins-of-types.lagda.md`; HoTT book `thm:hopf-fibration` | The Hopf family over `S²`, total-space comparison with `S¹ * S¹`, join-power comparison with `S³`, pointed total-space equivalence, and packaged fiber sequence `S¹ ->* S³ ->* S²` are checked. |
| 31 | Higher homotopy groups of `S^1` vanish | MISSING | Done locally | `src/synthetic-homotopy-theory/homotopy-groups-circle.lagda.md`; HoTT book `cor:pi1s1` | Positive concrete homotopy groups of the circle and 1-sphere are trivial, now including ordinary group-level triviality wrappers. |
| 32 | Freudenthal suspension theorem | MISSING | Done locally | `src/synthetic-homotopy-theory/freudenthal-suspension-theorem.lagda.md`, `src/synthetic-homotopy-theory/blakers-massey-span-pushouts.lagda.md`; HoTT book `thm:freudenthal`; Coq-HoTT `BlakersMassey.v` as decomposition guide | The checked generalized Blakers-Massey span-pushout theorem specializes to the suspension span `unit <- A -> unit`, yielding the reusable theorem `is-connected-map-Freudenthal-suspension-Blakers-Massey`. |
| 33 | Stability of homotopy groups of spheres | MISSING | Done locally | `src/synthetic-homotopy-theory/stability-third-homotopy-group-sphere-3.lagda.md`, `src/synthetic-homotopy-theory/stability-diagonal-homotopy-groups-spheres.lagda.md`; HoTT book `cor:stability-spheres` | The comparison `π₂(S²) ≅ π₃(S³)` and the general diagonal stabilization comparisons `πₙ₊₂(Sⁿ⁺²) ≅ πₙ₊₃(Sⁿ⁺³)` are checked from Freudenthal/Blakers-Massey. |
| 34 | Diagonal theorem `pi_n(S^n) ~= Z` | MISSING | Done locally for positive spheres | `src/synthetic-homotopy-theory/diagonal-homotopy-groups-spheres.lagda.md`, `src/synthetic-homotopy-theory/third-homotopy-group-sphere-3.lagda.md`; HoTT book `thm:pinsn` | The checked diagonal module proves `πₙ₊₁(Sⁿ⁺¹) ≅ ℤ`; the low-dimensional `π₃(S³) ≅ ℤ` theorem remains as a direct composite through this route's ingredients. |
| 35 | Final theorem `pi_3(S^2) ~= Z` | MISSING | Done locally | `src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md` | The final theorem is checked unconditionally as `iso-third-homotopy-group-sphere-2-ℤ`. |

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

## Upstream extraction candidates

The local route is checked. Upstream work should be organized as reviewable
batches, keeping high-fan-in files stable unless maintainers request otherwise:

1. **LES and exactness packages.** Extract the generic pointed-set exactness
   layer, the pointed-set LES display, the set-truncated fiber-sequence
   instance, the group-level and abelian LES packages, and the pointed-set tail.
   The detailed naming and extraction review is in `LES-STATUS.md`.
2. **Hopf fibration packages.** Extract the circle H-space, Hopf construction,
   Hopf family, total-space comparison, and packaged Hopf fiber sequence in
   small subject files.
3. **Freudenthal and Blakers-Massey packages.** Extract the span-pushout
   Blakers-Massey theorem, the suspension-span specialization, and the
   Freudenthal suspension theorem.
4. **Sphere stability and diagonal theorem packages.** Extract diagonal
   stability, the positive diagonal theorem, and the final low-dimensional
   corollaries.

Supporting algebra and foundation bridge modules such as
`group-theory.isomorphisms-from-exact-sequences-groups`,
`group-theory.trivial-underlying-groups-concrete-groups`, and the concrete
homotopy-group underlying-type comparisons should be reviewed as separate
dependencies rather than folded into the top-level theorem files.

High-fan-in/cache-sensitive targets remain:

- `src/foundation/` and `src/foundation-core/`: avoid edits unless a reusable
  truncation/connectedness lemma clearly belongs there.
- `src/synthetic-homotopy-theory.lagda.md` and other umbrella/import modules:
  add imports only after each leaf module typechecks and the extraction shape is
  agreed.
- Existing central modules such as
  `synthetic-homotopy-theory.homotopy-groups`,
  `synthetic-homotopy-theory.spheres`, and
  `synthetic-homotopy-theory.suspensions-of-types`: avoid changing their public
  APIs unless maintainers request it.

## Tractability and risks after completion

The local theorem infrastructure is no longer the main risk: the final route
checks with no local holes, postulates, or weakening pragmas. The remaining risks
are upstream integration risks:

- **Review size:** the development spans LES, Hopf, Blakers-Massey,
  Freudenthal, stability, and diagonal homotopy groups. It should be proposed in
  small dependency-ordered batches, not as one large patch.
- **Naming and namespace fit:** local names are descriptive and checked, but
  maintainers may prefer different module boundaries or some migration facades.
- **Proof readability:** several proof-provider modules are necessarily
  technical. Public packages should keep structural statements prominent and
  route-specific transports hidden.
- **Cache risk:** touching umbrella or central modules too early will invalidate
  large parts of the library.

## Completed route and remaining upstream order

The original proof plan has been carried out locally:

1. The final theorem signature was fixed using the
   `concrete-homotopy-group 2` indexing convention.
2. Circle and 1-sphere homotopy-group facts were packaged, including
   `π₁(S¹) ≅ ℤ` and vanishing of positive higher homotopy groups of `S¹`.
3. Pointed fiber sequences, boundary maps, and induced maps on homotopy groups
   were formalized.
4. The LES was built through structural fiber-sequence packages, set-truncated
   exactness, and transport to concrete group exactness.
5. The Hopf construction and Hopf fibration `S¹ ->* S³ ->* S²` were checked.
6. The Hopf LES comparisons `π₂(S²) ≅ π₁(S¹)` and `π₃(S³) ≅ π₃(S²)` were
   extracted.
7. Blakers-Massey, Freudenthal, sphere stability, and the positive diagonal
   theorem were checked.
8. The final theorem was assembled as a short composition ending in
   `iso-third-homotopy-group-sphere-2-ℤ`.

The remaining work is upstream preparation:

1. Apply the LES naming/extraction review in `LES-STATUS.md`.
2. Do the same review for Blakers-Massey/Freudenthal and the sphere-stability
   layers.
3. Run the relevant `./check.sh <file>` commands after any extraction or rename.
4. Before any PR, run the upstream pre-commit checks and get human review that
   the literate exposition reads like normal agda-unimath documentation.
