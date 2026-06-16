# Formalization status report

This report tracks the autoformalized Agda code in this repository against
[the formalization plan](FORMALIZATION-PLAN.md) for `pi_3(S^2) = Z`.

Update this file whenever significant progress is made, for example when a
new theorem is proved, an important definition is formalized, a planned module
is added, or a major blocked item is resolved or re-scoped.

Last updated: 2026-06-15.

## Current summary

The repository currently contains early infrastructure for the planned
calculation:

- General pointed fiber sequences have been formalized, and the set
  truncations of the first four adjacent triples in any packaged pointed fiber
  sequence, `F ->* E ->* B`, `Ω B ->* F ->* E`,
  `Ω E ->* Ω B ->* F`, and `Ω F ->* Ω E ->* Ω B`, are now proved
  exact as sequences of pointed sets. These proofs are bundled as an initial
  set-truncated long-exact-sequence segment.
- Functoriality for iterated loop spaces and concrete homotopy groups has been
  added.
- Boundary maps associated to a fiber sequence have been formalized.
- The first HoTT Book Lemma 8.4.4-style fiber-of-the-fiber identification has
  been formalized: for a pointed map `g : E ->* B`, the fiber of
  `fiber g ->* E` is pointed equivalent to `Ω B`, and therefore
  `Ω B ->* fiber g ->* E` is packaged as a pointed fiber sequence.
- Ordinary group exactness has been defined.
- A fiber sequence of concrete-group classifying maps has been shown to imply
  ordinary exactness of the induced underlying group homomorphisms.
- Pointed sets and pointed maps of pointed sets have been separated into
  their own structured-types module. Exactness of pointed-set maps and the
  HoTT-book theorem that the set truncation of a canonical pointed fiber
  sequence is exact have been formalized. The canonical theorem has now been
  lifted to any packaged pointed fiber sequence `F ->* E ->* B` by comparison
  with the canonical fiber of `E ->* B`. The packaged boundary segment
  `Ω B ->* F ->* E`, the packaged loop-boundary segment
  `Ω E ->* Ω B ->* F`, and the looped packaged segment
  `Ω F ->* Ω E ->* Ω B` are also exact after set truncation. The code
  additionally includes the canonical adjacent triples
  `Ω B ->* fiber g ->* E`, `Ω E ->* Ω B ->* fiber g`, and
  `Ω² B ->* Ω (fiber g) ->* Ω E`, by comparison with canonical fiber
  sequences, and packages the first four exactness proofs into a single initial
  segment.
- The circle facts needed for vanishing higher homotopy groups have been
  formalized: the loop space of the circle and the 1-sphere is equivalent to
  the integers, the circle and 1-sphere are 1-types, and positive concrete
  homotopy groups of 1-types are trivial.
- The ordinary underlying type of `concrete-homotopy-group n A` has been
  identified with `type-homotopy-group (succ-ℕ n) A`, i.e. with the set
  truncation of the next iterated loop space. This removes the indexing and
  truncation mismatch from the group-level LES bridge.
- Foundation and loop-space computation lemmas now relate subtype path
  extensionality, automorphism-infinity path computations, `map-Ω` on
  classifying maps, and naturality of effectiveness of truncation. Together
  these prove the forward and inverse underlying-map coherence squares for
  concrete groups coming from pointed types. Homotopy-group wrapper proofs are
  recorded as target interfaces but not yet kept as named theorems, because the
  direct inverse wrapper caused expensive checking.
- The group-level LES bridge has been split one level lower. The file
  `exactness-homotopy-groups-fiber-sequences` now has no local holes or
  `--allow-unsolved-metas`; it composes separate targets for set-truncated
  iterated LES exactness and for transporting that pointed-set exactness to
  ordinary group exactness. The set-truncated target already proves the `n = 0`
  total-space iterated-loop case from the existing looped packaged exactness.

The final theorem `pi_3(S^2) = Z` is not yet proved. The top-level Agda file
now assembles the final isomorphism through two next-level files that themselves
compose one level further down. The Hopf comparison `π₃(S³) ≅ π₃(S²)` now has
its algebraic exactness-to-isomorphism step, trivial concrete-to-group bridge,
and Hopf LES packaging proved. The attempted route through fiber sequences of
concrete homotopy-group classifying maps has been rejected as too strong in
general. The current group-level LES bridge is therefore explicitly reduced to
comparing set-truncated adjacent exactness with ordinary group exactness of
concrete homotopy groups, and now delegates to four one-level-lower obligations: two set-truncated iterated exactness stubs and two group exactness transport stubs. The
`π₃(S³) ≅ ℤ` calculation is reduced to a stability comparison
`π₂(S²) ≅ π₃(S³)`, a Hopf base computation `π₂(S²) ≅ π₁(S¹)`, and the
group-level circle calculation `π₁(S¹) ≅ ℤ`. These are still intentionally
unfinished scaffolds.

## Implemented Agda code

| Area | File | Current status |
|---|---|---|
| Pointed fiber sequences | [`src/structured-types/fiber-sequences.lagda.md`](src/structured-types/fiber-sequences.lagda.md) | Defines the canonical pointed fiber inclusion, `is-fiber-sequence-Pointed-Type`, packaged `fiber-sequence-Pointed-Type`, accessors, null composite maps, and the canonical fiber sequence of a pointed map. |
| Iterated loop functoriality | [`src/synthetic-homotopy-theory/functoriality-iterated-loop-spaces.lagda.md`](src/synthetic-homotopy-theory/functoriality-iterated-loop-spaces.lagda.md) | Defines the pointed map induced by a pointed map on iterated loop spaces. |
| Homotopy automorphism functoriality | [`src/group-theory/functoriality-homotopy-automorphism-groups.lagda.md`](src/group-theory/functoriality-homotopy-automorphism-groups.lagda.md) | Defines classifying pointed maps and induced homomorphisms of concrete homotopy automorphism groups. |
| Homotopy group functoriality | [`src/synthetic-homotopy-theory/functoriality-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/functoriality-homotopy-groups.lagda.md) | Defines `hom-concrete-homotopy-group`, the homomorphism induced by a pointed map on concrete homotopy groups. |
| Classifying fiber-sequence route for homotopy groups | [`src/synthetic-homotopy-theory/classifying-fiber-sequences-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/classifying-fiber-sequences-homotopy-groups.lagda.md) | Records why the classifying-map fiber-sequence route is too strong for adjacent LES exactness and deliberately contains no theorem statements. |
| Exactness of group homomorphisms | [`src/group-theory/exact-sequences-groups.lagda.md`](src/group-theory/exact-sequences-groups.lagda.md) | Defines `is-exact-hom-Group` and proves `is-exact-is-fiber-sequence-hom-Concrete-Group`, the forward implication from a fiber sequence of concrete-group classifying maps to exactness of the induced ordinary group homomorphisms. |
| Pointed sets | [`src/structured-types/pointed-sets.lagda.md`](src/structured-types/pointed-sets.lagda.md) | Defines pointed sets, pointed maps of pointed sets, and set truncation as a pointed set and as a pointed map. |
| Exactness of pointed sets | [`src/structured-types/exact-sequences-pointed-sets.lagda.md`](src/structured-types/exact-sequences-pointed-sets.lagda.md) | Defines images, kernels, exactness of pointed-set maps, and proves that the set truncation of the canonical fiber sequence `fiber g -> E -> B` is exact. |
| Boundary maps and LES exactness steps | [`src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md) | Defines the boundary pointed map, induced maps on homotopy groups of a fiber sequence, recursive boundary pointed maps, and boundary homomorphisms. It proves the first fiber-of-the-fiber identification, packages `Ω B ->* fiber g ->* E` as a pointed fiber sequence, proves pointed-set exactness for canonical and packaged `F ->* E ->* B` fiber sequences, proves pointed-set exactness for the packaged boundary segment `Ω B ->* F ->* E`, proves pointed-set exactness for the packaged loop-boundary segment `Ω E ->* Ω B ->* F`, proves pointed-set exactness for the looped packaged segment `Ω F ->* Ω E ->* Ω B`, proves pointed-set exactness for the canonical adjacent triples `Ω B ->* fiber g ->* E`, `Ω E ->* Ω B ->* fiber g`, and `Ω² B ->* Ω (fiber g) ->* Ω E`, and bundles the first four packaged exactness proofs as an initial set-truncated LES segment. These are steps toward, not yet the full proof of, Theorem 8.4.6 of the HoTT book. |
| Higher homotopy groups of 1-types | [`src/synthetic-homotopy-theory/higher-homotopy-groups-truncated-types.lagda.md`](src/synthetic-homotopy-theory/higher-homotopy-groups-truncated-types.lagda.md) | Proves that positive concrete homotopy groups of pointed 1-types are trivial. |
| Circle and 1-sphere homotopy facts | [`src/synthetic-homotopy-theory/homotopy-groups-circle.lagda.md`](src/synthetic-homotopy-theory/homotopy-groups-circle.lagda.md) | Proves the loop-space equivalences for the circle and 1-sphere, the 1-type facts, and triviality of their positive concrete homotopy groups. |
| Exactness-to-isomorphism algebra | [`src/group-theory/isomorphisms-from-exact-sequences-groups.lagda.md`](src/group-theory/isomorphisms-from-exact-sequences-groups.lagda.md) | Proves that two adjacent exact group triples with trivial outer groups make the middle homomorphism an isomorphism. |
| Trivial concrete-to-group bridge | [`src/group-theory/trivial-underlying-groups-concrete-groups.lagda.md`](src/group-theory/trivial-underlying-groups-concrete-groups.lagda.md) | Proves the bridge from `is-trivial-Concrete-Group G` to triviality of `group-Concrete-Group G`. |
| Underlying types of concrete homotopy groups | [`src/synthetic-homotopy-theory/underlying-groups-concrete-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/underlying-groups-concrete-homotopy-groups.lagda.md) | Proves that the ordinary underlying type of `concrete-homotopy-group n A` is equivalent to `type-homotopy-group (succ-ℕ n) A`, using connected-component extensionality and effectiveness of truncation, and names the induced forward and inverse maps. |
| Underlying maps of concrete homotopy groups | [`src/synthetic-homotopy-theory/underlying-maps-concrete-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/underlying-maps-concrete-homotopy-groups.lagda.md) | Defines the ordinary underlying map of a concrete homotopy-group homomorphism and its set-truncated loop comparison squares. The forward and inverse coherence squares are proved for concrete groups coming from pointed types; the homotopy-group square types are kept as interfaces while named wrapper proofs are deferred until they check cheaply. |
| Computing identity types of subtypes | [`src/foundation/computing-identity-types-subtypes.lagda.md`](src/foundation/computing-identity-types-subtypes.lagda.md) | Proves the computation rule for the first component of subtype extensionality, used to control connected-component path calculations. |
| Computing identity types of automorphism-infinity groups | [`src/higher-group-theory/computing-identity-types-automorphism-infinity-groups.lagda.md`](src/higher-group-theory/computing-identity-types-automorphism-infinity-groups.lagda.md) | Proves section, concatenation, inverse, and loop-transport computation rules for paths in automorphism-infinity classifying types. |
| Loop-space classifying-map computations | [`src/group-theory/computing-loop-space-functoriality-homotopy-automorphism-groups.lagda.md`](src/group-theory/computing-loop-space-functoriality-homotopy-automorphism-groups.lagda.md) | Computes `map-Ω` on the classifying pointed map of connected components after automorphism-infinity extensionality. |
| Loop-space naturality of effectiveness | [`src/synthetic-homotopy-theory/naturality-effectiveness-loop-spaces.lagda.md`](src/synthetic-homotopy-theory/naturality-effectiveness-loop-spaces.lagda.md) | Transports naturality of effectiveness of truncation into the based-loop form required by the inverse underlying-map square. |
| Naturality of effectiveness of truncation | [`src/foundation/naturality-effectiveness-truncation.lagda.md`](src/foundation/naturality-effectiveness-truncation.lagda.md) | Proves that effectiveness on a unit-truncated path computes to `ap unit-trunc`, and that effectiveness of truncation is natural in maps, up to the naturality paths of the truncation unit. This is the reusable foundation lemma needed by the underlying-map comparison for concrete homotopy groups. |
| Set-truncated iterated LES exactness | [`src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md`](src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md) | Defines the set-truncated maps on `Ω Ω^n F`, `Ω Ω^n E`, and `Ω Ω^n B`, plus the iterated fibration-boundary map. It proves the `n = 0` total-space case from the existing looped packaged exactness and records the remaining iterated set-level exactness stubs. |
| Group exactness transport for homotopy groups | [`src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md`](src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md) | Records the two transport targets from set-truncated iterated exactness to ordinary group exactness of concrete homotopy groups. These are the image/kernel transport obligations for the LES bridge. |
| Group exactness of homotopy groups | [`src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md`](src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md) | Records the two adjacent group-level exactness statements needed by the Hopf comparison and proves them by composing the new set-truncated iterated LES target with the new group-exactness transport target. This file has no local holes and no `--allow-unsolved-metas`; the unfinished work is isolated in the two lower-level target files. |
| Hopf fiber sequence | [`src/synthetic-homotopy-theory/hopf-fiber-sequence.lagda.md`](src/synthetic-homotopy-theory/hopf-fiber-sequence.lagda.md) | Records the unfinished packaged fiber sequence with fiber `S¹`, total space `S³`, and base `S²` fixed definitionally. |
| Hopf LES comparison for third homotopy groups | [`src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md) | Builds the Hopf comparison isomorphism from the Hopf fibration homomorphism, two supplied group exactness hypotheses, and the two trivial endpoint hypotheses. |
| Hopf comparison for third homotopy groups | [`src/synthetic-homotopy-theory/hopf-fibration-third-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/hopf-fibration-third-homotopy-groups.lagda.md) | Delegates `π₃(S³) ≅ π₃(S²)` to the Hopf LES comparison scaffold and has no direct proof hole. |
| Stability comparison for `π₃(S³)` | [`src/synthetic-homotopy-theory/stability-third-homotopy-group-sphere-3.lagda.md`](src/synthetic-homotopy-theory/stability-third-homotopy-group-sphere-3.lagda.md) | Records the unfinished stability comparison `π₂(S²) ≅ π₃(S³)`. |
| Second homotopy group of `S²` | [`src/synthetic-homotopy-theory/second-homotopy-group-sphere-2.lagda.md`](src/synthetic-homotopy-theory/second-homotopy-group-sphere-2.lagda.md) | Records the unfinished Hopf-derived comparison `π₂(S²) ≅ π₁(S¹)`. |
| Fundamental group of `S¹` | [`src/synthetic-homotopy-theory/fundamental-group-sphere-1.lagda.md`](src/synthetic-homotopy-theory/fundamental-group-sphere-1.lagda.md) | Records the unfinished group-level packaging `π₁(S¹) ≅ ℤ`. |
| Third homotopy group of the 3-sphere | [`src/synthetic-homotopy-theory/third-homotopy-group-sphere-3.lagda.md`](src/synthetic-homotopy-theory/third-homotopy-group-sphere-3.lagda.md) | Delegates `π₃(S³) ≅ ℤ` to the stability comparison, the `π₂(S²) ≅ π₁(S¹)` comparison, and the `π₁(S¹) ≅ ℤ` scaffold, and has no direct proof hole. |
| Final theorem target | [`src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md`](src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md) | Records the pinned top-level statement `π₃(S²) ≅ ℤ` and proves it formally from the inverse Hopf-comparison stub and the `π₃(S³) ≅ ℤ` stub. The proof is therefore structurally assembled but depends on unfinished imported stubs. |

## Status against the formalization plan

| Plan item | Status | Notes |
|---|---|---|
| General pointed fiber sequences | Done | Implemented in [`src/structured-types/fiber-sequences.lagda.md`](src/structured-types/fiber-sequences.lagda.md). |
| Induced maps on homotopy groups | Done | Implemented via iterated loop functoriality and concrete homotopy group functoriality. |
| Long exact sequence of homotopy groups | Partial | Boundary maps, induced homomorphisms, pointed-set exactness, exactness of the set truncation of canonical and packaged `F ->* E ->* B` triples, exactness of the packaged boundary triple `Ω B ->* F ->* E`, exactness of the packaged loop-boundary triple `Ω E ->* Ω B ->* F`, exactness of the looped packaged triple `Ω F ->* Ω E ->* Ω B`, the first fiber-of-the-fiber identification `Ω B ≃* fiber (fiber g -> E)`, pointed-set exactness of the canonical triples `Ω B ->* fiber g ->* E`, `Ω E ->* Ω B ->* fiber g`, and `Ω² B ->* Ω (fiber g) ->* Ω E`, and a bundled initial four-triple set-truncated LES segment are formalized. The bridge is now split into set-truncated iterated exactness targets and group-exactness transport targets; the original group-level bridge module is a clean composition through those targets. The classifying-map fiber-sequence route is recorded as too strong in general. |
| Exactness-to-isomorphism with zero endpoints | Done | Proved in [`src/group-theory/isomorphisms-from-exact-sequences-groups.lagda.md`](src/group-theory/isomorphisms-from-exact-sequences-groups.lagda.md). |
| Higher homotopy groups of the circle vanish | Mostly done | Positive concrete homotopy groups of the circle and 1-sphere are trivial. Further packaging may be needed for the exact Hopf LES endpoints. |
| Loop space of the circle is the integers | Partial | The loop-space equivalence is formalized. A group-level final packaging against the target theorem may still be needed. |
| Hopf construction and Hopf fibration | Stubbed | The packaged Hopf fiber sequence target `S^1 -> S^3 -> S^2` is recorded, but the construction, maps, and fiber-sequence proof remain holes. |
| Hopf LES consequence `pi_3(S^3) = pi_3(S^2)` | Partially proved | The exactness-to-isomorphism extraction and Hopf LES packaging are proved. The comparison still depends on the Hopf fiber sequence, the circle endpoint triviality inputs, and the four lower-level LES bridge obligations. |
| Freudenthal suspension theorem | Not started | Still a major missing theorem. |
| Stability of homotopy groups of spheres | Instance stubbed | The needed comparison `π₂(S²) ≅ π₃(S³)` is recorded as an unfinished theorem depending on Freudenthal/stability. |
| Diagonal theorem `pi_n(S^n) = Z` | Reduced to lower stubs | The `n = 3` file now composes the stability, `π₂(S²) ≅ π₁(S¹)`, and `π₁(S¹) ≅ ℤ` scaffolds. The general theorem remains unproved. |
| Final theorem `pi_3(S^2) = Z` | Assembled from stubs | The target statement in [`src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md`](src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md) is now a formal composition of the two next-level stubs. It has no direct proof hole but remains mathematically unfinished until those imported stubs are proved. |

## Remaining tasks

1. Fill the four lower-level LES bridge obligations exposed by the new split:
   recursive set-truncated iterated exactness for the total-space triples,
   set-truncated iterated exactness for the fibration-boundary triples, and the
   two image/kernel transport proofs from set-truncated pointed-set exactness to
   ordinary group exactness. Named homotopy-group wrapper lemmas should be
   avoided unless they check cheaply; both variable wrappers and fixed-index
   wrappers at `1` and `2` caused expensive Agda normalization.
2. Formalize the Hopf fiber sequence `S^1 -> S^3 -> S^2`, including the actual
   pointed maps and the fiber-sequence proof.
3. Package the group-level computation `π₁(S¹) ≅ ℤ` from the existing loop-space
   equivalence of the 1-sphere with the integers.
4. Fill the Hopf-derived comparison `π₂(S²) ≅ π₁(S¹)`.
5. Prove the stability comparison `π₂(S²) ≅ π₃(S³)` from Freudenthal and sphere
   stability.
6. Recheck `π₃(S³) ≅ ℤ` and `π₃(S²) ≅ ℤ` after their imported lower stubs are
   proved; their proof bodies should remain short compositions.

## Current verification

The following refactor-relevant Agda modules were checked on 2026-06-10:

```sh
./check.sh src/structured-types/pointed-sets.lagda.md
./check.sh src/structured-types/exact-sequences-pointed-sets.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

All passed after adding pointed-set exactness for arbitrary packaged fiber
sequences, the packaged boundary segment `Ω B ->* F ->* E`, the packaged
loop-boundary segment `Ω E ->* Ω B ->* F`, the looped packaged segment
`Ω F ->* Ω E ->* Ω B`, the canonical adjacent exactness proofs for
`Ω B ->* fiber g ->* E`, `Ω E ->* Ω B ->* fiber g`, and
`Ω² B ->* Ω (fiber g) ->* Ω E`, and the bundled initial four-triple
set-truncated LES segment. A source search found no explicit Agda holes in
project-owned `.lagda.md` files under `src/` at that time.

On 2026-06-10, the then-current top-level stub modules were checked after
assembling the final proof from the two next-level stubs:

```sh
./check.sh src/synthetic-homotopy-theory/hopf-fibration-third-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/third-homotopy-group-sphere-3.lagda.md
./check.sh src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md
```

At that stage, these commands passed because the two next-level stub modules
were explicitly marked with `--allow-unsolved-metas`. That was a development
scaffold, not a completed proof. The 2026-06-11 scaffold below pushes those
direct holes one level lower.

On 2026-06-11, the one-level-lower scaffold modules were checked with:

```sh
./check.sh src/group-theory/isomorphisms-from-exact-sequences-groups.lagda.md
./check.sh src/group-theory/trivial-underlying-groups-concrete-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-fiber-sequence.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/stability-third-homotopy-group-sphere-3.lagda.md
./check.sh src/synthetic-homotopy-theory/second-homotopy-group-sphere-2.lagda.md
./check.sh src/synthetic-homotopy-theory/fundamental-group-sphere-1.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-fibration-third-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/third-homotopy-group-sphere-3.lagda.md
./check.sh src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md
```

All passed. The new lower-level modules are intentionally marked with
`--allow-unsolved-metas`, so this verifies the scaffold shape rather than the
completed proofs. The previous direct holes in the Hopf comparison and
`π₃(S³) ≅ ℤ` files have been pushed one level lower.

Later on 2026-06-11, the first three lower-level holes were filled and checked:

```sh
./check.sh src/group-theory/trivial-underlying-groups-concrete-groups.lagda.md
./check.sh src/group-theory/isomorphisms-from-exact-sequences-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
git diff --check
```

All passed. These three modules no longer use `--allow-unsolved-metas`.

Later on 2026-06-11, the classifying-map fiber-sequence route was rejected as
too strong in general and the group-level exactness file was restored as the
direct bridge target. The corrected modules were checked with:

```sh
./check.sh src/synthetic-homotopy-theory/classifying-fiber-sequences-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
rg -n '\{!!\}|allow-unsolved-metas' src/synthetic-homotopy-theory src/group-theory
git diff --check
```

The two Agda checks passed, the source search confirmed the intended hole
locations, and `git diff --check` passed. The classifying route module contains
no theorem statements and no holes. The exactness file intentionally uses
`--allow-unsolved-metas` and contains the two remaining group-level LES bridge
holes. The other remaining explicit holes are in the Hopf fiber sequence, the circle group-isomorphism
packaging, the Hopf-derived `π₂(S²) ≅ π₁(S¹)` comparison, and the stability
comparison `π₂(S²) ≅ π₃(S³)`.


Later on 2026-06-11, the underlying-type comparison for concrete homotopy
groups was added and checked with:

```sh
./check.sh src/synthetic-homotopy-theory/underlying-groups-concrete-homotopy-groups.lagda.md
```

The check passed. This module has no holes and proves the equivalence from the
ordinary underlying type of `concrete-homotopy-group n A` to
`type-homotopy-group (succ-ℕ n) A`, together with named forward and inverse
maps.

Later on 2026-06-11, the underlying-map comparison target for concrete
homotopy groups was added and checked with:

```sh
./check.sh src/synthetic-homotopy-theory/underlying-maps-concrete-homotopy-groups.lagda.md
rg -n "\{!!\}|allow-unsolved-metas|postulate" src/synthetic-homotopy-theory/underlying-maps-concrete-homotopy-groups.lagda.md
```

The Agda check passed, and the source search found no holes, postulates, or
`--allow-unsolved-metas` in the new module. The module records the ordinary
underlying map of a concrete homotopy-group homomorphism, the corresponding
set-truncated loop map, and the forward and inverse coherence-square target
types. An attempted proof of the inverse square reduced by set-truncation
induction to the generator loop case, but `refl` failed: the concrete-group
side maps through the classifying map and basepoint transport, while the
set-truncated loop side maps through effectiveness of truncation. The next
missing lemma is therefore a naturality/coherence theorem for this
effectiveness-extensionality comparison, not a definitional equality.

Later on 2026-06-13, the inverse comparison map was made more explicit and
rechecked:

```sh
./check.sh src/synthetic-homotopy-theory/underlying-groups-concrete-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/underlying-maps-concrete-homotopy-groups.lagda.md
```

Both checks passed. The pointed-type inverse
`map-inv-underlying-type-concrete-group-Pointed-Type` is now defined directly by
component extensionality and `map-effectiveness-trunc`, and the homotopy-group
inverse wrapper delegates to that explicit map. This gives downstream
naturality goals the right definitional shape without unfolding the inverse of
the composite equivalence. The attempted inverse coherence square is still not
completed: the remaining missing ingredient is a cheap naturality theorem for
effectiveness of truncation under a pointed map, including the basepoint
transport inserted by `map-Ω`. Earlier expanded computations of that theorem
were too expensive for real Agda checking, so the next proof step should isolate
that naturality as a small one-concept lemma before using it in the underlying
map square.


Later on 2026-06-13, a one-concept foundation lemma for naturality of
effectiveness of truncation was added and checked:

```sh
./check.sh src/foundation/naturality-effectiveness-truncation.lagda.md
./check.sh src/synthetic-homotopy-theory/underlying-maps-concrete-homotopy-groups.lagda.md
rg -n '{!!}|allow-unsolved-metas|postulate' src/foundation/naturality-effectiveness-truncation.lagda.md src/synthetic-homotopy-theory/underlying-maps-concrete-homotopy-groups.lagda.md
```

Both Agda checks passed, and the source search found no holes, postulates, or
`--allow-unsolved-metas` in the new lemma or the underlying-map target module.
The new file proves that effectiveness on a unit-truncated path computes to `ap unit-trunc`, and that effectiveness of truncation is natural with respect
to a map `f`, up to the naturality paths of the truncation unit. Applying
component extensionality to the inverse underlying-map square now reduces the
remaining proof to a further computation: how `map-Ω` on the classifying map of
connected components is seen after component extensionality, including the
basepoint transport `tr-type-Ω` introduced by pointed maps.

Later on 2026-06-13, a one-concept loop-space form of the naturality theorem
was added and checked:

```sh
./check.sh src/synthetic-homotopy-theory/naturality-effectiveness-loop-spaces.lagda.md
./check.sh src/synthetic-homotopy-theory/underlying-maps-concrete-homotopy-groups.lagda.md
rg -n "\{!!\}|allow-unsolved-metas|postulate" src/synthetic-homotopy-theory/naturality-effectiveness-loop-spaces.lagda.md src/synthetic-homotopy-theory/underlying-maps-concrete-homotopy-groups.lagda.md
```

Both Agda checks passed, and the source search found no holes, postulates, or
`--allow-unsolved-metas` in the checked files. The new helper proves that after
transporting along the truncation-unit naturality path, the naturality of
effectiveness becomes a based loop equality. An attempted use of this helper in
the inverse underlying-map square exposed the next missing one-concept lemma:
component extensionality for the connected-component subtype must compute the
first component of `map-Ω` on the classifying map to the transported
truncation-effectiveness path. The unfinished expanded proof was removed from
`underlying-maps-concrete-homotopy-groups.lagda.md`, which remains a checked
target-only module.


Later on 2026-06-13, the component-computation and equivalence-cancellation route for the pointed-type underlying-map squares was completed and checked with:

```sh
./check.sh src/foundation/computing-identity-types-subtypes.lagda.md
./check.sh src/higher-group-theory/computing-identity-types-automorphism-infinity-groups.lagda.md
./check.sh src/group-theory/functoriality-homotopy-automorphism-groups.lagda.md
./check.sh src/group-theory/computing-loop-space-functoriality-homotopy-automorphism-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/naturality-effectiveness-loop-spaces.lagda.md
./check.sh src/synthetic-homotopy-theory/underlying-maps-concrete-homotopy-groups.lagda.md
rg -n "\{!!\}|allow-unsolved-metas|postulate" src/foundation/computing-identity-types-subtypes.lagda.md src/higher-group-theory/computing-identity-types-automorphism-infinity-groups.lagda.md src/group-theory/computing-loop-space-functoriality-homotopy-automorphism-groups.lagda.md src/synthetic-homotopy-theory/naturality-effectiveness-loop-spaces.lagda.md src/synthetic-homotopy-theory/underlying-maps-concrete-homotopy-groups.lagda.md
```

The Agda checks passed, and the source search found no holes, postulates, or
`--allow-unsolved-metas` in the checked proof modules. The new computation
lemmas prove the first-component computation for subtype extensionality, path
algebra and transport computations for automorphism-infinity classifying types,
and the `map-Ω` computation for the classifying pointed map of connected
components. These results complete
`naturality-map-inv-underlying-type-concrete-group-Pointed-Type`. The explicit
section and retraction laws for the underlying-type comparison then give
`naturality-map-underlying-type-concrete-group-Pointed-Type` by cancellation. A
direct named homotopy-group wrapper of the inverse theorem was tried, but real
Agda checking became expensive enough that the wrapper was removed; the
homotopy-group square types remain as interfaces, and the checked pointed-type
theorems can still be instantiated manually at
`pointed-map-iterated-loop-space n f` when needed.

Later on 2026-06-15, the group-level LES bridge was split one level lower and
checked with:

```sh
./check.sh src/synthetic-homotopy-theory/underlying-maps-concrete-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
rg -n "{!!}|allow-unsolved-metas|postulate" src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md
git diff --check
```

The Agda checks passed, and `git diff --check` passed. The original
`exactness-homotopy-groups-fiber-sequences` bridge file now has no local holes
and no `--allow-unsolved-metas`; it delegates to two one-concept target files.
The intentional holes are now the recursive set-truncated iterated total-space
exactness step, the set-truncated iterated fibration-boundary exactness step,
and the two image/kernel transport steps from set-truncated exactness to group
exactness. A direct named wrapper for homotopy-group naturality at the fixed
indices `1` and `2` was also tried and removed after real Agda checking stayed
expensive, matching the earlier variable-wrapper failure.
