# Formalization status report

This report tracks the autoformalized Agda code in this repository against
[the formalization plan](FORMALIZATION-PLAN.md) for `pi_3(S^2) = Z`.

Update this file whenever significant progress is made, for example when a
new theorem is proved, an important definition is formalized, a planned module
is added, or a major blocked item is resolved or re-scoped.

Last updated: 2026-06-19.

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
- The low-dimensional sphere-connectivity facts needed for the lower Hopf
  segment have been formalized: `S³` is 2-connected, and therefore the first
  two concrete homotopy groups of `S³` are trivial.
- The concrete fundamental group of the 1-sphere has now been proved
  isomorphic to the additive group of integers. The checked carrier
  equivalence factors through the general concrete-homotopy-group
  underlying-type comparison, removes the redundant set truncation using the
  1-sphere loop-space set structure, proves the universal-cover loop-space
  computation is additive, transfers additivity from the circle to the
  1-sphere, and packages the result as an `iso-Group`.
- The ordinary underlying type of `concrete-homotopy-group n A` has been
  identified with `type-homotopy-group (succ-ℕ n) A`, i.e. with the set
  truncation of the next iterated loop space. This removes the indexing and
  truncation mismatch from the group-level LES bridge.
- Foundation and loop-space computation lemmas now relate subtype path
  extensionality, automorphism-infinity path computations, `map-Ω` on
  classifying maps, and naturality of effectiveness of truncation. Together
  these prove the forward and inverse underlying-map coherence squares for
  concrete groups coming from pointed types. The same layer now also proves
  that the inverse comparison sends the set-truncated base loop to the concrete
  unit, and consequently that the forward comparison sends the concrete unit to
  the set-truncated base loop. It additionally proves that the forward and
  inverse underlying-type comparisons preserve multiplication. The remaining
  additivity step for the loop-space computation `ΩS¹ ≃ ℤ` is now also
  checked via integer loop powers and the universal cover.
- Pointed-set exactness now has a derived mere-preimage/fiber interface. This
  keeps `is-exact-hom-Pointed-Set` as the source theorem while giving the
  group-level bridge a lower-level Coq-HoTT-style map-to-fiber form to consume.
  It also has a checked transport lemma for replacing the second pointed-set
  map by a pointwise equal one, a checked transport lemma for replacing the
  first map by an image-equivalent one, a checked image-invariance lemma for
  compatible middle self-maps, a checked transport lemma for shifted kernels
  along such middle self-maps, and a checked transport lemma for moving
  exactness across an injective comparison of the middle pointed set.
- The group exactness transport file now contains a checked generic transfer
  theorem from pointed-set exactness to ordinary group exactness, parameterized
  by explicit comparison maps, injectivity data, unit compatibility, and
  coherence squares. A pointed-type wrapper instantiates this theorem using the
  checked underlying-map squares. A second pointed-type wrapper handles the
  important trivial-codomain case: when the target group is contractible, the
  second group homomorphism's kernel is automatically full, so canonical
  set-level exactness can be transported without comparing the second maps.
- The group-level LES bridge has been split one level lower. The
  set-truncated iterated exactness file now checks without
  `--allow-unsolved-metas`: it proves the total-space iterated-loop case for
  all `n`, the Coq-HoTT-style canonical shifted boundary case, and a transport
  theorem reducing recursive boundary exactness to a pointwise comparison with
  the canonical shifted boundary. The Hopf fibration-boundary segment now uses
  the checked trivial-codomain transport instead of requiring that comparison.
  The looped boundary/fiber-inclusion segment `Ω² B ->* Ω F ->* Ω E` is also
  checked for packaged fiber sequences by transporting the canonical fiber
  version across the loop of the chosen-fiber equivalence, and it has been
  transported to ordinary group exactness at `π₁(F)`.
  The nontrivial-target fibration-boundary group exactness statement is now
  exposed as a checked wrapper from recursive set-level exactness. The
  remaining general LES bridge is the comparison between the canonical shifted
  boundary and the looped recursive boundary for nontrivial targets.
- The algebraic extraction for the lower Hopf segment
  `π₂(S³) → π₂(S²) → π₁(S¹) → π₁(S³)` is now checked with only the left
  fibration-boundary exactness assumption remaining: the right
  boundary/fiber-inclusion exactness statement and the triviality of the two
  outer `S³` groups are checked. A checked wrapper now consumes the remaining
  recursive set-truncated exactness statement directly and returns the desired
  isomorphism `π₂(S²) ≅ π₁(S¹)`.

The final theorem `pi_3(S^2) = Z` is not yet proved. The top-level Agda file
now assembles the final isomorphism through two next-level files that themselves
compose one level further down. The Hopf comparison `π₃(S³) ≅ π₃(S²)` now has
its algebraic exactness-to-isomorphism step, trivial concrete-to-group bridge,
and Hopf LES packaging proved. The attempted route through fiber sequences of
concrete homotopy-group classifying maps has been rejected as too strong in
general. The current group-level LES bridge is therefore explicitly reduced to
comparing set-truncated adjacent exactness with ordinary group exactness of
concrete homotopy groups. The total-space set-truncated iterated exactness
case, the canonical shifted boundary case, and the trivial-codomain
fibration-boundary group exactness case now check; the outstanding general
bridge is the coherence identifying the canonical shifted boundary with the
looped recursive boundary map expected by the concrete-group homomorphism. The
`π₃(S³) ≅ ℤ` calculation is reduced to a stability comparison
`π₂(S²) ≅ π₃(S³)`, a Hopf base computation `π₂(S²) ≅ π₁(S¹)`, and the
checked group-level circle calculation `π₁(S¹) ≅ ℤ`. The remaining two
comparisons are still intentionally unfinished scaffolds, but the Hopf base
comparison now has its exactness-to-isomorphism wrapper, right-hand exactness,
and trivial outer groups checked.

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
| Exactness of pointed sets | [`src/structured-types/exact-sequences-pointed-sets.lagda.md`](src/structured-types/exact-sequences-pointed-sets.lagda.md) | Defines images, kernels, exactness of pointed-set maps, derives the mere-preimage/fiber form of image membership and exactness, proves transport across pointwise replacement of the second map, image-equivalent replacement of the first map, compatible middle self-map shifts of the second map, and injective comparison of the middle pointed set, and proves that the set truncation of the canonical fiber sequence `fiber g -> E -> B` is exact. |
| Boundary maps and LES exactness steps | [`src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md) | Defines the boundary pointed map, induced maps on homotopy groups of a fiber sequence, recursive boundary pointed maps, and boundary homomorphisms. It proves the first fiber-of-the-fiber identification, packages `Ω B ->* fiber g ->* E` as a pointed fiber sequence, proves pointed-set exactness for canonical and packaged `F ->* E ->* B` fiber sequences, proves pointed-set exactness for the packaged boundary segment `Ω B ->* F ->* E`, proves pointed-set exactness for the packaged loop-boundary segment `Ω E ->* Ω B ->* F`, proves pointed-set exactness for the looped packaged segment `Ω F ->* Ω E ->* Ω B`, proves pointed-set exactness for the canonical adjacent triples `Ω B ->* fiber g ->* E`, `Ω E ->* Ω B ->* fiber g`, and `Ω² B ->* Ω (fiber g) ->* Ω E`, transports the last canonical theorem to the packaged looped boundary/fiber-inclusion segment `Ω² B ->* Ω F ->* Ω E`, and bundles the first four packaged exactness proofs as an initial set-truncated LES segment. These are steps toward, not yet the full proof of, Theorem 8.4.6 of the HoTT book. |
| Higher homotopy groups of 1-types | [`src/synthetic-homotopy-theory/higher-homotopy-groups-truncated-types.lagda.md`](src/synthetic-homotopy-theory/higher-homotopy-groups-truncated-types.lagda.md) | Proves that positive concrete homotopy groups of pointed 1-types are trivial. |
| Circle and 1-sphere homotopy facts | [`src/synthetic-homotopy-theory/homotopy-groups-circle.lagda.md`](src/synthetic-homotopy-theory/homotopy-groups-circle.lagda.md) | Proves the loop-space equivalences for the circle and 1-sphere, the 1-type facts, and triviality of their positive concrete homotopy groups. |
| Low homotopy groups of `S³` | [`src/synthetic-homotopy-theory/homotopy-groups-sphere-3.lagda.md`](src/synthetic-homotopy-theory/homotopy-groups-sphere-3.lagda.md) | Proves that inhabited types are `(-1)`-connected, that `1`-connected pointed types have trivial concrete group, that `S³` is 2-connected by iterated suspension connectivity, and that `concrete-homotopy-group 0 (S³)` and `concrete-homotopy-group 1 (S³)` are trivial. |
| Integer powers of loops | [`src/synthetic-homotopy-theory/computing-integer-powers-of-loops.lagda.md`](src/synthetic-homotopy-theory/computing-integer-powers-of-loops.lagda.md) | Proves successor, predecessor, and automorphism-iteration addition computations for integer powers of loops. |
| Computing the loop space of the circle | [`src/synthetic-homotopy-theory/computing-loop-space-circle.lagda.md`](src/synthetic-homotopy-theory/computing-loop-space-circle.lagda.md) | Proves the universal-cover encoder concatenation computation, generator and inverse-generator integer-code computations, that integer powers of the circle loop encode to their exponents, and that `compute-loop-space-𝕊¹` sends loop concatenation to integer addition. |
| Underlying type of `π₁(S¹)` | [`src/synthetic-homotopy-theory/underlying-type-fundamental-group-sphere-1.lagda.md`](src/synthetic-homotopy-theory/underlying-type-fundamental-group-sphere-1.lagda.md) | Proves a no-hole carrier equivalence from the ordinary underlying type of `concrete-homotopy-group 0 (sphere-Pointed-Type 1)` to `ℤ`, proves the intermediate equivalence to `ΩS¹` preserves multiplication, proves that the loop-space computation sends both `refl` and the set-truncated reflexivity class to `zero-ℤ`, and transfers circle additivity to `compute-loop-space-sphere-1`. |
| Exactness-to-isomorphism algebra | [`src/group-theory/isomorphisms-from-exact-sequences-groups.lagda.md`](src/group-theory/isomorphisms-from-exact-sequences-groups.lagda.md) | Proves that two adjacent exact group triples with trivial outer groups make the middle homomorphism an isomorphism. |
| Trivial concrete-to-group bridge | [`src/group-theory/trivial-underlying-groups-concrete-groups.lagda.md`](src/group-theory/trivial-underlying-groups-concrete-groups.lagda.md) | Proves the bridge from `is-trivial-Concrete-Group G` to triviality of `group-Concrete-Group G`. |
| Underlying types of concrete homotopy groups | [`src/synthetic-homotopy-theory/underlying-groups-concrete-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/underlying-groups-concrete-homotopy-groups.lagda.md) | Proves that the ordinary underlying type of `concrete-homotopy-group n A` is equivalent to `type-homotopy-group (succ-ℕ n) A`, using connected-component extensionality and effectiveness of truncation, names the induced forward and inverse maps, and proves that the inverse map preserves the set-truncated loop multiplication. |
| Underlying maps of concrete homotopy groups | [`src/synthetic-homotopy-theory/underlying-maps-concrete-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/underlying-maps-concrete-homotopy-groups.lagda.md) | Defines the ordinary underlying map of a concrete homotopy-group homomorphism and its set-truncated loop comparison squares. The forward and inverse coherence squares are proved for concrete groups coming from pointed types, as are the unit comparison lemmas needed by group exactness transport and the forward multiplication-preservation theorem for the underlying-type comparison. |
| Computing identity types of subtypes | [`src/foundation/computing-identity-types-subtypes.lagda.md`](src/foundation/computing-identity-types-subtypes.lagda.md) | Proves the computation rule for the first component of subtype extensionality, used to control connected-component path calculations. |
| Computing identity types of automorphism-infinity groups | [`src/higher-group-theory/computing-identity-types-automorphism-infinity-groups.lagda.md`](src/higher-group-theory/computing-identity-types-automorphism-infinity-groups.lagda.md) | Proves section, concatenation, inverse, and loop-transport computation rules for paths in automorphism-infinity classifying types. |
| Computing binary functoriality of set truncation | [`src/foundation/computing-binary-functoriality-set-truncation.lagda.md`](src/foundation/computing-binary-functoriality-set-truncation.lagda.md) | Proves that `binary-map-trunc-Set` computes on two set-truncation units, and that the inverse of `equiv-unit-trunc-Set` for set types preserves any binary operation lifted by `binary-map-trunc-Set`. |
| Loop-space classifying-map computations | [`src/group-theory/computing-loop-space-functoriality-homotopy-automorphism-groups.lagda.md`](src/group-theory/computing-loop-space-functoriality-homotopy-automorphism-groups.lagda.md) | Computes `map-Ω` on the classifying pointed map of connected components after automorphism-infinity extensionality. |
| Loop-space naturality of effectiveness | [`src/synthetic-homotopy-theory/naturality-effectiveness-loop-spaces.lagda.md`](src/synthetic-homotopy-theory/naturality-effectiveness-loop-spaces.lagda.md) | Transports naturality of effectiveness of truncation into the based-loop form required by the inverse underlying-map square. |
| Naturality of effectiveness of truncation | [`src/foundation/naturality-effectiveness-truncation.lagda.md`](src/foundation/naturality-effectiveness-truncation.lagda.md) | Proves that effectiveness on a unit-truncated path computes to `ap unit-trunc`, that it preserves concatenation on truncation-unit loop representatives, and that effectiveness of truncation is natural in maps, up to the naturality paths of the truncation unit. These are reusable foundation lemmas needed by the underlying-map and multiplication comparisons for concrete homotopy groups. |
| Set-truncated iterated LES exactness | [`src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md`](src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md) | Defines the set-truncated maps on `Ω Ω^n F`, `Ω Ω^n E`, and `Ω Ω^n B`, plus both the recursive boundary map used by the concrete-group homomorphism and the canonical shifted boundary map suggested by Coq-HoTT. It now checks without `--allow-unsolved-metas`, proving the total-space iterated case for all `n`, exactness for the canonical shifted fibration-boundary case, and transport theorems that turn either a kernel equivalence or a pointwise canonical-vs-recursive boundary comparison into recursive boundary exactness. |
| Group exactness transport for homotopy groups | [`src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md`](src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md) | Proves a generic transfer theorem from pointed-set exactness to ordinary group exactness using explicit comparison maps, injectivity, unit compatibility, and coherence squares; proves a pointed-type wrapper; proves a trivial-codomain pointed-type wrapper that avoids comparing the second maps; and proves the total-space LES-specific transport target from set-truncated iterated exactness to ordinary group exactness of concrete homotopy groups. This file no longer uses `--allow-unsolved-metas`. |
| Group exactness of homotopy groups | [`src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md`](src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md) | Records the adjacent group-level exactness statements needed by the Hopf comparison. The total-space statement composes through the checked transport layer. The boundary/fiber-inclusion statement `π₂(B) -> π₁(F) -> π₁(E)` is now checked from the packaged looped boundary exactness theorem. The fibration-boundary statement is proved under the hypothesis that the target homotopy group is contractible, using canonical shifted boundary exactness and the trivial-codomain transport. The unrestricted nontrivial-target boundary statement is exposed as a checked wrapper from recursive set-level exactness, but still requires the canonical-vs-recursive boundary comparison to instantiate. |
| Hopf fiber sequence | [`src/synthetic-homotopy-theory/hopf-fiber-sequence.lagda.md`](src/synthetic-homotopy-theory/hopf-fiber-sequence.lagda.md) | Records the unfinished packaged fiber sequence with fiber `S¹`, total space `S³`, and base `S²` fixed definitionally. |
| Hopf LES comparison for second homotopy groups | [`src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md) | Proves the right-hand boundary/fiber-inclusion exactness statement for the lower Hopf segment and the algebraic extraction: the remaining left fibration-boundary exactness statement plus the checked trivial outer `S³` groups identify `π₂(S²)` with `π₁(S¹)`. It now also has a checked wrapper reducing that remaining left exactness input to the recursive set-truncated exactness statement at degree zero. |
| Hopf LES comparison for third homotopy groups | [`src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md) | Builds the Hopf comparison isomorphism from the Hopf fibration homomorphism, the checked total-space exactness theorem, the checked trivial-codomain fibration-boundary exactness theorem, and the two trivial endpoint hypotheses. |
| Hopf comparison for third homotopy groups | [`src/synthetic-homotopy-theory/hopf-fibration-third-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/hopf-fibration-third-homotopy-groups.lagda.md) | Delegates `π₃(S³) ≅ π₃(S²)` to the Hopf LES comparison scaffold and has no direct proof hole. |
| Stability comparison for `π₃(S³)` | [`src/synthetic-homotopy-theory/stability-third-homotopy-group-sphere-3.lagda.md`](src/synthetic-homotopy-theory/stability-third-homotopy-group-sphere-3.lagda.md) | Records the unfinished stability comparison `π₂(S²) ≅ π₃(S³)`. |
| Second homotopy group of `S²` | [`src/synthetic-homotopy-theory/second-homotopy-group-sphere-2.lagda.md`](src/synthetic-homotopy-theory/second-homotopy-group-sphere-2.lagda.md) | Records the unfinished Hopf-derived comparison `π₂(S²) ≅ π₁(S¹)`, now reduced to the recursive set-truncated exactness input for the lower Hopf segment. |
| Fundamental group of `S¹` | [`src/synthetic-homotopy-theory/fundamental-group-sphere-1.lagda.md`](src/synthetic-homotopy-theory/fundamental-group-sphere-1.lagda.md) | Proves the checked group isomorphism from the concrete fundamental group of `S¹` to `ℤ-Group`, with no unsolved metas or scaffold holes. |
| Third homotopy group of the 3-sphere | [`src/synthetic-homotopy-theory/third-homotopy-group-sphere-3.lagda.md`](src/synthetic-homotopy-theory/third-homotopy-group-sphere-3.lagda.md) | Delegates `π₃(S³) ≅ ℤ` to the stability comparison, the `π₂(S²) ≅ π₁(S¹)` comparison, and the `π₁(S¹) ≅ ℤ` scaffold, and has no direct proof hole. |
| Final theorem target | [`src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md`](src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md) | Records the pinned top-level statement `π₃(S²) ≅ ℤ` and proves it formally from the inverse Hopf-comparison stub and the `π₃(S³) ≅ ℤ` stub. The proof is therefore structurally assembled but depends on unfinished imported stubs. |

## Status against the formalization plan

| Plan item | Status | Notes |
|---|---|---|
| General pointed fiber sequences | Done | Implemented in [`src/structured-types/fiber-sequences.lagda.md`](src/structured-types/fiber-sequences.lagda.md). |
| Induced maps on homotopy groups | Done | Implemented via iterated loop functoriality and concrete homotopy group functoriality. |
| Long exact sequence of homotopy groups | Partial | Boundary maps, induced homomorphisms, pointed-set exactness, exactness of the set truncation of canonical and packaged `F ->* E ->* B` triples, exactness of the packaged boundary triple `Ω B ->* F ->* E`, exactness of the packaged loop-boundary triple `Ω E ->* Ω B ->* F`, exactness of the looped packaged triple `Ω F ->* Ω E ->* Ω B`, the first fiber-of-the-fiber identification `Ω B ≃* fiber (fiber g -> E)`, pointed-set exactness of the canonical triples `Ω B ->* fiber g ->* E`, `Ω E ->* Ω B ->* fiber g`, and `Ω² B ->* Ω (fiber g) ->* Ω E`, transported exactness of the packaged looped boundary/fiber-inclusion triple `Ω² B ->* Ω F ->* Ω E`, and a bundled initial four-triple set-truncated LES segment are formalized. The group-exactness transport layer is checked for the total-space case, for the boundary/fiber-inclusion case at `π₁(F)`, and for fibration-boundary targets whose codomain group is contractible. The set-truncated iterated total-space theorem and the canonical shifted boundary theorem are checked; the remaining unrestricted LES bridge work is a comparison/transport theorem between the canonical shifted boundary and the loop of the recursive boundary map used to define the concrete-group homomorphism. The classifying-map fiber-sequence route is recorded as too strong in general. |
| Exactness-to-isomorphism with zero endpoints | Done | Proved in [`src/group-theory/isomorphisms-from-exact-sequences-groups.lagda.md`](src/group-theory/isomorphisms-from-exact-sequences-groups.lagda.md). |
| Higher homotopy groups of the circle vanish | Mostly done | Positive concrete homotopy groups of the circle and 1-sphere are trivial. Further packaging may be needed for the exact Hopf LES endpoints. |
| Loop space of the circle is the integers | Done | The loop-space equivalence is formalized, the universal-cover encoder is proved additive on loop concatenation, the result is transferred to the 1-sphere, and the concrete group isomorphism `π₁(S¹) ≅ ℤ` is checked. |
| Hopf construction and Hopf fibration | Stubbed | The packaged Hopf fiber sequence target `S^1 -> S^3 -> S^2` is recorded, but the construction, maps, and fiber-sequence proof remain holes. |
| Hopf LES consequence `pi_3(S^3) = pi_3(S^2)` | Partially proved | The exactness-to-isomorphism extraction and Hopf LES packaging are proved, and the fibration-boundary exactness uses the checked trivial-codomain bridge. The comparison still depends on the unfinished Hopf fiber sequence scaffold. |
| Freudenthal suspension theorem | Not started | Still a major missing theorem. |
| Stability of homotopy groups of spheres | Instance stubbed | The needed comparison `π₂(S²) ≅ π₃(S³)` is recorded as an unfinished theorem depending on Freudenthal/stability. |
| Diagonal theorem `pi_n(S^n) = Z` | Reduced to lower stubs | The `n = 3` file now composes the stability, `π₂(S²) ≅ π₁(S¹)`, and `π₁(S¹) ≅ ℤ` scaffolds. The general theorem remains unproved. |
| Final theorem `pi_3(S^2) = Z` | Assembled from stubs | The target statement in [`src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md`](src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md) is now a formal composition of the two next-level stubs. It has no direct proof hole but remains mathematically unfinished until those imported stubs are proved. |

## Remaining tasks

1. Fill the remaining unrestricted lower-level LES bridge obligation by the
   upstream-quality structural route: package the Coq-HoTT-style
   `connect_fiberseq` analogue `Ω E ->* Ω B ->* F` as a pointed fiber sequence
   for any packaged fiber sequence `F ->* E ->* B`, with comparison equivalence
   `Ω E ≃* fiber (boundary : Ω B ->* F)`, and derive recursive looped exactness
   from that package. This is preferred over closing the local target by a bare
   image/kernel transport, because it exposes the reusable homotopy-theoretic
   structure that should ultimately be upstreamed. The image/kernel comparison
   between the checked canonical shifted fibration-boundary map and the loop of
   the recursive boundary map remains useful as a diagnostic or fallback,
   especially for the loop-inversion/sign discrepancy exposed by goal
   reduction. This bridge is no longer needed for the current Hopf
   `π₃(S³) ≅ π₃(S²)` segment because its right endpoint is trivial, but it is
   still needed for the unrestricted LES and the lower Hopf comparison. The
   total-space set-truncated iterated exactness, canonical shifted boundary
   exactness, pointed-set mere-preimage adapter, pointed-set exactness
   transports for image replacement, compatible middle self-map shifts,
   pointwise and kernel replacement of the second map, unit comparison, generic
   group-transfer theorem, pointed-type wrapper, trivial-codomain wrapper,
   total-space concrete homotopy-group transport, and iterated
   recursive-boundary transport theorem are checked.
2. Formalize the Hopf fiber sequence `S^1 -> S^3 -> S^2`, including the actual
   pointed maps and the fiber-sequence proof.
3. Fill the Hopf-derived comparison `π₂(S²) ≅ π₁(S¹)` by instantiating the
   checked lower Hopf set-level wrapper with exactness of
   `π₂(S³) → π₂(S²) → π₁(S¹)` for the recursive boundary map. The adjacent
   exactness of `π₂(S²) → π₁(S¹) → π₁(S³)` is now checked, and the
   `second-homotopy-group-sphere-2` scaffold hole has been narrowed to this
   recursive set-truncated exactness input.
4. Prove the stability comparison `π₂(S²) ≅ π₃(S³)` from Freudenthal and sphere
   stability.
5. Recheck `π₃(S³) ≅ ℤ` and `π₃(S²) ≅ ℤ` after their imported lower stubs are
   proved; their proof bodies should remain short compositions.

## Next agent handoff

The next agent should prioritize the structural `connect_fiberseq` route for
unrestricted fibration-boundary group exactness. Do not try to reduce the
canonical shifted boundary to the looped recursive boundary by `refl`: a direct
pointwise attempt at degree zero exposed a loop-inversion/sign discrepancy
rather than a definitional equality. The checked set-level theorem is
`is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence`
in `src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md`.
It proves exactness for the canonical shifted boundary
`hom-trunc-canonical-iterated-loop-boundary-fiber-sequence`. The current Hopf
fibration-boundary consumer in
`src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md`
avoids the comparison by assuming the target group is contractible and using
the checked trivial-codomain transport. A future unrestricted consumer should
first package the connecting pointed fiber sequence `Ω E ->* Ω B ->* F`, with
comparison equivalence `Ω E ≃* fiber (boundary : Ω B ->* F)`, then derive the
recursive looped exactness from that reusable package. An explicit
image/kernel transport across loop inversion remains a fallback or diagnostic
bridge, not the preferred final proof.

The next proof target is the first of these bridge routes; the second is a
fallback if the structural route exposes a missing prerequisite that cannot be
closed immediately:

1. Package the Coq-HoTT-style connecting fiber sequence `Ω E ->* Ω B ->* F` for a packaged fiber sequence `F ->* E ->* B`, with comparison equivalence `Ω E ≃* fiber (boundary : Ω B ->* F)`, and derive recursive looped exactness from iterating that packaged fiber sequence.
2. Prove an image/kernel comparison between the canonical shifted boundary hom on set truncations and the recursive looped boundary hom, allowing for loop inversion on the source, then feed it to `is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-kernel`. The pointed-set transport lemmas `is-exact-hom-Pointed-Set-iff-image-left`, `iff-image-hom-Pointed-Set-middle-self-map`, and `is-exact-hom-Pointed-Set-image-kernel-shift-right` were added for this route.

Useful starting files and definitions:

- `long-exact-sequence-homotopy-groups.lagda.md`: `map-fiber-boundary-map-Ω-Pointed-Type`, `map-inv-fiber-boundary-map-Ω-Pointed-Type`, `eq-map-Ω-map-inv-fiber-boundary-map-Ω-Pointed-Type`, and `iterated-loop-fiber-sequence`.
- `set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md`: the checked canonical shifted boundary theorem, the recursive boundary hom, and `is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence`, which reduces recursive exactness to a pointwise boundary comparison.
- `group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md`: the existing transport theorem that explains why the recursive classifying map is currently expected.

Expected verification state before the unrestricted bridge is solved:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
```

All should pass. If a future agent tries to restore an unrestricted fibration-boundary group exactness theorem by feeding the canonical shifted set-level theorem directly to the recursive-boundary group transport, the expected error is `UnequalTerms`, comparing the canonical shifted boundary from `iterated-loop-fiber-sequence S (succ-ℕ n)` with the looped recursive boundary `pointed-map-Ω (pointed-map-iterated-boundary-fiber-sequence S n)`.

## Current verification

On 2026-06-19, the lower Hopf reduction and pointed-set transport additions
were checked with:

```sh
./check.sh src/structured-types/exact-sequences-pointed-sets.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/second-homotopy-group-sphere-2.lagda.md
```

All passed. The last file still uses its existing `--allow-unsolved-metas`, but
its remaining hole is now the recursive set-truncated exactness input consumed
by `iso-second-homotopy-group-is-exact-set-truncation-hopf-segment`, not the
whole isomorphism.

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

On 2026-06-16, the external LES inspiration plan was implemented at the lower
bridge layer. The pointed-set exactness file gained a checked
mere-preimage/fiber interface. The underlying-map comparison gained a checked
unit lemma, proved via the inverse comparison and the section law, avoiding the
slow forward-composite normalization path. The group transport file gained a
checked generic theorem transferring pointed-set exactness to ordinary group
exactness from explicit comparison maps, injectivity proofs, unit compatibility,
and coherence squares, plus a pointed-type wrapper that instantiates it using
the checked underlying-map squares. Both concrete homotopy-group LES transport
targets are now proved, and the group transport file no longer uses
`--allow-unsolved-metas`. The checked commands were:

```sh
./check.sh src/structured-types/exact-sequences-pointed-sets.lagda.md
./check.sh src/synthetic-homotopy-theory/underlying-maps-concrete-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
```

All checks passed. A source search over the relevant bridge files now finds
holes only in
`set-truncated-iterated-exactness-homotopy-groups-fiber-sequences`: the
remaining total-space recursive iterated exactness target and the remaining
iterated fibration-boundary exactness target.

On 2026-06-18, the iterated set-truncated LES target was revised following the
Coq-HoTT `loops_les` architecture: the file now keeps the recursive boundary
map used by the concrete-group homomorphism, adds the canonical shifted
boundary map, proves total-space iterated exactness for all `n`, and proves
exactness for the canonical shifted fibration-boundary case. The temporary
route through target-loop inversion was removed. The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
```

Both checks passed. Rechecking
`src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md`
then failed for the expected remaining bridge reason: the checked canonical
shifted boundary map has the right source and target pointed sets, but Agda
rightly does not identify it with
`hom-trunc-iterated-loop-boundary-fiber-sequence`, i.e. the loop of the
recursive boundary map used by the concrete-group homomorphism. An attempted
stronger fix, packaging `Ω E ->* Ω B ->* F` as a pointed fiber sequence, reduced
to the missing section/coherence proof for the equivalence
`Ω E ≃* fiber (boundary : Ω B ->* F)`. The next focused theorem should be that
Coq-HoTT-style `connect_fiberseq` package, or an image/kernel transport lemma
that avoids strict equality of the two boundary formulas.

Later on 2026-06-18, the image/kernel transport route was narrowed further and
checked. `structured-types.exact-sequences-pointed-sets` now proves that
pointed-set exactness is invariant under a pointwise replacement of the second
map, and records the induced homotopy on set-truncated pointed maps.
`set-truncated-iterated-exactness-homotopy-groups-fiber-sequences` now applies
that lemma to prove recursive fibration-boundary exactness from a pointwise
comparison between `hom-trunc-iterated-loop-boundary-fiber-sequence` and
`hom-trunc-canonical-iterated-loop-boundary-fiber-sequence`. The checked
commands were:

```sh
./check.sh src/structured-types/exact-sequences-pointed-sets.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
```

All three checks passed. The remaining bridge is now specifically the
pointwise canonical-vs-recursive boundary comparison; an attempted proof via
the loop-fiber equivalence exposed that its inverse is intentionally abstract,
so a direct `refl`/computation proof is not available.

On 2026-06-19, the Hopf fibration-boundary segment was routed through a checked
trivial-codomain transport. The group exactness transport file now has a
generic trivial-codomain theorem and a pointed-type wrapper.
`exactness-homotopy-groups-fiber-sequences` proves the fibration-boundary group
exactness statement under contractibility of the target group, using canonical
shifted set-level exactness; this avoids the recursive-vs-canonical boundary
comparison for the Hopf `π₃(S³) ≅ π₃(S²)` segment. The unrestricted boundary
comparison remains open for nontrivial targets. The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
./check.sh src/structured-types/exact-sequences-pointed-sets.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-fibration-third-homotopy-groups.lagda.md
```

All checks passed. The edited LES and Hopf comparison files have no new holes
or postulates, and `git diff --check` passed. The Hopf comparison still depends
on the unfinished Hopf fiber sequence scaffold.

Later on 2026-06-19, the `π₁(S¹) ≅ ℤ` scaffold was narrowed. A new
underlying-type module proves the carrier equivalence from the ordinary
underlying type of `concrete-homotopy-group 0 (sphere-Pointed-Type 1)` to `ℤ`,
and records checked computations that the circle and 1-sphere loop-space
computations send `refl`, and the set-truncated reflexivity loop, to
`zero-ℤ`. The group-isomorphism scaffold now uses this carrier equivalence via
`iso-equiv-Group`; its remaining hole is exactly the multiplication/additivity
preservation proof for that equivalence. The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/underlying-type-fundamental-group-sphere-1.lagda.md
./check.sh src/synthetic-homotopy-theory/fundamental-group-sphere-1.lagda.md
```

Both checks passed. The new underlying-type module has no holes, no postulates,
and no `--allow-unsolved-metas`; the `fundamental-group-sphere-1` file retains
one intentional scaffold hole under `--allow-unsolved-metas`.

Later on 2026-06-19, the multiplicativity infrastructure for the `π₁(S¹)`
carrier comparison was completed one layer further. New checked foundation
lemmas prove that effectiveness of truncation preserves concatenation on
truncation-unit loop representatives, that `binary-map-trunc-Set` computes on
two set-truncation units, and that the inverse of `equiv-unit-trunc-Set` for
sets preserves lifted binary operations. These feed the concrete homotopy-group
comparison: the inverse underlying-type map now preserves set-truncated loop
multiplication, the forward underlying-type map preserves concrete-group
multiplication, and the `S¹` carrier equivalence to the actual loop space is
proved multiplicative. The checked commands were:

```sh
./check.sh src/foundation/naturality-effectiveness-truncation.lagda.md
./check.sh src/foundation/computing-binary-functoriality-set-truncation.lagda.md
./check.sh src/higher-group-theory/computing-identity-types-automorphism-infinity-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/underlying-groups-concrete-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/underlying-maps-concrete-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/underlying-type-fundamental-group-sphere-1.lagda.md
```

All checks passed. At that point, the remaining `fundamental-group-sphere-1`
hole was only the additivity of `compute-loop-space-sphere-1`, i.e. the proof
that the existing loop-space equivalence `ΩS¹ ≃ ℤ` sends loop concatenation to
integer addition.

Later on 2026-06-19, the `π₁(S¹) ≅ ℤ` group computation was completed. New
checked modules formalize integer powers of loops and the universal-cover
encoder calculations for the circle: right concatenation by the generating
loop increments the integer code, right concatenation by its inverse decrements
the code, integer powers of the generating loop encode to their exponents, and
`compute-loop-space-𝕊¹` preserves loop multiplication as integer addition. This
additivity was transferred across the pointed equivalence between the circle
and the 1-sphere, and the final `iso-fundamental-group-sphere-1-ℤ` proof was
closed with no `--allow-unsolved-metas`. The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/computing-integer-powers-of-loops.lagda.md
./check.sh src/synthetic-homotopy-theory/computing-loop-space-circle.lagda.md
./check.sh src/synthetic-homotopy-theory/underlying-type-fundamental-group-sphere-1.lagda.md
./check.sh src/synthetic-homotopy-theory/fundamental-group-sphere-1.lagda.md
```

All checks passed. The next direct target for the final theorem is now the
Hopf-derived comparison `π₂(S²) ≅ π₁(S¹)` or the Hopf fiber sequence itself;
the circle endpoint is checked.

Later on 2026-06-19, progress was made on the lower Hopf LES segment. Pointed
set exactness gained a transport theorem across an injective comparison of the
middle pointed set. The long exact sequence file now transports the canonical
looped boundary theorem `Ω² B ->* Ω (fiber g) ->* Ω E` across the loop of the
chosen-fiber equivalence to prove exactness of the packaged segment
`Ω² B ->* Ω F ->* Ω E`. This gives a checked group-level
boundary/fiber-inclusion exactness theorem
`π₂(B) -> π₁(F) -> π₁(E)`, which in the Hopf case discharges the right-hand
exactness assumption for the lower segment
`π₂(S³) -> π₂(S²) -> π₁(S¹) -> π₁(S³)`. The remaining lower Hopf exactness
assumption is the left fibration-boundary statement
`π₂(S³) -> π₂(S²) -> π₁(S¹)`, still blocked on the nontrivial-target
canonical-vs-recursive boundary comparison. The checked commands were:

```sh
./check.sh src/structured-types/exact-sequences-pointed-sets.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/homotopy-groups-sphere-3.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
```

All checks passed.

Later on 2026-06-19, the upstream-quality route for the remaining lower Hopf fibration-boundary exactness advanced structurally. The long exact sequence file now proves an unpointed equivalence

```text
Ω E ≃ fiber (boundary-fiber-Pointed-Type g)
```

by comparing `boundary-fiber-Pointed-Type g` with the fiber inclusion of the fiber inclusion via the existing pointed equivalence `Ω B ≃ fiber (inclusion-fiber-Pointed-Type g)` and the generic `fiber-triangle` equivalence. This avoids the earlier brittle direct section proof for `map-fiber-boundary-map-Ω-Pointed-Type`; the remaining refinement is to package the equivalence pointedly, which requires a reusable basepoint-coherence lemma for the `fiber-triangle` map induced by a pointed homotopy. The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed, and the touched LES file contains no holes, postulates, or `--allow-unsolved-metas`.


Later on 2026-06-19, the structural boundary-fiber comparison was upgraded from an unpointed equivalence to a pointed equivalence. The long exact sequence file now includes a reusable computation lemma for `fiber-triangle` and proves that the induced equivalence

```text
fiber (boundary-fiber-Pointed-Type g) ≃ fiber (inclusion-fiber-Pointed-Type (inclusion-fiber-Pointed-Type g))
```

preserves the distinguished fiber point. Composing its pointed inverse with the existing HoTT Book 8.4.4-style pointed equivalence for `inclusion-fiber-Pointed-Type g` gives the checked pointed equivalence

```text
Ω E ≃∗ fiber (boundary-fiber-Pointed-Type g)
```

as `pointed-equiv-fiber-boundary-map-Ω-Pointed-Type`. This removes the previous blocker that the structural comparison had not yet been packaged pointedly. The next direct target is to use this pointed equivalence to prove the canonical loop-fibration-boundary fiber sequence `Ω E ->* Ω B ->* fiber g`, then transport it to the packaged fiber sequence boundary used in the Hopf lower LES segment. The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed, and the touched LES file contains no holes, postulates, or `--allow-unsolved-metas`.


Later on 2026-06-19, the recursive-vs-canonical boundary comparison target was reframed at the right level. The set-truncated iterated exactness module now includes

```text
is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-pointed-htpy
```

which converts a pointed homotopy between the recursive looped boundary map and the canonical boundary map into the exactness statement needed for the fibration-boundary segment. The group exactness module lifts this to

```text
is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-pointed-htpy
```

and the lower Hopf module now exposes the direct endpoint

```text
iso-second-homotopy-group-pointed-htpy-hopf-segment
```

so that a future proof of the pointed boundary comparison immediately yields the `π₂(S²) ≅ π₁(S¹)` isomorphism. This does not prove the boundary comparison itself, but it replaces the previous set-level pointwise-equality interface with the upstream-quality pointed-homotopy interface we actually want. The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
```

All checks passed. The next direct proof obligation is now a pointed homotopy

```text
pointed-map-Ω (pointed-map-iterated-boundary-fiber-sequence S n) ~∗
boundary-pointed-map-fiber-sequence (iterated-loop-fiber-sequence S (succ-ℕ n))
```

and for the lower Hopf segment specifically the case `S = hopf-fiber-sequence-sphere-1-sphere-3-sphere-2`, `n = 0`.


Later on 2026-06-20, the recursive-vs-canonical boundary comparison work made checked infrastructure progress while avoiding a false shortcut. The long exact sequence file now records reusable pointed-equivalence algebra for loops of inverse pointed equivalences and inverses of composite pointed equivalences, and it defines the canonical shifted iterated boundary map

```text
canonical-pointed-map-iterated-boundary-fiber-sequence n
  : Omega^(n+1) B ->* Omega^n F
```

as the boundary map of the iterated-loop fiber sequence transported back along the iterated fiber equivalence. A proposed raw pointed homotopy identifying the recursive looped boundary with this canonical shifted boundary was deliberately not kept: the real `./check.sh` gate reduced the comparison to a source-loop inversion obstruction of the form `ap (λ u → refl ∙ inv u) q = q`. This confirms that the upstreamable bridge must be an explicitly oriented comparison or the full `connect_fiberseq`-style pointed fiber sequence package, not a definitional or unproved sign fix. The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed. The touched LES file contains no new holes, postulates, or `--allow-unsolved-metas`. The existing pointed-homotopy adapters downstream remain the correct consumers once the oriented boundary comparison is proved.


Later on 2026-06-21, the `connect_fiberseq` route gained a checked comparison between the canonical boundary of the fibration map and the packaged boundary of a fiber sequence. The long exact sequence file now defines

```text
equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type
pointed-equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type
pointed-htpy-inclusion-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type
```

The pointed equivalence identifies

```text
fiber (boundary-fiber-Pointed-Type (fibration-fiber-sequence-Pointed-Type S))
  ~=*
fiber boundary-pointed-map-fiber-sequence
```

using `equiv-tot` over the common loop coordinate and the inverse of `pointed-equiv-fiber-fiber-sequence-Pointed-Type S`. The pointed homotopy proves that this comparison is over `Omega B`: both fiber inclusions have the same first projection. This removes the codomain-transport part of the planned upstream-quality `Omega E ->* Omega B ->* F` fiber-sequence package.

An attempted direct package through the older `pointed-equiv-fiber-boundary-map-Ω-Pointed-Type` was not kept, because real Agda reduces its required triangle to a non-definitional first-projection equality. The remaining hard target is therefore precise: construct a direct over-`Omega B` pointed equivalence `Omega E ~=* fiber boundary-pointed-map-fiber-sequence`, or prove the required projection law for the existing equivalence without changing orientations. After that, the package `Omega E ->* Omega B ->* F` can feed the set-truncated exactness theorem needed for the lower Hopf segment. The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed. The touched LES file contains no new holes, postulates, or `--allow-unsolved-metas`.


Later on 2026-06-21, the direct `connect_fiberseq` equivalence was advanced past the previous projection obstruction. The long exact sequence file now defines

```text
equiv-fiber-map-Ω-fiber-ap-Pointed-Type
equiv-fiber-map-Ω-boundary-map-Ω-Pointed-Type
equiv-fiber-boundary-map-Ω-direct-Pointed-Type
htpy-inclusion-fiber-boundary-map-Ω-direct-Pointed-Type
```

For an arbitrary pointed map `g : E ->* B`, this gives a direct unpointed equivalence

```text
Omega E ~= fiber (boundary-fiber-Pointed-Type g)
```

built by total-fiber factorization of `map-Ω g`. Unlike the older pointed equivalence, its first projection is definitionally aligned with `map-Ω g`, recorded by `htpy-inclusion-fiber-boundary-map-Ω-direct-Pointed-Type`. Composing this with the already checked canonical-to-packaged boundary-fiber comparison gives the packaged fiber-sequence version

```text
equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type
htpy-inclusion-fiber-boundary-fiber-sequence-direct-Pointed-Type
```

so the comparison `Omega E ~= fiber boundary-pointed-map-fiber-sequence` is now checked and over `Omega B`. The remaining hard coherence is the basepoint preservation for this direct equivalence; once that is proved, it can be packaged as the pointed equivalence required for the full `Omega E ->* Omega B ->* F` fiber sequence. The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed. The touched LES file contains no new holes, postulates, or `--allow-unsolved-metas`.


Later on 2026-06-21, the direct `connect_fiberseq` route cleared the first
basepoint-coherence obstruction. The long exact sequence file now records an
explicit inverse equivalence for the fiber equality comparison:

```text
equiv-map-inv-fiber-ap-eq-fiber
```

This packages the already available map `map-inv-fiber-ap-eq-fiber` as an
equivalence by proving it is homotopic to the abstract inverse of
`equiv-fiber-ap-eq-fiber`. The direct boundary-fiber comparison now uses this
explicit inverse rather than `inv-equiv (equiv-fiber-ap-eq-fiber ...)`, removing
the noncomputing abstract inverse that blocked the basepoint proof.

The same run also added the checked basepoint computation for the explicit
forward boundary-fiber map

```text
preserves-point-map-fiber-boundary-map-Ω-Pointed-Type
```

A renewed attempt to prove basepoint preservation for the full direct
equivalence reduced to the next precise obstruction: the abstract inverse of
`equiv-ap (equiv-tr-type-Ω refl)` inside
`equiv-fiber-map-Ω-fiber-ap-Pointed-Type`. The remaining hard target is now to
make that `map-Ω`/`ap` fiber conversion explicit, after which the direct
equivalence should be packageable as a pointed equivalence. The checked command
was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed. The touched LES file contains no new holes, postulates, or
`--allow-unsolved-metas`.


Later on 2026-06-21, the direct `connect_fiberseq` analogue for a pointed map was packaged as a checked pointed fiber sequence. The long exact sequence file now removes the last noncomputing `map-Ω`/`ap` conversion obstruction by defining an explicit conjugation inverse for loop-space transport:

```text
map-inv-tr-type-Ω-concat-inv-Pointed-Type
equiv-map-inv-tr-type-Ω-concat-inv-Pointed-Type
equiv-eq-map-Ω-eq-ap-Pointed-Type
```

Using this explicit inverse, the direct boundary-fiber equivalence now computes at the basepoint. The file consequently defines the reusable pointed package

```text
pointed-equiv-fiber-boundary-map-Ω-direct-Pointed-Type
pointed-htpy-inclusion-fiber-boundary-map-Ω-direct-Pointed-Type
is-fiber-sequence-boundary-map-Ω-direct-Pointed-Type
fiber-sequence-boundary-map-Ω-direct-Pointed-Type
```

for every pointed map `g : E ->* B`, exhibiting

```text
Omega E ->* Omega B ->* fiber g
```

as a pointed fiber sequence via the direct equivalence `Omega E ~=* fiber (boundary-fiber-Pointed-Type g)`. The fiber-sequence-specialized comparison is also now pointed:

```text
pointed-equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type
```

This clears the previous hard basepoint-coherence block. The next hard target is to feed this direct pointed fiber-sequence package into the set-truncated exactness layer and then bridge the canonical shifted boundary maps to the recursive concrete homotopy-group boundary maps. The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed. `git diff --check` passed, and the touched LES file contains no holes, postulates, or `--allow-unsolved-metas`.


Later on 2026-06-21, the direct `connect_fiberseq` package was connected to the set-truncated exactness layer. The long exact sequence file now defines, for every packaged pointed fiber sequence `S`, the pointed coherence and fiber-sequence package

```text
pointed-htpy-inclusion-fiber-boundary-fiber-sequence-direct-Pointed-Type
is-fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type
fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type
```

This packages the adjacent sequence

```text
Omega E ->* Omega B ->* F
```

for a fiber sequence `F ->* E ->* B`, using the direct equivalence
`Omega E ~=* fiber (boundary-pointed-map-fiber-sequence S)`. The pointed equivalence
`pointed-equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type` is now explicitly
constructed by `comp-pointed-equiv`, so the inclusion coherence is obtained by
composing the raw-map direct coherence with the canonical-to-packaged boundary
fiber coherence.

The set-truncated exactness theorem for the raw pointed-map segment

```text
is-exact-set-truncation-loop-boundary-fiber-sequence-Pointed-Type
```

now factors through `fiber-sequence-boundary-map-Ω-direct-Pointed-Type`, and the
packaged theorem

```text
is-exact-set-truncation-loop-boundary-fiber-sequence
```

now factors through `fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type S`.
The previous bespoke image comparison for the raw segment and the previous
kernel-transport adapters for the packaged segment were removed. This makes the
set-truncated exactness proof follow the structural fiber-sequence route rather
than re-proving image/kernel transport locally.

The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed. `git diff --check` passed, and the touched LES file contains no
holes, postulates, or `--allow-unsolved-metas`.
