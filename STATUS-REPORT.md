# Formalization status report

This report tracks the autoformalized Agda code in this repository against
[the formalization plan](FORMALIZATION-PLAN.md) for `pi_3(S^2) = Z`.

Update this file whenever significant progress is made, for example when a
new theorem is proved, an important definition is formalized, a planned module
is added, or a major blocked item is resolved or re-scoped.

Last updated: 2026-06-22.

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
- The circle H-space prerequisite for the Hopf construction is now checked.
  The module `h-space-structure-circle` packages the standard multiplication
  on `𝕊¹` as `𝕊¹-H-Space` and transports it to the 1-sphere as
  `sphere-1-H-Space`. It now also proves that all left and right translations
  by circle and 1-sphere points are equivalences, and packages the Hopf shear
  equivalence `(x , y) ↦ (y , x · y)` on `S¹ × S¹`.
- The first Hopf-construction layer is now checked. The generic module
  `hopf-construction` defines the Hopf map `A * A -> suspension A` and its
  pointed form for any H-space, and `hopf-construction-circle` specializes it
  to a pointed map `S¹ * S¹ ->* S²`.
- The Hopf-family/descent input over `S²` is now checked. The module
  `hopf-family-circle` defines the type family over `sphere 2` whose pole
  fibers are both `sphere 1` and whose meridians are the univalent paths
  classified by left multiplication on `sphere 1`; it also records the pole and
  meridian computation rules, names the family total space, identifies the
  fiber of the projection over the north pole with `sphere 1`, packages the
  projection as a pointed fiber sequence `S¹ ->* total ->* S²`, proves by the
  flattening lemma that the actual family total space is a pushout of the
  family-induced flattened span, names the Hopf-family descent data over the
  suspension span, forms its flattened descent span, and proves that the
  standard join `S¹ * S¹` is a pushout of that explicit flattened span via the
  Hopf shear. It now also names all three vertex equivalences comparing the
  family-induced flattened span with the explicit flattened descent span,
  proves both the definitional left-leg comparison and the right-leg meridian
  coherence, transports the family total-space pushout property to the
  explicit flattened descent span, and packages the canonical equivalence
  `total-space-hopf-family-sphere-1 ≃ S¹ * S¹`. It now also exposes the
  definitional comparison with the Hopf-construction total space and composes
  the checked `S¹ * S¹` bridge to give
  `total-space-hopf-family-sphere-1 ≃
  join-power 2 (Fin 2) * join-power 2 (Fin 2)`.
- The first total-space comparison layers for the Hopf construction are now
  checked. The module `suspensions-as-joins` proves an upstream-style
  equivalence `Fin 2 * X ≃ suspension X` by first identifying cocones over the
  `Fin 2 × X` join span with suspension structures, then deriving the pushout
  universal property for the suspension cocone. The module
  `hopf-family-circle` now also proves the pushout universal property of the
  actual Hopf-family total space for the family-induced flattened span, and the
  pushout universal property of `S¹ * S¹` for the explicit flattened
  Hopf-family descent span, using the unit-vertex equivalences and the Hopf
  shear. The module `spheres-as-join-powers` proves
  `join-power (succ n) (Fin 2) ≃ sphere n`,
  with named `S¹` and `S³` instances, and now also uses join functoriality to
  compare `S¹ * S¹` with the join of two `join-power 2 (Fin 2)` models. The
  new join infrastructure proves functoriality of joins under maps, preservation
  of equivalences by this functorial action, and commutativity `A * B ≃ B * A`.
  The Hopf-family total space and the canonical Hopf-construction total-space
  accessor are now checked equivalent to
  `join-power 2 (Fin 2) * join-power 2 (Fin 2)`. The structural join
  arithmetic now has a checked product-preservation pushout theorem, a checked
  associator map `((A * B) * C) -> A * (B * C)`, a checked inverse-direction
  associator map `A * (B * C) -> (A * B) * C`, and a checked generic
  comparison map
  `join-power 2 A * join-power 2 A -> join-power 4 A`. There is also a checked
  reduction proving this join-power comparison is an equivalence once the two
  relevant associator instances are equivalences. The remaining total-space
  comparison is therefore focused on the inverse-homotopy/universal-property
  proof for the associator itself, then transporting to the `S³` model.
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
  all `n`, the Coq-HoTT-style canonical shifted boundary case, transport
  theorems reducing recursive boundary exactness to boundary comparisons, and
  direct recursive fibration-boundary exactness for all iterates in the
  public `Ω^(n+1) X` indexing, by transporting the direct `Ω^n(Ω X)`
  theorem through checked reassociation of pointed types and induced maps. The
  Hopf `π₃(S²)` fibration-boundary segment now uses this checked direct
  exactness instead of the trivial-codomain shortcut. The looped
  boundary/fiber-inclusion segment `Ω² B ->* Ω F ->* Ω E` is also checked for
  packaged fiber sequences by transporting the canonical fiber version across
  the loop of the chosen-fiber equivalence, and it has been transported to
  ordinary group exactness at `π₁(F)`. The nontrivial-target
  fibration-boundary group exactness statement remains exposed as a checked
  wrapper from recursive set-level exactness. The packaged
  canonical-vs-recursive shifted-boundary comparison now has a checked full
  fiber equality after a generic path-splitting computation for applying
  pointed maps to paths into the base followed by loops. It also identifies the
  direct shifted boundary map pointwise with the recursive looped fiber
  inclusion, and lifts that comparison to set-truncated homomorphisms. The arbitrary-index
  fibration-boundary bridge is now checked at the set-truncated level and lifted to group exactness.
- The algebraic extraction for the lower Hopf segment
  `π₂(S³) → π₂(S²) → π₁(S¹) → π₁(S³)` is now checked. The left
  fibration-boundary exactness input is supplied by looping the packaged direct
  connecting fiber sequence `Ω S³ ->* Ω S² ->* S¹`; the right
  boundary/fiber-inclusion exactness statement and the triviality of the two
  outer `S³` groups are also checked. The Hopf-derived comparison
  `π₂(S²) ≅ π₁(S¹)` now has a checked proof body and no local scaffold hole.

The final theorem `pi_3(S^2) = Z` is not yet proved. The top-level Agda file
now assembles the final isomorphism through two next-level files that themselves
compose one level further down. The Hopf comparison `π₃(S³) ≅ π₃(S²)` now has
its algebraic exactness-to-isomorphism step, trivial concrete-to-group bridge,
and Hopf LES packaging proved. The attempted route through fiber sequences of
concrete homotopy-group classifying maps has been rejected as too strong in
general. The current group-level LES bridge is therefore explicitly reduced to
comparing set-truncated adjacent exactness with ordinary group exactness of
concrete homotopy groups. The total-space set-truncated iterated exactness
case, the canonical shifted boundary case, the unrestricted direct
fibration-boundary set-level case, and the unrestricted direct
fibration-boundary group exactness case now check. The
`π₃(S³) ≅ ℤ` calculation is reduced to the stability comparison
`π₂(S²) ≅ π₃(S³)`, the now-checked Hopf base computation
`π₂(S²) ≅ π₁(S¹)`, and the checked group-level circle calculation
`π₁(S¹) ≅ ℤ`. The remaining imported scaffolds for the final theorem are the
Hopf fiber sequence itself and the Freudenthal/stability comparison.

## Implemented Agda code

| Area | File | Current status |
|---|---|---|
| Pointed fiber sequences | [`src/structured-types/fiber-sequences.lagda.md`](src/structured-types/fiber-sequences.lagda.md) | Defines the canonical pointed fiber inclusion, `is-fiber-sequence-Pointed-Type`, packaged `fiber-sequence-Pointed-Type`, accessors, null composite maps, and the canonical fiber sequence of a pointed map. |
| Iterated loop functoriality | [`src/synthetic-homotopy-theory/functoriality-iterated-loop-spaces.lagda.md`](src/synthetic-homotopy-theory/functoriality-iterated-loop-spaces.lagda.md) | Defines the pointed map induced by a pointed map on iterated loop spaces. |
| Reassociation of iterated loop spaces | [`src/synthetic-homotopy-theory/reassociation-iterated-loop-spaces.lagda.md`](src/synthetic-homotopy-theory/reassociation-iterated-loop-spaces.lagda.md) | Proves the pointed-type reassociation equalities identifying `Ω^(n+1) X` with `Ω^n(Ω X)`, the corresponding looped pointed-type equalities, transport of `pointed-map-Ω`, and reassociation for induced maps on iterated loop spaces. |
| Homotopy automorphism functoriality | [`src/group-theory/functoriality-homotopy-automorphism-groups.lagda.md`](src/group-theory/functoriality-homotopy-automorphism-groups.lagda.md) | Defines classifying pointed maps and induced homomorphisms of concrete homotopy automorphism groups. |
| Homotopy group functoriality | [`src/synthetic-homotopy-theory/functoriality-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/functoriality-homotopy-groups.lagda.md) | Defines `hom-concrete-homotopy-group`, the homomorphism induced by a pointed map on concrete homotopy groups. |
| Classifying fiber-sequence route for homotopy groups | [`src/synthetic-homotopy-theory/classifying-fiber-sequences-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/classifying-fiber-sequences-homotopy-groups.lagda.md) | Records why the classifying-map fiber-sequence route is too strong for adjacent LES exactness and deliberately contains no theorem statements. |
| Exactness of group homomorphisms | [`src/group-theory/exact-sequences-groups.lagda.md`](src/group-theory/exact-sequences-groups.lagda.md) | Defines `is-exact-hom-Group` and proves `is-exact-is-fiber-sequence-hom-Concrete-Group`, the forward implication from a fiber sequence of concrete-group classifying maps to exactness of the induced ordinary group homomorphisms. |
| Pointed sets | [`src/structured-types/pointed-sets.lagda.md`](src/structured-types/pointed-sets.lagda.md) | Defines pointed sets, pointed maps of pointed sets, set truncation as a pointed set and as a pointed map, and transport of `hom-trunc-Pointed-Set` along identified source and target pointed types. |
| Exactness of pointed sets | [`src/structured-types/exact-sequences-pointed-sets.lagda.md`](src/structured-types/exact-sequences-pointed-sets.lagda.md) | Defines images, kernels, exactness of pointed-set maps, derives the mere-preimage/fiber form of image membership and exactness, proves transport across identified pointed-set triples and maps, pointwise replacement of the second map, image-equivalent replacement of the first map, compatible middle self-map shifts of the second map, and injective comparison of the middle pointed set, and proves that the set truncation of the canonical fiber sequence `fiber g -> E -> B` is exact. |
| Boundary maps and LES exactness steps | [`src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md) | Defines the boundary pointed map, induced maps on homotopy groups of a fiber sequence, recursive boundary pointed maps, and boundary homomorphisms. It proves the first fiber-of-the-fiber identification, packages `Ω B ->* fiber g ->* E` as a pointed fiber sequence, proves pointed-set exactness for canonical and packaged `F ->* E ->* B` fiber sequences, proves pointed-set exactness for the packaged boundary segment `Ω B ->* F ->* E`, proves pointed-set exactness for the packaged loop-boundary segment `Ω E ->* Ω B ->* F`, proves pointed-set exactness for the looped packaged segment `Ω F ->* Ω E ->* Ω B`, proves pointed-set exactness for the canonical adjacent triples `Ω B ->* fiber g ->* E`, `Ω E ->* Ω B ->* fiber g`, and `Ω² B ->* Ω (fiber g) ->* Ω E`, transports the last canonical theorem to the packaged looped boundary/fiber-inclusion segment `Ω² B ->* Ω F ->* Ω E`, and bundles the first four packaged exactness proofs as an initial set-truncated LES segment. These are steps toward, not yet the full proof of, Theorem 8.4.6 of the HoTT book. |
| Higher homotopy groups of 1-types | [`src/synthetic-homotopy-theory/higher-homotopy-groups-truncated-types.lagda.md`](src/synthetic-homotopy-theory/higher-homotopy-groups-truncated-types.lagda.md) | Proves that positive concrete homotopy groups of pointed 1-types are trivial. |
| Circle and 1-sphere homotopy facts | [`src/synthetic-homotopy-theory/homotopy-groups-circle.lagda.md`](src/synthetic-homotopy-theory/homotopy-groups-circle.lagda.md) | Proves the loop-space equivalences for the circle and 1-sphere, the 1-type facts, and triviality of their positive concrete homotopy groups. |
| Circle and 1-sphere H-space structures | [`src/synthetic-homotopy-theory/h-space-structure-circle.lagda.md`](src/synthetic-homotopy-theory/h-space-structure-circle.lagda.md) | Packages the existing circle multiplication as a coherent `𝕊¹-H-Space`, transports it across the circle--1-sphere equivalence, packages the transported multiplication as `sphere-1-H-Space`, proves that left and right translations on both the circle and 1-sphere are equivalences, and proves the Hopf shear equivalence on `S¹ × S¹`. |
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
| Set-truncated iterated LES exactness | [`src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md`](src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md) | Defines the set-truncated maps on `Ω Ω^n F`, `Ω Ω^n E`, and `Ω Ω^n B`, plus both the recursive boundary map used by the concrete-group homomorphism and the canonical shifted boundary map suggested by Coq-HoTT. It checks without `--allow-unsolved-metas`, proving the total-space iterated case for all `n`, exactness for the canonical shifted fibration-boundary case, transport theorems that turn either a kernel equivalence or a pointwise canonical-vs-recursive boundary comparison into recursive boundary exactness, and direct recursive fibration-boundary exactness for all iterates in the public shifted indexing by reassociation transport; the finite Hopf-facing instances reduce to the all-index theorem. |
| Group exactness transport for homotopy groups | [`src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md`](src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md) | Proves a generic transfer theorem from pointed-set exactness to ordinary group exactness using explicit comparison maps, injectivity, unit compatibility, and coherence squares; proves a pointed-type wrapper; proves a trivial-codomain pointed-type wrapper that avoids comparing the second maps; and proves the total-space LES-specific transport target from set-truncated iterated exactness to ordinary group exactness of concrete homotopy groups. This file no longer uses `--allow-unsolved-metas`. |
| Group exactness of homotopy groups | [`src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md`](src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md) | Records the adjacent group-level exactness statements needed by the Hopf comparison. The total-space statement composes through the checked transport layer. The boundary/fiber-inclusion statement `π₂(B) -> π₁(F) -> π₁(E)` is checked from the packaged looped boundary exactness theorem. The fibration-boundary statement is still available under a trivial-codomain hypothesis, and the unrestricted nontrivial-target fibration-boundary statement now has a direct checked group exactness theorem for every index, obtained from the reassociated public set-level direct theorem. The Hopf `π₃(S³) -> π₃(S²) -> π₂(S¹)` segment is the second shifted instance of this all-index theorem. |
| Hopf construction | [`src/synthetic-homotopy-theory/hopf-construction.lagda.md`](src/synthetic-homotopy-theory/hopf-construction.lagda.md) | Defines the generic Hopf total space `A * A`, base `suspension A`, cocone, map, pointed total space, pointed base, and pointed Hopf map for any H-space. |
| Hopf construction on the 1-sphere | [`src/synthetic-homotopy-theory/hopf-construction-circle.lagda.md`](src/synthetic-homotopy-theory/hopf-construction-circle.lagda.md) | Specializes the generic Hopf construction to `sphere-1-H-Space`, yielding the checked pointed map `S¹ * S¹ ->* S²`, and exposes the unpointed comparison from the Hopf-construction total space to `join-power 2 (Fin 2) * join-power 2 (Fin 2)`. |
| Hopf construction source fiber sequence | [`src/synthetic-homotopy-theory/hopf-construction-fiber-sequence.lagda.md`](src/synthetic-homotopy-theory/hopf-construction-fiber-sequence.lagda.md) | Packages the canonical fiber sequence of the Hopf-construction pointed map and its sphere-1 specialization, and now exposes the total-space accessor comparison to `join-power 2 (Fin 2) * join-power 2 (Fin 2)`. |
| Hopf family over `S²` | [`src/synthetic-homotopy-theory/hopf-family-circle.lagda.md`](src/synthetic-homotopy-theory/hopf-family-circle.lagda.md) | Defines the Hopf family over `sphere 2` using the univalent paths classified by left multiplication equivalences on `sphere 1`, proves the pole and meridian computation rules, names the total space of the family, identifies the north fiber of its projection with `sphere 1`, packages that projection as a pointed fiber sequence, proves by the flattening lemma that the family total space is a pushout of the family-induced flattened span, names the corresponding descent data over the suspension span and its flattened span, proves that `S¹ * S¹` is a pushout of that explicit flattened span by comparison with the standard join span via the Hopf shear, completes the comparison between the two flattened spans by proving both leg coherences, transports the total-space pushout property to the explicit span, packages the canonical equivalence `total-space-hopf-family-sphere-1 ≃ S¹ * S¹`, identifies the family total space with the Hopf-construction total space, and composes to a checked comparison with `join-power 2 (Fin 2) * join-power 2 (Fin 2)`. |
| Suspensions as joins | [`src/synthetic-homotopy-theory/suspensions-as-joins.lagda.md`](src/synthetic-homotopy-theory/suspensions-as-joins.lagda.md) | Defines the `Fin 2 × X` join span, maps both directions between `Fin 2 * X` and `suspension X`, proves cocones over that span equivalent to suspension structures, derives the pushout universal property for the suspension cocone, and packages the checked equivalence `Fin 2 * X ≃ suspension X`. |
| Functoriality of joins | [`src/synthetic-homotopy-theory/functoriality-joins-of-types.lagda.md`](src/synthetic-homotopy-theory/functoriality-joins-of-types.lagda.md) | Defines the map induced on joins by maps in both factors, proves its constructor computation rules, proves that it preserves equivalences by pushout invariance under equivalences of spans, and packages the resulting `equiv-join`. |
| Type arithmetic for joins | [`src/synthetic-homotopy-theory/type-arithmetic-joins-of-types.lagda.md`](src/synthetic-homotopy-theory/type-arithmetic-joins-of-types.lagda.md) | Proves commutativity of joins, `A * B ≃ B * A`, using the pushout-swap theorem and the commutativity equivalence of cartesian products. It now also proves that products preserve join pushouts via the flattening lemma, constructs the checked associator cocone and map `((A * B) * C) -> A * (B * C)`, and constructs the checked inverse-direction cocone and map `A * (B * C) -> (A * B) * C`, including the glue coherences needed to make both maps structural rather than sphere-mediated. |
| Spheres as join powers | [`src/synthetic-homotopy-theory/spheres-as-join-powers.lagda.md`](src/synthetic-homotopy-theory/spheres-as-join-powers.lagda.md) | Proves by induction that the nonzero join powers of `Fin 2` are spheres, packaged as `join-power (succ n) (Fin 2) ≃ sphere n`, with named `S¹` and `S³` instances, proves the Hopf-facing comparison from `S¹ * S¹` to the join of two `join-power 2 (Fin 2)` models, defines the checked structural comparison map `join-power 2 A * join-power 2 A -> join-power 4 A` with the `Fin 2` specialization, and proves that this comparison is an equivalence assuming the two relevant associator instances are equivalences. |
| Hopf fiber sequence | [`src/synthetic-homotopy-theory/hopf-fiber-sequence.lagda.md`](src/synthetic-homotopy-theory/hopf-fiber-sequence.lagda.md) | Records the unfinished packaged fiber sequence with fiber `S¹`, total space `S³`, and base `S²` fixed definitionally. |
| Hopf LES comparison for second homotopy groups | [`src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md) | Proves the right-hand boundary/fiber-inclusion exactness statement for the lower Hopf segment, the left fibration-boundary exactness statement by applying `is-exact-set-truncation-loop-fiber-sequence` to `fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type` instantiated at the Hopf fiber sequence, and the algebraic extraction identifying `π₂(S²)` with `π₁(S¹)` from the two exactness statements and the checked trivial outer `S³` groups. |
| Hopf LES comparison for third homotopy groups | [`src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md) | Builds the Hopf comparison isomorphism from the Hopf fibration homomorphism, the checked total-space exactness theorem, the new direct fibration-boundary exactness theorem for the second shifted segment, and the two trivial endpoint hypotheses. The exactness proof no longer uses triviality of `π₂(S¹)` as a shortcut. |
| Hopf comparison for third homotopy groups | [`src/synthetic-homotopy-theory/hopf-fibration-third-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/hopf-fibration-third-homotopy-groups.lagda.md) | Delegates `π₃(S³) ≅ π₃(S²)` to the Hopf LES comparison scaffold and has no direct proof hole. |
| Stability comparison for `π₃(S³)` | [`src/synthetic-homotopy-theory/stability-third-homotopy-group-sphere-3.lagda.md`](src/synthetic-homotopy-theory/stability-third-homotopy-group-sphere-3.lagda.md) | Records the unfinished stability comparison `π₂(S²) ≅ π₃(S³)`. |
| Second homotopy group of `S²` | [`src/synthetic-homotopy-theory/second-homotopy-group-sphere-2.lagda.md`](src/synthetic-homotopy-theory/second-homotopy-group-sphere-2.lagda.md) | Proves the Hopf-derived comparison `π₂(S²) ≅ π₁(S¹)` by instantiating the lower Hopf exactness-to-isomorphism wrapper with the checked direct-connecting-fiber-sequence set-level exactness. It has no local `--allow-unsolved-metas`. |
| Fundamental group of `S¹` | [`src/synthetic-homotopy-theory/fundamental-group-sphere-1.lagda.md`](src/synthetic-homotopy-theory/fundamental-group-sphere-1.lagda.md) | Proves the checked group isomorphism from the concrete fundamental group of `S¹` to `ℤ-Group`, with no unsolved metas or scaffold holes. |
| Third homotopy group of the 3-sphere | [`src/synthetic-homotopy-theory/third-homotopy-group-sphere-3.lagda.md`](src/synthetic-homotopy-theory/third-homotopy-group-sphere-3.lagda.md) | Delegates `π₃(S³) ≅ ℤ` to the stability scaffold, the checked `π₂(S²) ≅ π₁(S¹)` comparison, and the checked `π₁(S¹) ≅ ℤ` calculation, and has no direct proof hole. |
| Final theorem target | [`src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md`](src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md) | Records the pinned top-level statement `π₃(S²) ≅ ℤ` and proves it formally from the inverse Hopf-comparison stub and the `π₃(S³) ≅ ℤ` stub. The proof is therefore structurally assembled but depends on unfinished imported stubs. |

## Status against the formalization plan

| Plan item | Status | Notes |
|---|---|---|
| General pointed fiber sequences | Done | Implemented in [`src/structured-types/fiber-sequences.lagda.md`](src/structured-types/fiber-sequences.lagda.md). |
| Induced maps on homotopy groups | Done | Implemented via iterated loop functoriality and concrete homotopy group functoriality. |
| Long exact sequence of homotopy groups | Partial | Boundary maps, induced homomorphisms, pointed-set exactness, exactness of the set truncation of canonical and packaged `F ->* E ->* B` triples, exactness of the packaged boundary triple `Ω B ->* F ->* E`, exactness of the packaged loop-boundary triple `Ω E ->* Ω B ->* F`, exactness of the looped packaged triple `Ω F ->* Ω E ->* Ω B`, the first fiber-of-the-fiber identification `Ω B ≃* fiber (fiber g -> E)`, pointed-set exactness of the canonical triples `Ω B ->* fiber g ->* E`, `Ω E ->* Ω B ->* fiber g`, and `Ω² B ->* Ω (fiber g) ->* Ω E`, transported exactness of the packaged looped boundary/fiber-inclusion triple `Ω² B ->* Ω F ->* Ω E`, and a bundled initial four-triple set-truncated LES segment are formalized. The group-exactness transport layer is checked for the total-space case, for the boundary/fiber-inclusion case at `π₁(F)`, for fibration-boundary targets whose codomain group is contractible, and for unrestricted direct fibration-boundary segments in all indices. The set-truncated iterated total-space theorem, the canonical shifted boundary theorem, the direct-indexed shifted-boundary exactness theorem, the reassociated public shifted-boundary exactness theorem for all indices, the type-level and induced-map reassociation equalities, and the packaged shifted-boundary pointwise comparison are checked. The classifying-map fiber-sequence route is recorded as too strong in general. |
| Exactness-to-isomorphism with zero endpoints | Done | Proved in [`src/group-theory/isomorphisms-from-exact-sequences-groups.lagda.md`](src/group-theory/isomorphisms-from-exact-sequences-groups.lagda.md). |
| Higher homotopy groups of the circle vanish | Mostly done | Positive concrete homotopy groups of the circle and 1-sphere are trivial. Further packaging may be needed for the exact Hopf LES endpoints. |
| Loop space of the circle is the integers | Done | The loop-space equivalence is formalized, the universal-cover encoder is proved additive on loop concatenation, the result is transferred to the 1-sphere, and the concrete group isomorphism `π₁(S¹) ≅ ℤ` is checked. |
| Circle as an H-space | Done | The checked module [`src/synthetic-homotopy-theory/h-space-structure-circle.lagda.md`](src/synthetic-homotopy-theory/h-space-structure-circle.lagda.md) packages both `𝕊¹-H-Space` and the transported `sphere-1-H-Space`, and proves that circle and 1-sphere translations are equivalences. |
| Hopf construction and Hopf fibration | Partial | The generic Hopf map `A * A -> suspension A`, the `S¹ * S¹ ->* S²` specialization, the canonical Hopf-construction source fiber sequence, the Hopf family over `S²`, the Hopf-family projection fiber sequence with fiber `S¹`, the Hopf shear equivalence on `S¹ × S¹`, the proof that the actual Hopf-family total space is a pushout of the family-induced flattened span, the proof that `S¹ * S¹` is a pushout of the explicit flattened Hopf-family descent span, the completed two-leg comparison between these flattened spans, the canonical equivalence `total-space-hopf-family-sphere-1 ≃ S¹ * S¹`, the comparison `Fin 2 * X ≃ suspension X`, join functoriality under equivalences, join commutativity, the structural associator and inverse-direction associator maps for joins, the bridge from `S¹ * S¹` to the join of two `join-power 2 (Fin 2)` models, the composed comparisons from both Hopf total-space models to `join-power 2 (Fin 2) * join-power 2 (Fin 2)`, the structural map onward to `join-power 4 (Fin 2)`, and the reduction of that map's equivalence proof to the associator equivalence proof are checked. The packaged Hopf fiber sequence target `S^1 -> S^3 -> S^2` is still stubbed pending proof that the associator map is an equivalence, transport to the `S³` model, and packaging of the final fiber-sequence proof. |
| Hopf LES consequence `pi_3(S^3) = pi_3(S^2)` | Partially proved | The exactness-to-isomorphism extraction and Hopf LES packaging are proved, and the fibration-boundary exactness now uses the direct checked second shifted boundary theorem rather than the trivial-codomain shortcut. The comparison still depends on the unfinished Hopf fiber sequence scaffold. |
| Freudenthal suspension theorem | Not started | Still a major missing theorem. |
| Stability of homotopy groups of spheres | Instance stubbed | The needed comparison `π₂(S²) ≅ π₃(S³)` is recorded as an unfinished theorem depending on Freudenthal/stability. |
| Diagonal theorem `pi_n(S^n) = Z` | Reduced to lower stubs | The `n = 3` file now composes the stability scaffold, the checked `π₂(S²) ≅ π₁(S¹)` comparison, and the checked `π₁(S¹) ≅ ℤ` calculation. The general theorem remains unproved. |
| Final theorem `pi_3(S^2) = Z` | Assembled from stubs | The target statement in [`src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md`](src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md) is now a formal composition of the two next-level stubs. It has no direct proof hole but remains mathematically unfinished until those imported stubs are proved. |

## Remaining tasks

1. Extend the checked Hopf map `S¹ * S¹ ->* S²` to the Hopf fiber sequence
   `S^1 -> S^3 -> S^2`. The circle translation equivalences, Hopf family over
   `S²`, Hopf-family projection fiber sequence, Hopf shear equivalence on
   `S¹ × S¹`, actual-family flattening pushout, explicit flattened-span
   pushout comparison with `S¹ * S¹`, suspension-as-join layer,
   sphere-as-join-power layer, join functoriality under equivalences, join
   commutativity, and the bridge from `S¹ * S¹` to
   `join-power 2 (Fin 2) * join-power 2 (Fin 2)`, the two-leg flattened-span
   comparison, the canonical equivalence
   `total-space-hopf-family-sphere-1 ≃ S¹ * S¹`, and the composed comparisons
   from the Hopf-family and Hopf-construction total spaces to
   `join-power 2 (Fin 2) * join-power 2 (Fin 2)` are checked, and there is now
   a checked structural map from that join to `join-power 4 (Fin 2)`, together
   with a checked proof that this structural map is an equivalence assuming the
   two relevant associator instances are equivalences. The remaining Hopf work
   is to prove the associator inverse homotopies or universal property,
   transport the total-space comparison to the `S³` model, and then
   transport/package the result as the final
   `S^1 -> S^3 -> S^2` fiber sequence.
2. Prove the stability comparison `π₂(S²) ≅ π₃(S³)` from Freudenthal and sphere
   stability.
3. Recheck `π₃(S³) ≅ ℤ` and `π₃(S²) ≅ ℤ` after their imported lower stubs are
   proved; their proof bodies should remain short compositions.

## Next agent handoff

The arbitrary-index LES bridge is complete. The circle/1-sphere H-space input and translation equivalences are checked in `src/synthetic-homotopy-theory/h-space-structure-circle.lagda.md`. The generic Hopf map is checked in `src/synthetic-homotopy-theory/hopf-construction.lagda.md`, the sphere-1 specialization is checked in `src/synthetic-homotopy-theory/hopf-construction-circle.lagda.md`, the canonical Hopf-construction source sequence is checked in `src/synthetic-homotopy-theory/hopf-construction-fiber-sequence.lagda.md`, and the Hopf family over `S²` is checked in `src/synthetic-homotopy-theory/hopf-family-circle.lagda.md`, including the pointed fiber sequence given by projecting its total space to `S²`, the flattening-lemma pushout for its actual total space, the proof that `S¹ * S¹` is a pushout of the explicit flattened Hopf-family descent span, the completed two-leg comparison between those flattened spans, the canonical equivalence `total-space-hopf-family-sphere-1 ≃ S¹ * S¹`, and the composed comparison of the Hopf-family total space with `join-power 2 (Fin 2) * join-power 2 (Fin 2)`.

The next upstream-shaped target is to turn the checked pointed Hopf map `S¹ * S¹ ->* S²` into the packaged Hopf fiber sequence. The structural route now has one main total-space comparison target: prove the checked join associator map `((A * B) * C) -> A * (B * C)` is an equivalence, using either the checked inverse-direction map or a universal-property proof. The checked lemma in `spheres-as-join-powers` then turns the resulting associator equivalence instances into the equivalence of `join-power 2 (Fin 2) * join-power 2 (Fin 2) -> join-power 4 (Fin 2)`. After that, compose with the checked `S¹ * S¹` and `join-power 4 (Fin 2) ≃ S³` comparisons, transport the Hopf map across the `S³` comparison as needed, and fill `src/synthetic-homotopy-theory/hopf-fiber-sequence.lagda.md` with the actual pointed maps and fiber-sequence proof.

Expected verification for this next step should start with:

```sh
./check.sh src/synthetic-homotopy-theory/h-space-structure-circle.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-construction.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-construction-circle.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-family-circle.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-fiber-sequence.lagda.md
```

Once the Hopf scaffold is closed, recheck the Hopf LES second and third segment files before moving to the Freudenthal/stability scaffold.

## Current verification

Later on 2026-06-22, the flattened Hopf-family span comparison was completed
and the family total space was compared with the join:

```sh
./check.sh src/synthetic-homotopy-theory/hopf-family-circle.lagda.md
./check.sh src/synthetic-homotopy-theory/spheres-as-join-powers.lagda.md
```

Both checks passed. The new checked layer proves the right-leg meridian
coherence between the family-induced flattened span and the explicit flattened
descent span, inverts the span comparison to transport the total-space pushout
property to the explicit span, and packages the canonical equivalence
`total-space-hopf-family-sphere-1 ≃ S¹ * S¹`. The remaining total-space
comparison is now the associator equivalence proof. Both directions of the
structural associator map have checked cocones/maps, and the join-power
multiplication equivalence has been reduced to the two relevant associator
equivalence instances.

Later on 2026-06-22, the first span-comparison data between the actual
Hopf-family flattening span and the explicit flattened descent span was added
and checked with:

```sh
./check.sh src/synthetic-homotopy-theory/hopf-family-circle.lagda.md
```

The check passed. The new checked layer names the three vertex equivalences
between the family-induced flattened span and the explicit flattened descent
span, and proves the left-leg comparison square by reflexivity. The right-leg
meridian coherence remains.

Later on 2026-06-22, the actual Hopf-family total-space pushout supplied by
the flattening lemma was added and checked with:

```sh
./check.sh src/synthetic-homotopy-theory/hopf-family-circle.lagda.md
```

The check passed. The new checked layer names the family-induced flattened
span, its cocone into `total-space-hopf-family-sphere-1`, and the universal
property showing that this cocone is a pushout.

Later on 2026-06-22, the flattened Hopf-family descent span was compared with
the standard join span and checked with:

```sh
./check.sh src/synthetic-homotopy-theory/hopf-family-circle.lagda.md
```

The check passed. The new checked layer names the Hopf-family descent data over
the suspension span, forms its flattened descent span, and proves that
`S¹ * S¹` satisfies the pushout universal property for that span via the unit
vertex equivalences and the Hopf shear.

Later on 2026-06-22, the Hopf shear equivalence on `S¹ × S¹` was added and
checked with:

```sh
./check.sh src/synthetic-homotopy-theory/h-space-structure-circle.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-family-circle.lagda.md
```

Both checks passed. The new checked layer packages the equivalence
`(x , y) ↦ (y , x · y)`, which is the span-equivalence ingredient needed to
compare the flattened Hopf-family descent span with the standard join span.

Later on 2026-06-22, the Hopf-family projection was packaged as a pointed
fiber sequence and checked with:

```sh
./check.sh src/synthetic-homotopy-theory/hopf-family-circle.lagda.md
```

The check passed. The new checked layer identifies the north fiber of the
projection from the Hopf-family total space with `sphere 1` and packages the
projection as `fiber-sequence-hopf-family-sphere-1`.

On 2026-06-22, the Hopf-family input was added and checked with:

```sh
./check.sh src/synthetic-homotopy-theory/h-space-structure-circle.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-family-circle.lagda.md
```

Both passed. The new checked layer proves circle and 1-sphere translation
equivalences and defines the Hopf family over `S²` using the univalent paths
classified by left multiplication on `S¹`.

On 2026-06-21, the lower Hopf comparison was closed by the direct connecting
fiber-sequence route and checked with:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/second-homotopy-group-sphere-2.lagda.md
```

All passed. The `second-homotopy-group-sphere-2` file no longer uses a local
`--allow-unsolved-metas`, and its Hopf-derived comparison
`π₂(S²) ≅ π₁(S¹)` has a checked proof body.

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


Later on 2026-06-21, the shifted loop-boundary exactness layer was advanced one step further. The long exact sequence file now records the direct shifted hom and exactness theorem

```text
hom-trunc-boundary-boundary-fiber-sequence-direct-Pointed-Type
is-exact-set-truncation-loop-boundary-boundary-fiber-sequence-direct
```

For a packaged fiber sequence `S : F ->* E ->* B`, this applies the generic set-truncated loop-boundary exactness theorem to the checked direct shifted fiber sequence

```text
fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type S
```

and therefore proves the canonical exactness of the shifted adjacent triple

```text
OmegaOmega B -> Omega F -> Omega E
```

where the second map is the boundary map of the direct shifted sequence `Omega E ->* Omega B ->* F`. The existing recursive loop-boundary exactness theorem is still checked through the canonical-fiber transport bridge. An exploratory attempt to replace it by direct homotopy invariance exposed the remaining upstream-quality comparison: identify the direct shifted boundary with `pointed-map-Ω (fiber-inclusion-fiber-sequence-Pointed-Type S)` by a K-safe inverse computation for the direct boundary-fiber equivalence. The failed direct comparison was removed, so the file remains fully checked.

The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed. `git diff --check` passed, and the touched LES file contains no holes, postulates, or `--allow-unsolved-metas`.


Later on 2026-06-21, the looped packaged fiber-sequence exactness segment was upgraded to the structural iterated-loop route. The long exact sequence file now defines

```text
is-exact-set-truncation-loop-fiber-sequence-direct
```

by applying the generic packaged fiber-sequence exactness theorem to

```text
iterated-loop-fiber-sequence S (succ-ℕ zero-ℕ)
```

and the public theorem

```text
is-exact-set-truncation-loop-fiber-sequence
```

is now just this direct structural proof. The previous hand-built proof at `Omega E`, together with its bespoke kernel/image conversions and explicit loop-fiber comparison helpers, was removed. This keeps the set-truncated exactness layer aligned with the intended upstream proof: adjacent triples are exact because they are packaged fiber sequences, not because each adjacent image/kernel comparison is reconstructed locally.

The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed. `git diff --check` passed, and the touched LES file contains no holes, postulates, or `--allow-unsolved-metas`. The remaining hard target is still the K-safe comparison identifying the direct shifted boundary with `pointed-map-Ω (fiber-inclusion-fiber-sequence-Pointed-Type S)`, which would let the recursive shifted boundary theorem collapse onto the direct route.


Later on 2026-06-21, the direct shifted-boundary comparison target gained a checked first-projection foothold. The long exact sequence file now records K-safe loop-nullity computations for the canonical fiber and packaged fiber-sequence composites, together with first-projection comparisons

```text
eq-map-Ω-inclusion-fiber-Pointed-Type
eq-pr1-map-equiv-fiber-boundary-map-Ω-direct-loop-inclusion-fiber-Pointed-Type
eq-map-Ω-fibration-map-Ω-fiber-inclusion-fiber-sequence-Pointed-Type
eq-pr1-map-equiv-fiber-boundary-fiber-sequence-direct-loop-fiber-inclusion
```

These lemmas prove that the raw and packaged direct shifted boundary comparison has the expected underlying point in the target fiber. The remaining hard target is the second component of the equality in the fiber: real Agda rejected the naive `right-unit` proof because this is a higher path in a fiber, so the upstreamable comparison still needs a coherent K-safe path-algebra proof rather than a definitional shortcut.

The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed. `git diff --check` passed, and the touched LES file contains no holes, postulates, or `--allow-unsolved-metas`.


Later on 2026-06-21, the shifted-boundary comparison gained a second checked helper layer for the inverse-side route. The long exact sequence file now records boundary-basepoint path algebra for the direct boundary map:

```text
eq-inv-preserves-point-boundary-fiber-concat-loop-Pointed-Type
eq-ap-pr1-preserves-point-boundary-fiber-Pointed-Type
eq-ap-pr1-preserves-point-boundary-fiber-concat-loop-Pointed-Type
```

These lemmas show that the boundary basepoint path cancels before a loop in the fiber, that its first projection is reflexivity, and that the first projection of `preserves-point boundary ∙ q` is exactly `map-Ω` of the fiber inclusion on `q`. This converts part of the remaining direct shifted-boundary comparison into a checked inverse-side computation and avoids the rejected `--without-K` loop pattern split.

The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed. `git diff --check` passed, and the touched LES file contains no holes, postulates, or `--allow-unsolved-metas`.


Later on 2026-06-21, the raw shifted-boundary inverse computation was made explicit. The long exact sequence file now proves

```text
eq-map-inv-fiber-boundary-map-Ω-boundary-boundary-Pointed-Type
```

For a pointed map `g` and a loop `q` in its fiber, the hand inverse `map-inv-fiber-boundary-map-Ω-Pointed-Type g` sends the boundary-of-boundary element to `map-Ω (inclusion-fiber-Pointed-Type g) q`. This is the inverse-side computation needed before comparing the direct equivalence inverse with the hand inverse, and it was proved from the checked boundary-basepoint first-projection algebra.

The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed. `git diff --check` passed, and the touched LES file contains no holes, postulates, or `--allow-unsolved-metas`.


Later on 2026-06-21, a structural wrapper in the direct boundary equivalence was computed away. The long exact sequence file now records

```text
compute-map-equiv-equiv-ap-refl
compute-equiv-eq-map-Ω-eq-ap-refl-Pointed-Type
```

The first lemma says that `equiv-ap` of an equivalence sends reflexivity to reflexivity. The second applies this to the loop-map comparison equivalence, showing that `equiv-eq-map-Ω-eq-ap-Pointed-Type p (map-Ω g p)` sends `refl` to the canonical path `eq-ap-map-Ω-Pointed-Type p`. This removes one structural wrapper from the second-component comparison between the direct equivalence and the hand boundary-fiber map.

The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed. `git diff --check` passed, and the touched LES file contains no holes, postulates, or `--allow-unsolved-metas`.


Later on 2026-06-21, the direct boundary equivalence was compared with the hand boundary-fiber map. The long exact sequence file now records

```text
compute-equiv-fiber-map-Ω-boundary-map-Ω-map-fiber-boundary-Pointed-Type
eq-map-equiv-fiber-boundary-map-Ω-direct-map-fiber-boundary-Pointed-Type
```

The first lemma computes the `inv-equiv-total-fiber`/`fiber-ap` wrapper on the canonical point `(p , refl)`, using the previously checked `equiv-ap` reflexivity computation. The second lemma packages this into the forward-map comparison: `equiv-fiber-boundary-map-Ω-direct-Pointed-Type` sends a loop `p` to the same fiber element as the hand-built `map-fiber-boundary-map-Ω-Pointed-Type`. This is a stronger foothold for the shifted-boundary comparison because the remaining raw equality can now be attacked at the hand-map/hand-inverse level rather than under the structural equivalence wrappers.

The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed. `git diff --check` passed, and the touched LES file contains no holes, postulates, or `--allow-unsolved-metas`.


Later on 2026-06-21, the hand boundary-fiber map was registered as an equivalence by comparison with the direct structural equivalence. The long exact sequence file now records

```text
is-equiv-map-fiber-boundary-map-Ω-Pointed-Type
equiv-map-fiber-boundary-map-Ω-Pointed-Type
```

The proof uses `is-equiv-htpy-equiv` and the checked forward-map comparison between `equiv-fiber-boundary-map-Ω-direct-Pointed-Type` and `map-fiber-boundary-map-Ω-Pointed-Type`. This avoids expanding the large second-component section path for the hand inverse directly. The failed direct section attempt showed that path induction on the boundary fiber path is blocked by `--without-K`; the equivalence-transfer route is cleaner and better aligned with an upstreamable proof.

The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed. `git diff --check` passed, and the touched LES file contains no holes, question-mark metas, postulates, or `--allow-unsolved-metas`.


Later on 2026-06-21, the hand inverse for the boundary-fiber map gained a checked two-sided inverse law by inverse uniqueness. The long exact sequence file now records

```text
is-equiv-map-inv-fiber-boundary-map-Ω-Pointed-Type
equiv-map-inv-fiber-boundary-map-Ω-Pointed-Type
is-section-map-inv-fiber-boundary-map-Ω-Pointed-Type
```

The proof first observes that `map-inv-fiber-boundary-map-Ω-Pointed-Type` is a retraction of the now-checked equivalence `map-fiber-boundary-map-Ω-Pointed-Type`, hence is itself an equivalence by `is-equiv-is-retraction`. The missing section is then obtained from `htpy-map-inv-equiv-section` and `is-retraction-map-inv-equiv` for the packaged inverse equivalence. This clears the previous section block without expanding the large `fiber-ap-eq-fiber` naturality equation and keeps the construction compatible with `--without-K`.

The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed. `git diff --check` passed, and the touched LES file contains no holes, question-mark metas, postulates, or `--allow-unsolved-metas`.


Later on 2026-06-21, the raw shifted-boundary comparison was proved. The long exact sequence file now records

```text
eq-map-equiv-fiber-boundary-map-Ω-direct-loop-inclusion-fiber-Pointed-Type
```

For a pointed map `g` and a loop `q` in its fiber, this lemma identifies the direct boundary equivalence applied to `map-Ω (inclusion-fiber-Pointed-Type g) q` with the boundary-of-boundary map `boundary-fiber-Pointed-Type (boundary-fiber-Pointed-Type g) q`. The proof is the intended three-step route: use the checked direct-to-hand forward-map comparison, rewrite by the inverse-side boundary-of-boundary computation, and finish with the section of the hand inverse obtained by equivalence uniqueness. This clears the raw hard target without the rejected `--without-K` path split and without expanding the large `fiber-ap-eq-fiber` coherence.

The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed. `git diff --check` passed, and the touched LES file contains no holes, question-mark metas, postulates, or `--allow-unsolved-metas`.


Later on 2026-06-21, a generic pointed-equivalence loop retraction helper was added as a packaged-lift ingredient. The long exact sequence file now records

```text
is-retraction-map-Ω-pointed-map-inv-pointed-equiv
```

For a pointed equivalence `e`, this proves that `map-Ω (pointed-map-inv-pointed-equiv e)` retracts `map-Ω (pointed-map-pointed-equiv e)`. The proof uses the existing pointed homotopy `pointed-htpy-Ω-inv-pointed-equiv` to compare `Ω(inv e)` with the inverse of the loop equivalence, then applies `is-retraction-map-inv-equiv (equiv-Ω-pointed-equiv e)`. This is the first-projection ingredient needed for the packaged canonical fiber comparison after the raw shifted-boundary theorem.

The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed. `git diff --check` passed, and the touched LES file contains no holes, question-mark metas, postulates, or `--allow-unsolved-metas`.


Later on 2026-06-21, the raw shifted-boundary theorem was lifted into the packaged fiber-sequence comparison layer. The long exact sequence file now records

```text
eq-map-Ω-fiber-inclusion-map-Ω-pointed-map-fiber-fiber-sequence-Pointed-Type
eq-map-equiv-fiber-boundary-map-Ω-direct-loop-fiber-inclusion-fiber-sequence-Pointed-Type
eq-map-equiv-fiber-boundary-fiber-sequence-direct-loop-fiber-inclusion-canonical-Pointed-Type
```

The first lemma compares the loop of the packaged fiber inclusion with the loop of the canonical fiber inclusion composite through `pointed-map-fiber-fiber-sequence-Pointed-Type`. The second applies the checked raw shifted-boundary theorem to the packaged fiber inclusion. The third lifts that equality through `equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type`, so the packaged direct boundary equivalence is now reduced to the canonical boundary-boundary target on loops from the fiber fiber sequence. This is the intended upstreamable route toward the `connect_fiberseq` analogue; the remaining hard step is the second-component comparison identifying the canonical boundary-boundary target with `boundary-fiber-Pointed-Type (boundary-pointed-map-fiber-sequence S)`.

The checked command was:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

The check passed. `git diff --check` passed, and the touched LES file contains no holes, question-mark metas, postulates, or `--allow-unsolved-metas`.


Later on 2026-06-21, the lower Hopf base comparison was closed using the already checked direct connecting fiber sequence. The lower Hopf module now records

```text
is-exact-set-truncation-second-homotopy-hopf-fibration-boundary
```

This proves the recursive set-truncated exactness input for
`π₂(S³) -> π₂(S²) -> π₁(S¹)` by applying
`is-exact-set-truncation-loop-fiber-sequence` to
`fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type` instantiated at the
Hopf fiber sequence. The proof is structural: it loops the packaged direct
sequence `Ω S³ ->* Ω S² ->* S¹` rather than comparing images and kernels by a
local shortcut.

The second homotopy group file now consumes this theorem directly:

```text
iso-second-homotopy-group-sphere-2-fundamental-group-sphere-1
```

The local `--allow-unsolved-metas` pragma was removed from
`second-homotopy-group-sphere-2.lagda.md`, and the previous hole was filled with
`is-exact-set-truncation-second-homotopy-hopf-fibration-boundary`.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/second-homotopy-group-sphere-2.lagda.md
./check.sh src/synthetic-homotopy-theory/third-homotopy-group-sphere-3.lagda.md
./check.sh src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md
git diff --check
rg -n "\{!!\}|allow-unsolved-metas|postulate" src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md src/synthetic-homotopy-theory/second-homotopy-group-sphere-2.lagda.md
rg -n "allow-unsolved-metas|\{!!\}" src/synthetic-homotopy-theory src/group-theory src/structured-types -g "*.lagda.md"
```

All Agda checks passed. `git diff --check` passed. The touched-file scan found no holes, postulates, or local `--allow-unsolved-metas`; the broader scaffold scan found only the expected Hopf fiber sequence and stability comparison holes.


Later on 2026-06-21, the packaged shifted-boundary comparison gained the checked first-projection theorem

```text
eq-pr1-map-equiv-fiber-canonical-boundary-boundary-fiber-sequence-boundary-boundary
```

For a loop `q` in the packaged fiber `F`, this compares the first projection of the canonical boundary-boundary target after applying `equiv-fiber-canonical-boundary-boundary-fiber-sequence-Pointed-Type` with the first projection of the recursive boundary map `boundary-fiber-Pointed-Type (boundary-pointed-map-fiber-sequence S) q`. The proof composes the inverse of the existing full lifted equality

```text
eq-map-equiv-fiber-boundary-fiber-sequence-direct-loop-fiber-inclusion-canonical-Pointed-Type
```

with the earlier direct first-projection comparison

```text
eq-pr1-map-equiv-fiber-boundary-fiber-sequence-direct-loop-fiber-inclusion
```

This is the correct base path for the remaining dependent second-component proof. A temporary probe of that second component was removed after real Agda showed that the residual is not a definitional `refl`/`right-unit` proof; it requires controlling `ap (map-pointed-map (boundary-pointed-map-fiber-sequence S))` on the composed first-projection path.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
git diff --check
rg -n "\{!!\}|allow-unsolved-metas|postulate" src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
rg -n "allow-unsolved-metas|\{!!\}" src/synthetic-homotopy-theory src/group-theory src/structured-types -g "*.lagda.md"
```

The Agda check passed. `git diff --check` passed. The touched-file scan found no holes, postulates, or local `--allow-unsolved-metas`; the broader scaffold scan found only the expected Hopf fiber sequence and stability comparison holes.


Later on 2026-06-21, the Hopf third-homotopy fibration-boundary exactness was rerouted through direct shifted exactness rather than the trivial-codomain shortcut. The set-truncated iterated exactness file now records

```text
is-exact-set-truncation-first-iterated-loop-fibration-boundary-fiber-sequence-direct
is-exact-set-truncation-second-iterated-loop-fibration-boundary-fiber-sequence-direct
```

These theorems apply the direct connecting fiber sequence `Ω E ->* Ω B ->* F` and its first iterated loop sequence to obtain recursive fibration-boundary exactness for the first two shifted segments. The attempted arbitrary-index direct theorem exposed a real iterated-loop reassociation issue: the direct sequence naturally gives `Ω^n(Ω X)`, while the public homotopy-group interface is phrased with `Ω^(n+1) X`. That general theorem now has a precise remaining target: prove functorial reassociation for iterated loop spaces and induced maps.

The group exactness file now records

```text
is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-second-direct
```

and the Hopf third-homotopy LES file now uses it for

```text
is-exact-third-homotopy-hopf-fibration-boundary
```

Thus the Hopf `π₃(S³) -> π₃(S²) -> π₂(S¹)` exactness segment no longer uses triviality of `π₂(S¹)` to prove exactness; triviality of the outer Hopf groups is still used only in the final exactness-to-isomorphism extraction.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md
git diff --check
rg -n "\{!!\}|allow-unsolved-metas|postulate" src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
rg -n "allow-unsolved-metas|\{!!\}" src/synthetic-homotopy-theory src/group-theory src/structured-types -g "*.lagda.md"
```

All Agda checks passed. `git diff --check` passed. The touched-file scan found no holes, postulates, or local `--allow-unsolved-metas`; the broader scaffold scan found only the expected Hopf fiber sequence and stability comparison holes.


Later on 2026-06-21, the direct shifted exactness theorem was generalized in its natural indexing. The set-truncated iterated exactness file now records the direct-indexed homomorphisms

```text
hom-trunc-direct-iterated-loop-fibration-fiber-sequence
hom-trunc-direct-iterated-loop-boundary-fiber-sequence
```

and the all-iterates direct exactness theorem

```text
is-exact-set-truncation-direct-iterated-loop-fibration-boundary-fiber-sequence
```

For a packaged fiber sequence `F ->* E ->* B`, this proves exactness for every iterate of the direct shifted connecting sequence in the form

```text
Ω Ω^n(Ω E) -> Ω Ω^n(Ω B) -> Ω Ω^n F.
```

The two public finite shifted theorems used by the lower and third Hopf segments are now just the `0` and `1` instances of this direct-indexed theorem.

A new one-concept module

```text
synthetic-homotopy-theory.reassociation-iterated-loop-spaces
```

was added with checked type-level reassociation lemmas

```text
reassociate-succ-iterated-loop-space
inv-reassociate-succ-iterated-loop-space
reassociate-Ω-succ-iterated-loop-space
inv-reassociate-Ω-succ-iterated-loop-space
```

These identify `Ω^(n+1) X` with `Ω^n(Ω X)` at the pointed-type level. A probe of the induced-map compatibility theorem was removed after raw Agda rejected the natural rewrite/with proof: the successor case requires an explicit transport-through-`Ω` computation rather than a direct `refl` after splitting `ap Ω` of the reassociation path.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/reassociation-iterated-loop-spaces.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md
```

All four Agda checks passed. `git diff --check` passed. The touched-file scan found no holes, postulates, or local `--allow-unsolved-metas`; the broader scaffold scan found only the expected Hopf fiber sequence and stability comparison holes. The next precise LES bridge target is the induced-map reassociation/transport theorem comparing `pointed-map-iterated-loop-space (succ-ℕ n) f` with `pointed-map-iterated-loop-space n (pointed-map-Ω f)` through the checked pointed-type reassociation paths.


Later on 2026-06-21, the arbitrary-index direct fibration-boundary bridge was completed. The reusable transport layer now includes

```text
tr-hom-trunc-Pointed-Set
is-exact-hom-Pointed-Set-tr
```

for transporting set-truncated pointed maps and pointed-set exactness along identified source, middle, and target pointed sets. The reassociation module now proves transport-through-loop functoriality and induced-map reassociation:

```text
tr-pointed-map-Ω
reassociate-pointed-map-iterated-loop-space
reassociate-Ω-pointed-map-iterated-loop-space
```

The long exact sequence file now proves the boundary-specific recursive/direct reassociation lemmas

```text
reassociate-pointed-map-iterated-boundary-fiber-sequence
reassociate-Ω-pointed-map-iterated-boundary-fiber-sequence
```

Using these, the set-truncated iterated exactness file proves the public all-index direct theorem

```text
is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-direct
```

for every `n`, in the public `Ω^(n+1) X` indexing. The group-level exactness file lifts this to

```text
is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-direct
```

so the previous second-shifted Hopf exactness theorem is now just the `n = 1` instance of an unrestricted direct fibration-boundary group exactness theorem.

The checked commands were:

```sh
./check.sh src/structured-types/pointed-sets.lagda.md
./check.sh src/structured-types/exact-sequences-pointed-sets.lagda.md
./check.sh src/synthetic-homotopy-theory/reassociation-iterated-loop-spaces.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md
```

All Agda checks passed. `git diff --check` passed. The touched-file scan found no holes, postulates, or local `--allow-unsolved-metas`; the broader scaffold scan found only the expected Hopf fiber sequence and stability comparison holes. The next major mathematical blockers are the Hopf fiber sequence scaffold and the Freudenthal/stability comparison scaffold.


Later on 2026-06-21, the circle H-space prerequisite and first Hopf-construction layer were checked. The new module

```text
synthetic-homotopy-theory.h-space-structure-circle
```

packages the existing circle multiplication as a coherent `𝕊¹-H-Space`, transports it across the circle--1-sphere equivalence, and packages the result as `sphere-1-H-Space`. The new generic module

```text
synthetic-homotopy-theory.hopf-construction
```

defines the Hopf total space `A * A`, the base `suspension A`, the Hopf cocone, the Hopf map, and its pointed form for any H-space. The specialization

```text
synthetic-homotopy-theory.hopf-construction-circle
```

instantiates this construction at `sphere-1-H-Space`, yielding the checked pointed Hopf map `S¹ * S¹ ->* S²`.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/h-space-structure-circle.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-construction.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-construction-circle.lagda.md
git diff --check
rg -n "\{!!\}|allow-unsolved-metas|postulate" src/synthetic-homotopy-theory/h-space-structure-circle.lagda.md src/synthetic-homotopy-theory/hopf-construction.lagda.md src/synthetic-homotopy-theory/hopf-construction-circle.lagda.md
rg -n "allow-unsolved-metas|\{!!\}" src/synthetic-homotopy-theory src/group-theory src/structured-types -g "*.lagda.md"
```

All three Agda checks passed. `git diff --check` passed. The touched-file scan found no holes, postulates, or local `--allow-unsolved-metas`; the broader scaffold scan still found only the expected Hopf fiber sequence and Freudenthal/stability comparison holes. The next Hopf target is the total-space comparison `S¹ * S¹ ≃ S³` and the packaged fiber-sequence proof using the checked pointed Hopf map.


Later on 2026-06-21, the Hopf-construction source fiber sequence and the first total-space comparison layer were checked. The new module

```text
synthetic-homotopy-theory.hopf-construction-fiber-sequence
```

packages the canonical fiber sequence of the generic Hopf-construction pointed map. For `sphere-1-H-Space`, this gives a checked source fiber sequence whose fiber is the pointed fiber of `S^1 * S^1 ->* S^2`, total space is the Hopf-construction total space, and base is `S^2`. This is the structural object to compare with the desired geometric Hopf fiber sequence.

The new module

```text
synthetic-homotopy-theory.suspensions-as-joins
```

defines the two comparison maps

```text
Fin 2 * X -> suspension X
suspension X -> Fin 2 * X
```

and checked computation rules on the two `Fin 2` endpoints, the right copy of `X`, and the suspension meridians. A probe of the section law was removed after MCP exposed that the meridian case expands to a large dependent-transport coherence; the next proof should package a reusable helper for this suspension/join computation rather than inline the expanded transport.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/hopf-construction-fiber-sequence.lagda.md
./check.sh src/synthetic-homotopy-theory/suspensions-as-joins.lagda.md
git diff --check
rg -n "\{!!\}|allow-unsolved-metas|postulate" src/synthetic-homotopy-theory/hopf-construction-fiber-sequence.lagda.md src/synthetic-homotopy-theory/suspensions-as-joins.lagda.md
rg -n "allow-unsolved-metas|\{!!\}" src/synthetic-homotopy-theory src/group-theory src/structured-types -g "*.lagda.md"
```

Both Agda checks passed. `git diff --check` passed. The touched-file scan found no holes, postulates, or local `--allow-unsolved-metas`; the broader scaffold scan found only the expected Hopf fiber sequence and Freudenthal/stability comparison holes. The Hopf fibration scaffold and Freudenthal/stability scaffold remain the only expected unfinished Agda theorem files in this area.
