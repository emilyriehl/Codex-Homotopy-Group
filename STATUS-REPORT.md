# Formalization status report

This report tracks the autoformalized Agda code in this repository against
[the formalization plan](FORMALIZATION-PLAN.md) for `pi_3(S^2) = Z`.

Update this file whenever significant progress is made, for example when a
new theorem is proved, an important definition is formalized, a planned module
is added, or a major blocked item is resolved or re-scoped.

Last updated: 2026-06-10.

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

The final theorem `pi_3(S^2) = Z` is not yet proved. The top-level Agda file
now assembles the final isomorphism from two intentionally unfinished next-level
stubs: the Hopf-fibration comparison `π₃(S³) ≅ π₃(S²)` and the diagonal sphere
instance `π₃(S³) ≅ ℤ`. The Hopf fibration, the full long exact sequence theorem
for homotopy groups, Freudenthal, sphere stability, and the diagonal sphere
theorem remain to be done.

## Implemented Agda code

| Area | File | Current status |
|---|---|---|
| Pointed fiber sequences | [`src/structured-types/fiber-sequences.lagda.md`](src/structured-types/fiber-sequences.lagda.md) | Defines the canonical pointed fiber inclusion, `is-fiber-sequence-Pointed-Type`, packaged `fiber-sequence-Pointed-Type`, accessors, null composite maps, and the canonical fiber sequence of a pointed map. |
| Iterated loop functoriality | [`src/synthetic-homotopy-theory/functoriality-iterated-loop-spaces.lagda.md`](src/synthetic-homotopy-theory/functoriality-iterated-loop-spaces.lagda.md) | Defines the pointed map induced by a pointed map on iterated loop spaces. |
| Homotopy automorphism functoriality | [`src/group-theory/functoriality-homotopy-automorphism-groups.lagda.md`](src/group-theory/functoriality-homotopy-automorphism-groups.lagda.md) | Defines classifying pointed maps and induced homomorphisms of concrete homotopy automorphism groups. |
| Homotopy group functoriality | [`src/synthetic-homotopy-theory/functoriality-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/functoriality-homotopy-groups.lagda.md) | Defines `hom-concrete-homotopy-group`, the homomorphism induced by a pointed map on concrete homotopy groups. |
| Exactness of group homomorphisms | [`src/group-theory/exact-sequences-groups.lagda.md`](src/group-theory/exact-sequences-groups.lagda.md) | Defines `is-exact-hom-Group` and proves `is-exact-is-fiber-sequence-hom-Concrete-Group`, the forward implication from a fiber sequence of concrete-group classifying maps to exactness of the induced ordinary group homomorphisms. |
| Pointed sets | [`src/structured-types/pointed-sets.lagda.md`](src/structured-types/pointed-sets.lagda.md) | Defines pointed sets, pointed maps of pointed sets, and set truncation as a pointed set and as a pointed map. |
| Exactness of pointed sets | [`src/structured-types/exact-sequences-pointed-sets.lagda.md`](src/structured-types/exact-sequences-pointed-sets.lagda.md) | Defines images, kernels, exactness of pointed-set maps, and proves that the set truncation of the canonical fiber sequence `fiber g -> E -> B` is exact. |
| Boundary maps and LES exactness steps | [`src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md) | Defines the boundary pointed map, induced maps on homotopy groups of a fiber sequence, recursive boundary pointed maps, and boundary homomorphisms. It proves the first fiber-of-the-fiber identification, packages `Ω B ->* fiber g ->* E` as a pointed fiber sequence, proves pointed-set exactness for canonical and packaged `F ->* E ->* B` fiber sequences, proves pointed-set exactness for the packaged boundary segment `Ω B ->* F ->* E`, proves pointed-set exactness for the packaged loop-boundary segment `Ω E ->* Ω B ->* F`, proves pointed-set exactness for the looped packaged segment `Ω F ->* Ω E ->* Ω B`, proves pointed-set exactness for the canonical adjacent triples `Ω B ->* fiber g ->* E`, `Ω E ->* Ω B ->* fiber g`, and `Ω² B ->* Ω (fiber g) ->* Ω E`, and bundles the first four packaged exactness proofs as an initial set-truncated LES segment. These are steps toward, not yet the full proof of, Theorem 8.4.6 of the HoTT book. |
| Higher homotopy groups of 1-types | [`src/synthetic-homotopy-theory/higher-homotopy-groups-truncated-types.lagda.md`](src/synthetic-homotopy-theory/higher-homotopy-groups-truncated-types.lagda.md) | Proves that positive concrete homotopy groups of pointed 1-types are trivial. |
| Circle and 1-sphere homotopy facts | [`src/synthetic-homotopy-theory/homotopy-groups-circle.lagda.md`](src/synthetic-homotopy-theory/homotopy-groups-circle.lagda.md) | Proves the loop-space equivalences for the circle and 1-sphere, the 1-type facts, and triviality of their positive concrete homotopy groups. |
| Hopf comparison for third homotopy groups | [`src/synthetic-homotopy-theory/hopf-fibration-third-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/hopf-fibration-third-homotopy-groups.lagda.md) | Records the next-level stub `π₃(S³) ≅ π₃(S²)`, intentionally unfinished and marked with `--allow-unsolved-metas` so the top-level assembly can import it. |
| Third homotopy group of the 3-sphere | [`src/synthetic-homotopy-theory/third-homotopy-group-sphere-3.lagda.md`](src/synthetic-homotopy-theory/third-homotopy-group-sphere-3.lagda.md) | Records the next-level stub `π₃(S³) ≅ ℤ`, intentionally unfinished and marked with `--allow-unsolved-metas` so the top-level assembly can import it. |
| Final theorem target | [`src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md`](src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md) | Records the pinned top-level statement `π₃(S²) ≅ ℤ` and proves it formally from the inverse Hopf-comparison stub and the `π₃(S³) ≅ ℤ` stub. The proof is therefore structurally assembled but depends on unfinished imported stubs. |

## Status against the formalization plan

| Plan item | Status | Notes |
|---|---|---|
| General pointed fiber sequences | Done | Implemented in [`src/structured-types/fiber-sequences.lagda.md`](src/structured-types/fiber-sequences.lagda.md). |
| Induced maps on homotopy groups | Done | Implemented via iterated loop functoriality and concrete homotopy group functoriality. |
| Long exact sequence of homotopy groups | Partial | Boundary maps, induced homomorphisms, pointed-set exactness, exactness of the set truncation of canonical and packaged `F ->* E ->* B` triples, exactness of the packaged boundary triple `Ω B ->* F ->* E`, exactness of the packaged loop-boundary triple `Ω E ->* Ω B ->* F`, exactness of the looped packaged triple `Ω F ->* Ω E ->* Ω B`, the first fiber-of-the-fiber identification `Ω B ≃* fiber (fiber g -> E)`, pointed-set exactness of the canonical triples `Ω B ->* fiber g ->* E`, `Ω E ->* Ω B ->* fiber g`, and `Ω² B ->* Ω (fiber g) ->* Ω E`, and a bundled initial four-triple set-truncated LES segment are formalized. The remaining proof obligation is to organize these into the full iterated fiber sequence, prove the remaining HoTT-book fiber-of-the-fiber identifications uniformly, and transport pointed-set exactness to the concrete homotopy-group maps. |
| Exactness-to-isomorphism with zero endpoints | Not started | Needed to extract isomorphisms from exact segments. |
| Higher homotopy groups of the circle vanish | Mostly done | Positive concrete homotopy groups of the circle and 1-sphere are trivial. Further packaging may be needed for the exact Hopf LES endpoints. |
| Loop space of the circle is the integers | Partial | The loop-space equivalence is formalized. A group-level final packaging against the target theorem may still be needed. |
| Hopf construction and Hopf fibration | Not started | No formal Hopf construction, circle H-space package, or `S^1 -> S^3 -> S^2` fiber sequence yet. |
| Hopf LES consequence `pi_3(S^3) = pi_3(S^2)` | Stubbed | The expected comparison is recorded in [`src/synthetic-homotopy-theory/hopf-fibration-third-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/hopf-fibration-third-homotopy-groups.lagda.md) as an unfinished theorem. |
| Freudenthal suspension theorem | Not started | Still a major missing theorem. |
| Stability of homotopy groups of spheres | Not started | Depends on Freudenthal. |
| Diagonal theorem `pi_n(S^n) = Z` | Instance stubbed | The needed `n = 3` instance is recorded in [`src/synthetic-homotopy-theory/third-homotopy-group-sphere-3.lagda.md`](src/synthetic-homotopy-theory/third-homotopy-group-sphere-3.lagda.md) as an unfinished theorem. The general diagonal theorem remains unproved. |
| Final theorem `pi_3(S^2) = Z` | Assembled from stubs | The target statement in [`src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md`](src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md) is now a formal composition of the two next-level stubs. It has no direct proof hole but remains mathematically unfinished until those imported stubs are proved. |

## Remaining tasks

1. Prove the two next-level stubs now used by the final assembly: the Hopf LES
   comparison `π₃(S³) ≅ π₃(S²)` and the diagonal sphere instance `π₃(S³) ≅ ℤ`.
2. Package the loop-space computation of the circle as whatever group-level
   statement is needed for the final target.
3. Package the full iterated fiber sequence of a pointed map. The
   pointed-set exactness layer now covers arbitrary packaged triples
   `F ->* E ->* B`, `Ω B ->* F ->* E`, `Ω E ->* Ω B ->* F`,
   and `Ω F ->* Ω E ->* Ω B`, and bundles these as a finite initial segment.
   Canonically, the looped boundary-fiber triple
   `Ω² B ->* Ω (fiber g) ->* Ω E` is also exact. The remaining adjacent
   triples for an arbitrary packaged fiber still need the uniform HoTT book
   Lemma 8.4.4 fiber-of-the-fiber identifications and the associated map
   identifications, including the sign conventions for iterated loops.
4. Use the resulting family of pointed-set exactness proofs to prove the long
   exact sequence of pointed sets from HoTT book Theorem 8.4.6, then identify
   the group-level maps with the existing homotopy-group maps up to the sign
   conventions in the book.
5. Prove or port the exactness-to-isomorphism lemma for exact segments with
   zero endpoints.
6. Formalize the circle as the connected H-space needed for the Hopf
   construction.
7. Port or formalize the Hopf construction and specialize it to the Hopf
   fibration `S^1 -> S^3 -> S^2`, including the total-space equivalence.
8. Fill the Hopf comparison stub by using the Hopf long exact sequence and
   circle vanishing results to identify `pi_3(S^3)` with `pi_3(S^2)`.
9. Port or prove Freudenthal and the stability theorem for homotopy groups of
   spheres.
10. Fill the `pi_3(S^3) = Z` stub by proving the diagonal theorem
    `pi_n(S^n) = Z` and instantiating it at `n = 3`.
11. Recheck the final theorem after both imported stubs are proved; its proof
    body should remain only the current composition.

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

The current top-level stub modules were checked after assembling the final
proof from the two next-level stubs:

```sh
./check.sh src/synthetic-homotopy-theory/hopf-fibration-third-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/third-homotopy-group-sphere-3.lagda.md
./check.sh src/synthetic-homotopy-theory/third-homotopy-group-sphere-2.lagda.md
```

These commands passed because the two next-level stub modules are explicitly
marked with `--allow-unsolved-metas`. This is a development scaffold, not a
completed proof. The two remaining holes are in the Hopf comparison stub and the
`π₃(S³) ≅ ℤ` stub; the final `π₃(S²) ≅ ℤ` file has no direct proof hole and is
only incomplete through those imports.
