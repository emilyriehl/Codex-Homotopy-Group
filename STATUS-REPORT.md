# Formalization status report

This report tracks the autoformalized Agda code in this repository against
[the formalization plan](FORMALIZATION-PLAN.md) for `pi_3(S^2) = Z`.

Update this file whenever significant progress is made, for example when a
new theorem is proved, an important definition is formalized, a planned module
is added, or a major blocked item is resolved or re-scoped.

Last updated: 2026-06-09.

## Current summary

The repository currently contains early infrastructure for the planned
calculation:

- General pointed fiber sequences have been formalized.
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
  sequence is exact have been formalized. This now includes the adjacent
  set-truncated triples `Ω B ->* fiber g ->* E` and
  `Ω E ->* Ω B ->* fiber g`, by comparison with canonical fiber sequences.
- The circle facts needed for vanishing higher homotopy groups have been
  formalized: the loop space of the circle and the 1-sphere is equivalent to
  the integers, the circle and 1-sphere are 1-types, and positive concrete
  homotopy groups of 1-types are trivial.

The final theorem `pi_3(S^2) = Z` is not yet formalized. The Hopf fibration,
the full long exact sequence theorem for homotopy groups, Freudenthal, sphere
stability, and the diagonal sphere theorem remain to be done.

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
| Boundary maps and LES exactness steps | [`src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md) | Defines the boundary pointed map, induced maps on homotopy groups of a fiber sequence, recursive boundary pointed maps, and boundary homomorphisms. It proves the first fiber-of-the-fiber identification, packages `Ω B ->* fiber g ->* E` as a pointed fiber sequence, records pointed-set exactness for `fiber g ->* E ->* B`, and proves pointed-set exactness for the adjacent triples `Ω B ->* fiber g ->* E` and `Ω E ->* Ω B ->* fiber g`. These are steps toward, not yet the full proof of, Theorem 8.4.6 of the HoTT book. |
| Higher homotopy groups of 1-types | [`src/synthetic-homotopy-theory/higher-homotopy-groups-truncated-types.lagda.md`](src/synthetic-homotopy-theory/higher-homotopy-groups-truncated-types.lagda.md) | Proves that positive concrete homotopy groups of pointed 1-types are trivial. |
| Circle and 1-sphere homotopy facts | [`src/synthetic-homotopy-theory/homotopy-groups-circle.lagda.md`](src/synthetic-homotopy-theory/homotopy-groups-circle.lagda.md) | Proves the loop-space equivalences for the circle and 1-sphere, the 1-type facts, and triviality of their positive concrete homotopy groups. |

## Status against the formalization plan

| Plan item | Status | Notes |
|---|---|---|
| General pointed fiber sequences | Done | Implemented in [`src/structured-types/fiber-sequences.lagda.md`](src/structured-types/fiber-sequences.lagda.md). |
| Induced maps on homotopy groups | Done | Implemented via iterated loop functoriality and concrete homotopy group functoriality. |
| Long exact sequence of homotopy groups | Partial | Boundary maps, induced homomorphisms, pointed-set exactness, exactness of the set truncation of a canonical fiber sequence, the first fiber-of-the-fiber identification `Ω B ≃* fiber (fiber g -> E)`, and pointed-set exactness of `Ω B ->* fiber g ->* E` and `Ω E ->* Ω B ->* fiber g` are formalized. The remaining proof obligation is to generalize this to the full iterated fiber sequence, prove the remaining HoTT-book fiber-of-the-fiber identifications uniformly, and transport pointed-set exactness to the concrete homotopy-group maps. |
| Exactness-to-isomorphism with zero endpoints | Not started | Needed to extract isomorphisms from exact segments. |
| Higher homotopy groups of the circle vanish | Mostly done | Positive concrete homotopy groups of the circle and 1-sphere are trivial. Further packaging may be needed for the exact Hopf LES endpoints. |
| Loop space of the circle is the integers | Partial | The loop-space equivalence is formalized. A group-level final packaging against the target theorem may still be needed. |
| Hopf construction and Hopf fibration | Not started | No formal Hopf construction, circle H-space package, or `S^1 -> S^3 -> S^2` fiber sequence yet. |
| Freudenthal suspension theorem | Not started | Still a major missing theorem. |
| Stability of homotopy groups of spheres | Not started | Depends on Freudenthal. |
| Diagonal theorem `pi_n(S^n) = Z` | Not started | Needed at `n = 3`. |
| Final theorem `pi_3(S^2) = Z` | Not started | Should be an assembly theorem after Hopf, exactness, and diagonal sphere results are available. |

## Remaining tasks

1. Confirm the final theorem signature, including the `concrete-homotopy-group`
   indexing convention from [the plan](FORMALIZATION-PLAN.md).
2. Package the loop-space computation of the circle as whatever group-level
   statement is needed for the final target.
3. Generalize the proved adjacent exactness steps
   `Ω B ->* fiber g ->* E` and `Ω E ->* Ω B ->* fiber g` to the full
   iterated fiber sequence of a pointed map, proving the remaining
   fiber-of-the-fiber identifications from HoTT book Lemma 8.4.4 uniformly.
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
8. Use the Hopf long exact sequence and circle vanishing results to identify
   `pi_3(S^2)` with `pi_3(S^3)`.
9. Port or prove Freudenthal and the stability theorem for homotopy groups of
   spheres.
10. Prove the diagonal theorem `pi_n(S^n) = Z`, then instantiate it at `n = 3`.
11. Assemble the final theorem by composing the Hopf isomorphism with the
    diagonal theorem instance.

## Current verification

The following refactor-relevant Agda modules were checked on 2026-06-09:

```sh
./check.sh src/structured-types/pointed-sets.lagda.md
./check.sh src/structured-types/exact-sequences-pointed-sets.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
```

All passed after adding the pointed-set exactness proofs for
`Ω B ->* fiber g ->* E` and `Ω E ->* Ω B ->* fiber g`. A source search found
no explicit Agda holes in project-owned `.lagda.md` files under `src/`.
