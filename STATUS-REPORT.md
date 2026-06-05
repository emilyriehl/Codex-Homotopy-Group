# Formalization status report

This report tracks the autoformalized Agda code in this repository against
[the formalization plan](FORMALIZATION-PLAN.md) for `pi_3(S^2) = Z`.

Update this file whenever significant progress is made, for example when a
new theorem is proved, an important definition is formalized, a planned module
is added, or a major blocked item is resolved or re-scoped.

Last updated: 2026-06-05.

## Current summary

The repository currently contains early infrastructure for the planned
calculation:

- General pointed fiber sequences have been formalized.
- Functoriality for iterated loop spaces and concrete homotopy groups has been
  added.
- Boundary maps associated to a fiber sequence have been formalized.
- Ordinary group exactness has been defined.
- A fiber sequence of concrete-group classifying maps has been shown to imply
  ordinary exactness of the induced underlying group homomorphisms.
- The circle facts needed for vanishing higher homotopy groups have been
  formalized: the loop space of the circle and the 1-sphere is equivalent to
  the integers, the circle and 1-sphere are 1-types, and positive concrete
  homotopy groups of 1-types are trivial.

The final theorem `pi_3(S^2) = Z` is not yet formalized. The Hopf fibration,
the exactness theorem for the homotopy long exact sequence, Freudenthal,
sphere stability, and the diagonal sphere theorem remain to be done.

## Implemented Agda code

| Area | File | Current status |
|---|---|---|
| Pointed fiber sequences | [`src/structured-types/fiber-sequences.lagda.md`](src/structured-types/fiber-sequences.lagda.md) | Defines the canonical pointed fiber inclusion, `is-fiber-sequence-Pointed-Type`, packaged `fiber-sequence-Pointed-Type`, accessors, null composite maps, and the canonical fiber sequence of a pointed map. |
| Iterated loop functoriality | [`src/synthetic-homotopy-theory/functoriality-iterated-loop-spaces.lagda.md`](src/synthetic-homotopy-theory/functoriality-iterated-loop-spaces.lagda.md) | Defines the pointed map induced by a pointed map on iterated loop spaces. |
| Homotopy automorphism functoriality | [`src/group-theory/functoriality-homotopy-automorphism-groups.lagda.md`](src/group-theory/functoriality-homotopy-automorphism-groups.lagda.md) | Defines classifying pointed maps and induced homomorphisms of concrete homotopy automorphism groups. |
| Homotopy group functoriality | [`src/synthetic-homotopy-theory/functoriality-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/functoriality-homotopy-groups.lagda.md) | Defines `hom-concrete-homotopy-group`, the homomorphism induced by a pointed map on concrete homotopy groups. |
| Exactness of group homomorphisms | [`src/group-theory/exact-sequences-groups.lagda.md`](src/group-theory/exact-sequences-groups.lagda.md) | Defines `is-exact-hom-Group` and proves `is-exact-is-fiber-sequence-hom-Concrete-Group`, the forward implication from a fiber sequence of concrete-group classifying maps to exactness of the induced ordinary group homomorphisms. |
| Boundary maps for fiber sequences | [`src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md`](src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md) | Defines the boundary pointed map, induced maps on homotopy groups of a fiber sequence, recursive boundary pointed maps, and boundary homomorphisms. This is not yet a proof of long exactness. |
| Higher homotopy groups of 1-types | [`src/synthetic-homotopy-theory/higher-homotopy-groups-truncated-types.lagda.md`](src/synthetic-homotopy-theory/higher-homotopy-groups-truncated-types.lagda.md) | Proves that positive concrete homotopy groups of pointed 1-types are trivial. |
| Circle and 1-sphere homotopy facts | [`src/synthetic-homotopy-theory/homotopy-groups-circle.lagda.md`](src/synthetic-homotopy-theory/homotopy-groups-circle.lagda.md) | Proves the loop-space equivalences for the circle and 1-sphere, the 1-type facts, and triviality of their positive concrete homotopy groups. |

## Status against the formalization plan

| Plan item | Status | Notes |
|---|---|---|
| General pointed fiber sequences | Done | Implemented in [`src/structured-types/fiber-sequences.lagda.md`](src/structured-types/fiber-sequences.lagda.md). |
| Induced maps on homotopy groups | Done | Implemented via iterated loop functoriality and concrete homotopy group functoriality. |
| Long exact sequence of homotopy groups | Partial | Boundary maps and induced homomorphisms are formalized, but the exactness theorem itself is not yet proved. |
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
3. Prove the exactness part of the homotopy long exact sequence for fiber
   sequences, at least for the segments needed by the Hopf application.
4. Prove or port the exactness-to-isomorphism lemma for exact segments with
   zero endpoints.
5. Formalize the circle as the connected H-space needed for the Hopf
   construction.
6. Port or formalize the Hopf construction and specialize it to the Hopf
   fibration `S^1 -> S^3 -> S^2`, including the total-space equivalence.
7. Use the Hopf long exact sequence and circle vanishing results to identify
   `pi_3(S^2)` with `pi_3(S^3)`.
8. Port or prove Freudenthal and the stability theorem for homotopy groups of
   spheres.
9. Prove the diagonal theorem `pi_n(S^n) = Z`, then instantiate it at `n = 3`.
10. Assemble the final theorem by composing the Hopf isomorphism with the
    diagonal theorem instance.

## Current verification

The following project-owned Agda modules were checked on 2026-06-05:

```sh
./check.sh src/structured-types/fiber-sequences.lagda.md
./check.sh src/group-theory/exact-sequences-groups.lagda.md
./check.sh src/group-theory/functoriality-homotopy-automorphism-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/functoriality-iterated-loop-spaces.lagda.md
./check.sh src/synthetic-homotopy-theory/functoriality-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/higher-homotopy-groups-truncated-types.lagda.md
./check.sh src/synthetic-homotopy-theory/homotopy-groups-circle.lagda.md
```

All passed. A source search found no explicit Agda holes in project-owned
`.lagda.md` files under `src/`.
