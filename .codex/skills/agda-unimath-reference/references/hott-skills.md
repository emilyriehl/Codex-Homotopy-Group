# Homotopy Type Theory Formalization Practices

Use this note when formalizing homotopy type theory in agda-unimath-style
repositories. It records project-level conventions that are more specific than
general Agda or library style.

## Prefer Native Homotopical Definitions

Definitions should live at the mathematical level where they are meant to be
used. Avoid defining homotopical or higher-group-theoretic notions by
immediately translating them into lower-level algebra unless the algebraic
definition is the concept itself.

In particular, constructions involving concrete groups should be native to
concrete groups:

- A concrete group is represented by a pointed connected 1-type.
- A concrete group homomorphism is represented by a pointed map between
  classifying pointed types.
- A concrete exactness condition should therefore be stated as a fiber sequence
  of classifying pointed types, not merely as exactness of the underlying
  ordinary groups.

When an ordinary group formulation is also useful, keep it as a separate
comparison definition and try to prove a logical equivalence between the native
concrete-group formulation and the ordinary group formulation. This makes clear
which theorem identifies the homotopical and algebraic meanings, and prevents
later developments from silently depending on a lossy reinterpretation.

## Comparison Theorems

For parallel native and algebraic definitions, prefer this structure:

- `is-...-Concrete-Group` for the native concrete-group definition.
- `is-algebraically-...-Concrete-Group` for the ordinary-group reinterpretation.
- A named logical equivalence theorem connecting them.

When asked to formalize a theorem, do not only formalize the statement of the
theorem as an element of `UU`. The request is to prove the theorem. If the proof
is not yet available, state the theorem with a proof name following the naming
conventions and leave a hole in the definition if necessary. Then write an
informal proof plan and try to formalize the proof following that plan. If the
plan exposes a missing prerequisite or a mismatch in the theorem statement,
record that explicitly rather than replacing the theorem by a definition of its
type.

When decomposing a theorem into implications, name each direction by the
conclusion followed by the hypothesis. For a proof of `A → B`, use a name of
the form `B-A-...`; for example, a proof from exact concrete-group data to
algebraic exactness should be named
`is-algebraically-exact-is-exact-hom-Concrete-Group`.

## Fiber Sequences And Long Exact Sequences

When following the HoTT Book route to a long exact sequence, keep the proof
stratified. First prove exactness for the set truncation of canonical pointed
fiber sequences. Then prove each adjacent non-canonical triple by comparing it
with a canonical fiber sequence, and only afterward package the uniform
iterated statement and identify the maps with concrete homotopy-group
homomorphisms.

A practical pattern for a pointed map `g : E ->* B` is:

- Start with the canonical exact triple `fiber g ->* E ->* B` after set
  truncation.
- Package the first fiber-of-the-fiber identification, such as
  `Ω B ≃* fiber (fiber g ->* E)`, before proving the next exactness step.
- For the next triples, it may be enough to prove projection or image
  comparison laws, rather than a full pointed equivalence immediately. For
  example, exactness of `Ω E ->* Ω B ->* fiber g` can be reduced to the
  canonical fiber sequence of the boundary map once a point in the fiber of the
  boundary map is shown to project to a loop whose image under `Ω g` is the
  original loop.

For set-truncated exactness proofs, work with pointed-set images and kernels.
The reliable proof shape is to map image witnesses between two maps, eliminate
truncations only into propositions or sets, and use naturality of the
set-truncation unit to relate the maps after truncation.

## Loop-Map Path Algebra

Remember that `map-Ω f p` is defined by transporting `ap (map-pointed-map f) p`
along `preserves-point-pointed-map f`. If a goal relates an untransported path
to a loop map, unfold mentally to
`tr-type-Ω (preserves-point-pointed-map f) (ap (map-pointed-map f) p)` and look
for `eq-conjugation-tr-type-Ω` before expanding all path algebra manually.
Small named helpers for common conjugation cancellations are often worth
keeping when they are used to bridge fiber-equality API output to loop-map
statements.
