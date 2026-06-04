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
- A named logical equivalence type or theorem connecting them.

If the comparison proof is not yet available, leave a typechecked definition of
the comparison target rather than adding a postulate or proving only one
direction under an unclear name.
