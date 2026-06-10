# Codex Homotopy Group

This repository contains planning artifacts and experimental agda-unimath
formalization files for the `pi_3(S^2) = Z` project.

## Getting the library

The agda-unimath library is included as a Git submodule. To clone this
repository with the library available, run:

```sh
git clone --recurse-submodules git@github.com:emilyriehl/Codex-Homotopy-Group.git
```

If you already cloned the repository, initialize the submodule with:

```sh
git submodule update --init --depth 1
```

## Optional Agda MCP server

Agents can optionally use an Agda MCP server for interactive proof development,
such as inspecting goals and local contexts. See `MCP-SETUP.md` for setup and
smoke-test instructions. Final verification should still use `./check.sh`.

## Checking a file

The local Agda library file `Codex-Homotopy-Group.agda-lib` includes both this
repository's `src/` directory and `agda-unimath/src/`. To check the current
fiber sequence module, run:

```sh
./check.sh src/synthetic-homotopy-theory/fiber-sequences.lagda.md
```

The first run may take a while because Agda has to build interface files for
dependencies from agda-unimath. Later runs should be faster.
