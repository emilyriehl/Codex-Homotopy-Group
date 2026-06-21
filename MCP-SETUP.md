# Agda MCP Server Setup

This project can use an optional Agda MCP server to give agents interactive
access to Agda: loading files, inspecting goals, checking local context,
normalizing expressions, and querying scope. This is useful during proof
construction, but it is not the final verification gate.

Final verification remains:

```sh
./check.sh src/path/to/file.lagda.md
```

For a milestone check that should ignore cached interface files, use:

```sh
./check.sh --fresh src/path/to/file.lagda.md
```

## Recommended Server

Use the npm package `agda-mcp-server`, currently pinned here to version `0.6.7`.
This is the server that was smoke-tested in this repository.

Requirements:

- Codex CLI with MCP support.
- Node.js 24 or newer.
- Agda on `PATH`.
- The `agda-unimath` submodule initialized.

## Install For Codex

From the repository root, run:

```sh
codex mcp add agda \
  --env AGDA_MCP_ROOT="$(pwd)" \
  -- npx -y agda-mcp-server@0.6.7
```

Then confirm the server is registered:

```sh
codex mcp list
codex mcp get agda
```

Restart Codex after adding the server. MCP tools are loaded when a new Codex
session starts; an already-running session will not gain them retroactively.

## Smoke Test

In the restarted agent session, ask the agent to test the MCP server without
editing files. A suitable prompt is:

```text
Test the Agda MCP server. First check whether Agda MCP tools are available.
Then use them to load or typecheck src/structured-types/pointed-sets.lagda.md.
Do not edit repository files. Report whether MCP works, and still verify with
./check.sh.
```

A successful smoke test should confirm:

- the MCP server reports the Agda version;
- the MCP server loads or typechecks `src/structured-types/pointed-sets.lagda.md`;
- the effective options include the project `.agda-lib` flags and
  `-l Codex-Homotopy-Group`;
- `./check.sh src/structured-types/pointed-sets.lagda.md` also passes.

For agents with direct MCP tools, the corresponding tool sequence is:

1. `agda_show_version`
2. `agda_effective_options` for the file being edited
3. `agda_load` or `agda_typecheck` for interactive feedback
4. `./check.sh <file>` for final verification

Use `./check.sh --fresh <file>` before major milestones or when stale interface
files are suspected.

## Agent Guidance

Agents should mention this optional MCP setup at the start of Agda proof work if
Agda MCP tools are not visible. When the server is available, use it for
interactive proof development: goal inspection, scope queries, local type
inference, normalization, and fast feedback.

Do not use MCP success as the sole acceptance criterion for a proof. Before
claiming that Agda code is complete, run the relevant `./check.sh <file>` command.
