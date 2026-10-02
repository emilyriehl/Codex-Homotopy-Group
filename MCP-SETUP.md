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

## Current experimental server: Peter Thiemann's agda-mcp

The 2026-10-02 session tested
[`peterthiemann/agda-mcp`](https://github.com/peterthiemann/agda-mcp), pinned to
the npm release `agda-mcp@0.4.1`, and configured it for the current Codex client.
It passed the literate-file, type-error, open-goal, and invisible-metavariable
smoke tests, and loaded `src/structured-types/pointed-sets.lagda.md` successfully.
See the [four-server comparison](agda-mcp-ux-report/server-comparison-2026-10-02.md)
for the measured results and limitations.

A follow-up in the restarted client confirmed that all 18 tools are exposed
and that the server works through Codex itself. The live test covered the
repository module, type inference, goal contexts, normalization, refinement preview, applying a
refinement, type-error diagnostics, and invisible metavariables.

This server requires Node.js 22 or newer and an Agda installation. The tested
Agda version was 2.8.0. Its default transformation mode is preview; an
individual transformation can explicitly request `apply: true`.

### Register it in the configuration used by this client

This session uses `CODEX_HOME=/home/eriehl/.codex-astral`. A server registered
only in `~/.codex/config.toml` is therefore not visible to this client. Check
`printenv CODEX_HOME` in the client environment when diagnosing missing tools.
For the configuration used in the 2026-10-02 session:

```sh
CODEX_HOME=/home/eriehl/.codex-astral codex mcp add agda \
  --env 'AGDA_MCP_OPTIONS={"workspaceRoots":["/home/eriehl/Math/Formalization/Codex-Homotopy-Group"],"loadTimeoutMs":300000}' \
  -- npx -y agda-mcp@0.4.1

CODEX_HOME=/home/eriehl/.codex-astral codex mcp get agda
```

The five-minute load timeout accommodates the library: the first test hit the
default two-minute limit, while the subsequent attempt completed in about
113 seconds. Keep the server's default asynchronous mode so long calls return
a job handle that can be collected with `agda_job_await`.

Restart the Codex client after registration and check that Agda tools appear
in the new session. The direct stdio tests in the comparison verify the server;
they do not establish that an already-running client has loaded its tools.

### Smoke test for this server

1. Call `agda_server_info` and check the Agda version and workspace policy.
2. Call `agda_load_module` with the absolute path to
   `src/structured-types/pointed-sets.lagda.md`, and `includeContexts: true`.
3. If the call returns a pending job, collect it with `agda_job_await`.
4. Inspect `diagnostics`, `goals`, and `invisibleMetavariables` in the final
   structured result. `checked: true` alone does not mean a proof is complete:
   both visible holes and invisible metas can remain in an interactive load.
5. Run `./check.sh src/structured-types/pointed-sets.lagda.md`.

## Original server: InvariantHoldings/agda-mcp-server

Use the npm package `agda-mcp-server`, currently pinned here to version `0.6.7`.
This is the server that was smoke-tested in this repository.

Requirements:

- Codex CLI with MCP support.
- Node.js 24 or newer.
- Agda on `PATH`.
- The `agda-unimath` submodule initialized.

### Install For Codex

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

### Smoke Test

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

For agents using the original server's MCP tools, the corresponding sequence is:

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
