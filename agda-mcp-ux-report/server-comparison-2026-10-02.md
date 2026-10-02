# Agda MCP server comparison

Date: 2026-10-02. Agent: Codex, based on GPT-6; the exact served model variant
and reasoning effort were not exposed.

The user requested an Agda MCP smoke test, then asked to consider Peter
Thiemann's server, Agda Native AIR, and cliu238's fork alongside the server
used previously in this repository.

Peter Thiemann's server is now configured and usable through the current client.
The three JavaScript implementations passed the small diagnostic tests below.
Native AIR was reviewed from source, but its runtime was not tested. These
results support an initial trial, not a comprehensive reliability ranking.

## Candidates and provenance

| Candidate | Version or revision examined | Distribution | Tools observed |
| --- | --- | --- | --- |
| [Peter Thiemann](https://github.com/peterthiemann/agda-mcp) | npm `agda-mcp@0.4.1` | `npx -y agda-mcp@0.4.1` | 18 |
| [InvariantHoldings, the original server](https://github.com/InvariantHoldings/agda-mcp-server) | npm `agda-mcp-server@0.6.7` | npm package already cached locally | 72 |
| [cliu238](https://github.com/cliu238/agda-mcp-server) | `5fa2475`, package version `0.6.8` | Git checkout, `npm ci --ignore-scripts`, `npm run build` | 74 |
| [Agda Native AIR](https://github.com/formalverification/agda-native-air) | `7825392`, Haskell package version `0.2.0` | Cabal build in its Nix backend | Not measured |

The cliu238 repository explicitly identifies itself as a fork of
InvariantHoldings, with its own fixes and team feedback workflow. Its README
specifies installation from Git rather than an npm release. The test used the
server directly; it did not run the team setup or upload workflow.

Native AIR is a broader environment: its server combines batch Agda verdicts,
interactive queries, and optional corpus retrieval. Its
[server documentation](https://github.com/formalverification/agda-native-air/blob/main/agda-mcp/README.md)
describes fourteen tools, with four retrieval tools registered only when a
corpus is supplied. It also exposes a project acceptance-gate tool. These are
documented capabilities, not runtime observations in this comparison.

## Method

The initial live tests used the locally installed Agda 2.8.0 and direct MCP stdio
JSON-RPC calls (`initialize`, `tools/list`, `tools/call`) from a temporary
Python harness. Agda tools were not yet exposed in the running Codex client's
tool catalogue. The follow-up below verifies that integration after restart.

Temporary fixtures and downloaded checkouts were kept under `/tmp`. No
formalization source in this repository was edited. Four standalone
`.lagda.md` fixtures, using `--without-K --exact-split`, exercised:

- A completed identity function on a datatype `A`.
- A genuine type mismatch: `bad : A`, with body `b : B` for a different datatype.
- An open interactive goal: `identity x = {!!}`.
- An invisible unresolved metavariable: `incomplete : A; incomplete = _`.

Independent `agda --no-allow-unsolved-metas <file>` runs returned exit code 0
for the complete fixture and 42 for each of the other three. The errors were
`UnequalTerms`, `UnsolvedInteractionMetas`, and `UnsolvedMetaVariables`,
respectively.

The project smoke test loaded
`src/structured-types/pointed-sets.lagda.md`, a real agda-unimath-dependent
module. The independent acceptance command also passed:

```sh
./check.sh src/structured-types/pointed-sets.lagda.md
```

## Observed results

| Test | Peter 0.4.1 | Original 0.6.7 | cliu238 0.6.8 |
| --- | --- | --- | --- |
| Completed literate module | Checked, no goals or invisible metas | `ok-complete`, `isComplete: true` | `ok-complete`, `isComplete: true` |
| Actual type error | `checked: false`, mismatch diagnostic | `type-error`, `success: false` | `type-error`, `success: false` |
| Visible hole | One goal of type `A` | `ok-with-holes`, `isComplete: false` | `ok-with-holes`, `isComplete: false` |
| Goal context | `includeContexts` returned `x : A` | `agda_goal_type` returned `x : A` | `agda_goal_type` returned `x : A` |
| Invisible meta | One entry of type `A` in `invisibleMetavariables` | One invisible goal, `isComplete: false` | One invisible goal, `isComplete: false` |
| Real repository module | Loaded with no diagnostics, goals, or invisible metas | Loaded complete | Loaded complete |

The original server and cliu238's fork both reported the seven project flags
from `Codex-Homotopy-Group.agda-lib`, plus `--interaction-json` and
`-l Codex-Homotopy-Group`, through `agda_effective_options`.

Peter's first project load hit the default 120-second command timeout. A
subsequent request with a 300-second timeout succeeded in about 113 seconds.
The cliu238 project load completed in about 10 seconds. These were not
controlled performance trials: cache state and concurrent setup work differed.
The observed latency is a reason to retain asynchronous jobs and increase the
load timeout, not a measured general speed ranking.

## What successful calls mean

The success fields have different meanings. Peter's interactive loads returned
`checked: true` both for the visible hole and for the invisible meta; the
remaining obligations were correctly exposed in their respective arrays.
The original server and its fork returned an outer `ok: true` even for a
type-error result, while `classification: type-error` and inner
`success: false` correctly described the proof state. For open holes they
returned inner `success: true` but `isComplete: false`.

Read the complete proof-state result, not a single transport or operation
success flag. The examples did not reproduce a false claim of completeness.
That observation does not invalidate the historical failures documented in
the [June UX report](README.md), or establish correctness for untested cases.
`./check.sh` remains the final proof acceptance gate for every server.

## Follow-up: live client integration

After restarting the client, the user requested another test and a recommendation.
All 18 Peter 0.4.1 tools were exposed to the agent. Calls in this follow-up used
the client's actual MCP tools rather than the temporary JSON-RPC harness.

- `agda_server_info` reported the configured repository root, Agda 2.8.0, a
  supported adapter, and the preview-by-default mutation policy.
- An asynchronous `agda_load_module` job for `pointed-sets.lagda.md` completed
  with no diagnostics, goals, or invisible metavariables. Type inference for
  `point-Pointed-Set` returned the expected dependent function type.
  `./check.sh src/structured-types/pointed-sets.lagda.md` independently passed.
- An isolated literate fixture contained `identity : Two → Two` with
  `identity x = {!!}`. Loading it returned a goal of type `Two` and context
  `x : Two`.
- Refining with `x` and `apply: false` returned the expected edit, preserved
  the source file's Git object hash, and returned a fresh goal handle.
- Refining that fresh goal with `x` and `apply: true` updated the temporary
  file and returned no goals. Normalizing `identity left` returned `left`.
  Independent `agda --no-allow-unsolved-metas Interactive.lagda.md`, run from
  the fixture's own library directory, exited 0.
- A distinct fixture with an actual type mismatch returned `checked: false`
  and the diagnostic `B !=< A`. An invisible-meta fixture returned one entry
  in `invisibleMetavariables`. Independent batch Agda runs rejected both with
  exit code 42 and the corresponding type-error and unsolved-meta diagnostics.

The temporary fixtures used a separate `.agda-lib` beneath the ignored `temp/`
directory because this server accepts only paths within its configured
workspace. The project wrapper always selects the repository library, so it
cannot check these standalone fixture module names; their batch checks used
their own working directory. After testing, the fixture directory was moved
to `/tmp`. No tracked formalization source was changed.

One reporting detail matters: for the invisible-meta fixture, the short text
summary said `checked: true`, zero diagnostics, and zero goals. The unresolved
meta was present in `structuredContent.data.invisibleMetavariables`. Consumers
must inspect that field as well as the visible goals.

This supports choosing Peter's server for this project's current interactive
workflow: module loading, goal inspection, a refinement preview, applying the
refinement, and normalization now work through the actual client. It does not
establish a universal reliability or performance ranking, or test case splits,
automatic proof search, or the other servers' transformation behavior.

## Native AIR setup limitation

The installed GHC is 9.4.7. The server's Cabal package requires
`base >= 4.18`, newer than the `base` shipped with that compiler. Its documented
build uses the Nix backend shell. An attempt to enter that shell with
`nix develop --offline .#backend --command ghc --version` failed because the
required backend dependencies were not available locally. No claim about
Native AIR's runtime correctness or performance follows from this setup
limitation; completing its toolchain installation remains future work.

## Configuration and recommendation

For the user's current experiment, use Peter's pinned 0.4.1 release. It has a
compact tool surface, returned structured goal contexts, and passed both the
small diagnostics and the real project load. Its
[documented defaults](https://github.com/peterthiemann/agda-mcp#installation-and-use)
support asynchronous jobs and transformation previews, with edits explicitly
requested per call. The initial comparison did not exercise transformations;
the live-client follow-up verified refinement preview and application.

The original server and cliu238 fork remain viable alternatives on this smoke
test evidence. The test did not distinguish their reliability; the fork adds
installation and release-management work. Native AIR is especially relevant
to a future comparison of project gates and corpus retrieval, which these
fixtures do not measure.

The actual registration is in `/home/eriehl/.codex-astral/config.toml`:

```toml
[mcp_servers.agda]
command = "npx"
args = ["-y", "agda-mcp@0.4.1"]

[mcp_servers.agda.env]
AGDA_MCP_OPTIONS = '{"workspaceRoots":["/home/eriehl/Math/Formalization/Codex-Homotopy-Group"],"loadTimeoutMs":300000}'
```

The initial absence of tools was a configuration-directory mismatch: the
original server existed in `~/.codex/config.toml`, but this client reads
`~/.codex-astral/config.toml`. The latter now contains Peter's server, as
confirmed by `codex mcp get agda`. The follow-up after restart confirmed that
the tools are available and usable through Codex itself.

See [MCP-SETUP.md](../MCP-SETUP.md) for the commands and the tool workflow.
