# Agda MCP Server UX Report

Report date: 2026-06-30.

This directory is the shareable report package. It contains the human-readable
report, the redacted evidence artifacts, and the extractor used to regenerate
them from local full Codex logs.

This report summarizes Agda MCP server issues observed while using the server for
Agda development in a repository that depends on `agda-unimath`. It is written
for an Agda user or MCP maintainer who may not know homotopy type theory or the
agda-unimath library.

The goal is not to complain about ordinary Agda type errors. The goal is to
identify places where the MCP server made those errors hard to interpret,
reported success for failed operations, or gave incomplete machine-readable
status to the client.

## Evidence Sources

The report is based on full Codex session logs, not on `CHAT-LOG.md`.

- Full session logs scanned locally: `~/.codex/sessions/2026/06/*.jsonl`.
- Runtime log database scanned locally: `~/.codex/logs_2.sqlite`.
- Extractor: `extract-mcp-evidence.mjs`.
- Structured evidence: `mcp-evidence.json`.
- Compact evidence index: `mcp-evidence.csv`.

The full logs are not copied into this repository. The evidence files contain
redacted, shortened excerpts and source file/line pointers into the local logs.

Observed environment from the logs:

- Agda MCP server version: `0.6.7`.
- Agda version reported by the server: `Agda version 2.8.0`.
- Codex CLI versions seen across sessions: `0.136.0`, `0.137.0`,
  `0.140.0`, `0.141.0`.
- Agda MCP calls counted: `711`.
- Suspicious MCP call occurrences classified: `290`.
- Unclassified suspicious MCP call occurrences after extraction: `0`.

Counts are occurrences, not necessarily distinct root-cause bugs. Categories can
overlap; for example, the same call can both contain an Agda error and return
`ok: true`.

## Completeness Method

The extractor is intentionally part of the deliverable. It parses every JSONL
session file under the configured session root, counts every `agda_*` MCP call
found in `custom_tool_call` or `mcp_tool_call_end` events, pairs calls with their
visible outputs when possible, and classifies every suspicious structured result.

The working completeness criterion was:

- all available full session logs for June 2026 were scanned;
- every Agda MCP call in those logs was counted;
- every call matching a suspicious pattern was assigned to a named category;
- ordinary Agda failures were not counted as MCP bugs unless the MCP result made
  the failure misleading or non-machine-readable;
- the final extraction reported `unclassified_suspicious_items: 0`.

This means the report is comprehensive over the observed types of MCP failure in
these logs. It does not claim that every possible MCP server issue has been
observed.

## Why agda-unimath Flags Matter

This repository uses agda-unimath-style flags. These flags are normal Agda
configuration choices, but they matter when interpreting errors:

- `--without-K`: Agda does not assume uniqueness of identity proofs. In practice,
  some pattern matches on equality proofs, especially around `refl`, are not
  accepted. Split/unification failures caused by this flag are legitimate Agda
  feedback, not server bugs.
- `--exact-split`: pattern matching clauses must satisfy Agda's exact splitting
  discipline. A case split may be rejected even if a user expected a looser
  coverage check.
- `--no-import-sorts`: primitive sort names are not automatically brought into
  scope in the same way as in a default Agda setup. agda-unimath code normally
  uses its own universe notation such as `UU`.
- `--no-postfix-projections`: postfix projection syntax is disabled; projection
  use must follow the library's prefix style.
- `--no-require-unique-meta-solutions`: meta-solution reporting can differ from
  stricter Agda modes, so a client needs to distinguish visible goals, hidden
  metas, constraints, and final completeness carefully.
- `--auto-inline` and
  `-WnoWithoutKFlagPrimEraseEquality` affect normalization/warnings and are part
  of the library environment.

These flags can explain why Agda rejects a proof attempt. They do not explain an
MCP result that says `ok: true` while the payload contains `error: [...]`, no
checked term, or a failed post-edit reload.

## Findings

### 1. `ok: true` was not a reliable success signal

Observed counts:

- `70` calls returned `ok: true` while the payload contained an Agda diagnostic
  such as `error: [NotInScope]`, `error: [UnequalTerms]`, or
  `error: [ParseError]`.
- `15` calls had a failed user-facing status or failure classification while the
  structured result still had `ok: true`.
- `13` context-check calls returned `ok: true` but the checked term field said no
  checked term was returned.
- Under the extractor's heuristic for embedded Agda `error: [...]` diagnostics,
  `0` such failures were surfaced as `ok: false`; process timeouts were surfaced
  separately.

Impact: clients and agents cannot use `ok` as a programmatic success predicate.
They have to parse human text for error strings, which is brittle and leads to
bad automation decisions.

Suggested fix: separate transport success from Agda success. For example:

- `transportOk`: the MCP request/response completed;
- `agdaCommandOk`: Agda accepted the requested query or edit;
- `fileComplete`: no goals, metas, or constraints remain;
- `diagnostics`: structured Agda diagnostics with severity and range.

### 2. `agda_auto` reported malformed proof-search payloads as solutions

Observed count: `15`.

Representative symptom: `agda_auto` returned a "Solution" whose text was an
Agda scope error saying `Not in scope: -d`, with a search payload such as
`-d 5 --list-candidates`.

Impact: an agent can treat a command-line parse/scope error as a proof term. In
one observed state-changing case, that error text was written back into the
source file and the reload then failed.

Suggested fix: make proof search return a structured failure when the search
payload is rejected. Do not place diagnostic text in a field named `solution`,
and never report `hasSolution: true` for an Agda error.

### 3. State-changing tools could report success after creating reload errors

Observed count: `6`.

Affected tools in the evidence: `agda_case_split`, `agda_refine`,
`agda_refine_exact`, and one `agda_auto` case.

Representative symptom: the tool wrote a replacement, then reported text such
as `Reloaded with errors: 0 goal(s) remaining` and `Goal diff: solved ?0`, while
the same payload contained parse errors or split errors from Agda.

Impact: the client sees "goal solved" even though the file does not type-check.
This is especially risky for editing tools because the source has already been
mutated.

Suggested fix: split the result into:

- `editApplied`;
- `reloadOk`;
- `postReloadGoalCount`;
- `postReloadDiagnostics`;
- `solvedGoals`.

If `reloadOk` is false, the headline status should be failure or partial
failure, even if a previous goal marker disappeared textually.

### 4. Hole/completeness accounting was ambiguous

Observed count: `151`.

Representative symptom: `agda_load` returned classification `ok-with-holes`,
`hasHoles: true`, `goalCount: 0`, and `invisibleGoalCount: 0`.

This may reflect a real distinction between visible interaction goals and other
hole/metavariable states. The UX problem is that the result looks internally
contradictory to a client: there are holes, but no visible or invisible goals.

Impact: a user or agent cannot reliably decide whether a file is complete, has
hidden metas, has source-level hole syntax, or is in a stale/inconsistent state.

Suggested fix: expose distinct fields for:

- source hole syntax, such as `{! !}` or `?`;
- visible interaction goals;
- hidden/invisible goals;
- unsolved metas;
- constraints;
- final file completeness.

### 5. `agda_proof_status` could say there were no goals while constraints held Agda errors

Observed count: `6` as a subcase of `ok_true_embedded_agda_error`.

Representative symptom: `agda_proof_status` reported `Goals: 0 unsolved` and
`Constraints: yes`, while the constraints block contained Agda errors such as
`error: [UnequalTerms]`.

Impact: "all goals solved" is not enough for completion. Constraints and errors
must participate in the machine-readable status.

Suggested fix: if constraints contain errors, the command should not summarize
the proof state as complete. The status model should make "no visible goals" a
different state from "file accepted".

### 6. Timeout/process errors were real but diagnostics were too coarse

Observed counts:

- `10` timeout/no-protocol-response occurrences.
- `9` timeout diagnostics that suggested the subprocess may have crashed or
  failed to start, even though the direct evidence was a 120-second command
  timeout with no protocol response.

Affected tools included `agda_load`, `agda_typecheck`, and `agda_auto_all`.

Impact: users get advice that may send them toward installation/startup
debugging when the real situation might be a long-running type check, blocked
command, or protocol silence.

Suggested fix: distinguish:

- subprocess failed to start;
- subprocess exited;
- protocol produced no response before timeout;
- Agda is still running;
- Agda is checking a specific file;
- user/client cancelled.

### 7. User-visible timing was inconsistent

Observed count: `20`.

Representative symptom: the MCP structured result reported an `elapsedMs` value
of a few hundred or a few thousand milliseconds, while the outer command wall
time was tens of seconds, minutes, or longer.

Impact: users cannot tell whether time was spent in Agda, server queueing,
protocol wait, client-side processing, or stale-session recovery.

Suggested fix: expose separate timing fields for server handling time, Agda
command time, protocol wait time, queue time, and total wall time if available.

### 8. Reload/staleness transitions were hard to interpret

Observed count: `63`.

Representative symptom: `agda_load` after a modified file reported
`staleBeforeLoad: true` and a changed classification, but not enough explanation
to tell whether the previous classification was invalidated by a source edit,
cache state, interface files, or server state.

Impact: an agent has to guess whether the new status is a real source result or
an artifact of stale state.

Suggested fix: when reporting stale reloads, include a concise transition:

- previous loaded file and mtime;
- current file and mtime;
- whether interface cache was reused;
- previous classification;
- new classification;
- reason for reload.

### 9. Startup/discovery friction appeared in runtime logs

Observed count: `8` runtime log items.

Representative symptom: `list_tools_for_server{server_name=agda ... startup_complete=false}`
followed by cancellation and graceful child exit/SIGTERM records.

Impact: from the user side, tools can appear unavailable or disappear without a
clear explanation of whether startup was still in progress, cancelled by the
client, or failed.

Suggested fix: surface a first-class server lifecycle state to the client:
`starting`, `ready`, `cancelled`, `exited`, or `failed`, with child-exit reason.

### 10. Raw Agda remained necessary as the acceptance gate

Observed count: `31` targeted log excerpts showing the workflow warning in
`check.sh`.

This count is not a direct MCP bug count. It is evidence of the user experience
consequence: because MCP results were not reliable enough as final acceptance,
the repository workflow required raw Agda verification through `check.sh`.

Suggested fix: make MCP completion semantics precise enough that users know
exactly when they still need raw Agda. Even if raw Agda remains the final
authority, MCP should avoid names such as `ok-complete` unless the meaning is
fully specified and machine-checkable.

## Recommended Regression Tests

These tests do not require HoTT-specific knowledge. They can be small Agda files
or temporary modules using ordinary scope/type errors.

1. A file containing a visible hole should never produce a result where
   `fileComplete` is true.
2. A query whose expression is not in scope should return `ok: false` or
   `agdaCommandOk: false`, with a structured `NotInScope` diagnostic.
3. A context-check command that fails should not include "no checked term" in a
   success result.
4. `agda_auto` should not treat command-line flags or search payload text as an
   Agda term, and should not report diagnostics as solutions.
5. A mutation tool that writes text and then fails to reload should return a
   partial/failure status with post-reload diagnostics.
6. `agda_load` should distinguish visible goals, hidden metas, constraints,
   source hole syntax, and complete file acceptance.
7. A timeout should identify whether Agda exited, remained running, or produced
   no protocol response.
8. A stale reload should report the previous and new classification together
   with the reason the previous state was stale.

## Suggested Schema Direction

A result shape along these lines would make client behavior much safer:

```json
{
  "transportOk": true,
  "agdaCommandOk": false,
  "fileComplete": false,
  "classification": "type-error",
  "goals": {
    "visible": 0,
    "invisible": 0,
    "sourceHoles": 1,
    "unsolvedMetas": 1,
    "constraints": 0
  },
  "diagnostics": [
    {
      "severity": "error",
      "code": "NotInScope",
      "range": "Example.agda:3.5-8",
      "message": "Not in scope: foo"
    }
  ],
  "timing": {
    "serverMs": 12,
    "agdaMs": 430,
    "protocolWaitMs": 0,
    "totalWallMs": 450
  }
}
```

The important point is not this exact JSON. The important point is that clients
should not have to parse prose to learn whether Agda accepted the command, the
file is complete, a proof search found a term, or an edit left the file broken.

## Appendix: Category Counts

From `mcp-evidence.json`:

| Category | Count |
| --- | ---: |
| `auto_malformed_search_payload` | 15 |
| `ok_true_embedded_agda_error` | 70 |
| `failed_status_but_ok_true` | 15 |
| `ok_true_no_checked_term` | 13 |
| `state_change_success_after_reload_errors` | 6 |
| `holes_reported_zero_goals` | 151 |
| `timeout_no_protocol_response` | 10 |
| `timeout_diagnostic_overstates_crash` | 9 |
| `wall_time_elapsed_mismatch` | 20 |
| `stale_reload_classification_flip` | 63 |
| `availability_or_startup_friction` | 8 |
| `raw_agda_required_as_acceptance_gate` | 31 |
