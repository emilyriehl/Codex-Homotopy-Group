# Codex History, June 3-27 2026

This folder is a publishable record of Codex work associated with the
`Codex-Homotopy-Group` repository from June 3 through June 27, 2026 inclusive.
The JSONL files are intended to stay close to the original Codex session format
while redacting sensitive local details.

Current status: complete. This bundle contains eight sessions imported from a
Mac and eleven sessions imported from a Linux laptop. The same researcher
operated both machines.

## Contents

- `sessions/`: sanitized Codex session JSONL files, preserving the original
  `YYYY/MM/DD/*.jsonl` layout expected by Codex history tooling.
- `history.filtered.jsonl`: sanitized prompt-history entries for all included
  session ids and source machines, ordered chronologically by timestamp. Each
  entry records the stable researcher pseudonym and its source machine.
- `manifest.json`: provenance, timestamps, line counts, checksums, and inclusion
  reasons for each sanitized session. The manifest records that one stable
  researcher identity operated both source machines.
- `REDACTION.md`: the redaction policy and review checklist.
- `tools/sanitize_codex_history.py`: the script used to generate this bundle.
- `tools/test_sanitize_codex_history.py`: a regression test for merging records
  from multiple source machines.
- `tools/validate_codex_history.py`: structural, chronological-order, line-count,
  and checksum validation for a generated bundle.

The `sessions/**/*.jsonl` files are tracked with Git LFS because the largest
local session is over GitHub's normal per-file blob limit. After cloning this
repository, run `git lfs pull` if the session files appear as LFS pointer files
instead of JSONL.

## Viewing The Logs

The files can be viewed as raw JSONL, or with a Codex history viewer extension
for VS Code. One option is the Codex History Viewer extension on Open VSX:

```text
https://open-vsx.org/extension/HizTam/codex-history-viewer
```

After installing the extension, point its sessions root at this folder's
`sessions/` directory. If using the extension setting, use the absolute path to:

```text
codex-history-2026-06-03-to-2026-06-27/sessions
```

## Selection Rule

Each machine import selected Codex session files whose session metadata recorded
the repository working directory and whose event timestamps overlapped June 3
through June 27, 2026 inclusive. Sessions and prompt history are ordered by
timestamp across machines, not grouped by source machine.

Sessions from other projects in the same date range were excluded. A June 30
session in this repository was also excluded because it falls outside the
requested date range.

## Refreshing Source Logs

To refresh logs from either source machine:

1. Make the source machine's Codex session root readable on the machine running
   the sanitizer.
2. Run `tools/sanitize_codex_history.py` with `--source-root` pointing at that
   session root, `--repo-root` set to the source machine's absolute checkout
   path, and the matching `--source-machine` label. Supply private names and
   account strings as repeated `--redact-term 'raw value=<PLACEHOLDER>'`
   arguments. These raw values should not be committed to the repository. The
   sanitizer preserves sessions from other source machines, reapplies the
   supplied redactions to those retained records, and rebuilds the combined
   prompt history in chronological order.
   A damaged or stale individual session can be refreshed without rewriting the
   rest of the bundle by repeating the command with `--session-id SESSION_ID`.
3. Review the updated `sessions/`, `history.filtered.jsonl`, and
   `manifest.json`.
4. Run the validation checks in `REDACTION.md` before committing.

Do not add unsanitized Codex session files to this repository.
