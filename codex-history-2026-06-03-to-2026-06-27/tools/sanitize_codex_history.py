#!/usr/bin/env python3
"""Build a publishable, redacted Codex history bundle.

The script copies matching Codex session JSONL files into this bundle, preserving
JSONL structure while recursively redacting sensitive strings in JSON values.
It also writes a manifest and a filtered prompt-history file for the included
session ids.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import re
from pathlib import Path
from typing import Any


REDACTION_VERSION = "2026-08-13.1"
DATE_START_UTC = dt.datetime.fromisoformat("2026-06-03T00:00:00+00:00")
DATE_END_EXCLUSIVE_UTC = dt.datetime.fromisoformat("2026-06-28T00:00:00+00:00")
DEFAULT_RESEARCHER_ID = "<RESEARCHER_1>"


SECRET_PATTERNS = [
    (re.compile(r"sk-proj-[A-Za-z0-9_-]+"), "<OPENAI_API_KEY_REDACTED>"),
    (re.compile(r"sk-[A-Za-z0-9_-]{20,}"), "<OPENAI_API_KEY_REDACTED>"),
    (re.compile(r"org-[A-Za-z0-9_-]{5,}"), "<OPENAI_ORG_ID_REDACTED>"),
    (re.compile(r"proj_[A-Za-z0-9_-]{5,}"), "<OPENAI_PROJECT_ID_REDACTED>"),
    (re.compile(r"github_pat_[A-Za-z0-9_]+"), "<GITHUB_TOKEN_REDACTED>"),
    (re.compile(r"gh[pousr]_[A-Za-z0-9_]{20,}"), "<GITHUB_TOKEN_REDACTED>"),
    (
        re.compile(r"(?i)(OPENAI_API_KEY\s*[:=]\s*)[A-Za-z0-9_./+=-]+"),
        r"\1<OPENAI_API_KEY_REDACTED>",
    ),
    (
        re.compile(r"(?i)(Authorization:\s*Bearer\s+)[A-Za-z0-9_./+=-]+"),
        r"\1<BEARER_TOKEN_REDACTED>",
    ),
]

CONTACT_PATTERNS = [
    (
        re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}"),
        "<EMAIL_REDACTED>",
    ),
]

STATIC_PATTERNS = CONTACT_PATTERNS + SECRET_PATTERNS


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source-root",
        default=str(Path.home() / ".codex" / "sessions"),
        help="Codex sessions root containing YYYY/MM/DD/*.jsonl.",
    )
    parser.add_argument(
        "--history-file",
        default=str(Path.home() / ".codex" / "history.jsonl"),
        help="Codex history.jsonl file to filter by included session id.",
    )
    parser.add_argument(
        "--repo-root",
        default=None,
        help="Exact cwd value identifying sessions for this repository.",
    )
    parser.add_argument(
        "--output-root",
        default=str(Path(__file__).resolve().parents[1]),
        help="Bundle root where sessions/, manifest.json, and history.filtered.jsonl are written.",
    )
    parser.add_argument(
        "--source-machine",
        default="mac-local",
        help="Label recorded in the manifest for this source machine.",
    )
    parser.add_argument(
        "--researcher-id",
        default=DEFAULT_RESEARCHER_ID,
        help="Stable pseudonym for the researcher operating this source machine.",
    )
    parser.add_argument(
        "--session-id",
        action="append",
        default=[],
        help="Refresh only this session id while retaining all other imported sessions. May be repeated.",
    )
    parser.add_argument(
        "--redact-term",
        action="append",
        default=[],
        metavar="RAW=REPLACEMENT",
        help="Private literal to redact, for example 'Name=<RESEARCHER_1>'. May be repeated.",
    )
    return parser.parse_args()


def parse_timestamp(value: str | None) -> dt.datetime | None:
    if not value:
        return None
    return dt.datetime.fromisoformat(value.replace("Z", "+00:00"))


def literal_patterns(args: argparse.Namespace) -> list[tuple[re.Pattern[str], str]]:
    repo_root = args.repo_root or str(Path.cwd())
    home = str(Path.home())
    patterns: list[tuple[re.Pattern[str], str]] = [
        (re.compile(re.escape(repo_root)), "<REPO_ROOT>"),
        (re.compile(re.escape(home) + r"\b"), "<HOME>"),
        (re.compile(r"/Users/([A-Za-z0-9._-]+)\b"), "<HOME_MAC>"),
        (
            re.compile(r"/home/([A-Za-z0-9._-]+)/Codex-Homotopy-Group\b"),
            "<REPO_ROOT_LINUX>",
        ),
        (re.compile(r"/home/([A-Za-z0-9._-]+)\b"), "<HOME_LINUX>"),
    ]
    for term in args.redact_term:
        if "=" not in term:
            raise ValueError(f"invalid --redact-term {term!r}; expected RAW=REPLACEMENT")
        raw, replacement = term.split("=", 1)
        if not raw:
            raise ValueError("--redact-term raw value must not be empty")
        if re.fullmatch(r"[A-Za-z]{1,4}", raw):
            raw_pattern = rf"(?<![A-Za-z0-9_-]){re.escape(raw)}(?![A-Za-z0-9_-])"
        else:
            raw_pattern = re.escape(raw)
        patterns.append(
            (
                re.compile(raw_pattern, re.IGNORECASE),
                replacement,
            )
        )
    return patterns


def redact_string(value: str, patterns: list[tuple[re.Pattern[str], str]]) -> str:
    redacted = value
    for _ in range(3):
        previous = redacted
        for pattern, replacement in patterns + STATIC_PATTERNS:
            redacted = pattern.sub(replacement, redacted)
        if redacted == previous:
            break
    return redacted


def redact_json(value: Any, patterns: list[tuple[re.Pattern[str], str]]) -> Any:
    if isinstance(value, str):
        return redact_string(value, patterns)
    if isinstance(value, list):
        return [redact_json(item, patterns) for item in value]
    if isinstance(value, dict):
        return {
            redact_string(str(key), patterns): redact_json(item, patterns)
            for key, item in value.items()
        }
    return value


def iter_session_files(source_root: Path) -> list[Path]:
    return sorted(source_root.glob("2026/*/*/*.jsonl"))


def session_metadata(path: Path) -> dict[str, Any] | None:
    with path.open("r", encoding="utf-8") as handle:
        first_line = handle.readline()
    try:
        first = json.loads(first_line)
    except json.JSONDecodeError:
        return None
    payload = first.get("payload", {})
    return {
        "session_id": payload.get("id"),
        "started_at": payload.get("timestamp") or first.get("timestamp"),
        "cwd": payload.get("cwd"),
    }


def session_window(path: Path) -> tuple[dt.datetime | None, dt.datetime | None, int]:
    earliest: dt.datetime | None = None
    latest: dt.datetime | None = None
    line_count = 0
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line_count += 1
            try:
                timestamp = parse_timestamp(json.loads(line).get("timestamp"))
            except json.JSONDecodeError:
                continue
            if timestamp is None:
                continue
            earliest = timestamp if earliest is None or timestamp < earliest else earliest
            latest = timestamp if latest is None or timestamp > latest else latest
    return earliest, latest, line_count


def overlaps_requested_window(
    earliest: dt.datetime | None, latest: dt.datetime | None
) -> bool:
    return (
        earliest is not None
        and latest is not None
        and earliest < DATE_END_EXCLUSIVE_UTC
        and latest >= DATE_START_UTC
    )


def relative_session_path(path: Path) -> Path:
    parts = path.parts
    try:
        index = parts.index("sessions")
    except ValueError:
        return Path(path.name)
    return Path(*parts[index + 1 :])


def write_redacted_jsonl(
    source: Path, destination: Path, patterns: list[tuple[re.Pattern[str], str]]
) -> tuple[int, str]:
    destination.parent.mkdir(parents=True, exist_ok=True)
    line_count = 0
    sha256 = hashlib.sha256()
    with source.open("r", encoding="utf-8") as input_handle, destination.open(
        "w", encoding="utf-8"
    ) as output_handle:
        for raw_line in input_handle:
            line_count += 1
            obj = json.loads(raw_line)
            rendered = json.dumps(
                redact_json(obj, patterns), ensure_ascii=False, separators=(",", ":")
            )
            output_handle.write(rendered + "\n")
            sha256.update(rendered.encode("utf-8"))
            sha256.update(b"\n")
    return line_count, sha256.hexdigest()


def rewrite_redacted_jsonl(
    path: Path, patterns: list[tuple[re.Pattern[str], str]]
) -> tuple[int, str]:
    temporary_path = path.with_name(f".{path.name}.redacting")
    try:
        line_count, digest = write_redacted_jsonl(path, temporary_path, patterns)
        temporary_path.replace(path)
    finally:
        temporary_path.unlink(missing_ok=True)
    return line_count, digest


def load_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    entries: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for raw_line in handle:
            entries.append(json.loads(raw_line))
    return entries


def history_sort_key(entry: dict[str, Any]) -> tuple[float, str]:
    timestamp = entry.get("ts")
    if isinstance(timestamp, (int, float)):
        numeric_timestamp = float(timestamp)
    else:
        parsed_timestamp = parse_timestamp(entry.get("timestamp"))
        numeric_timestamp = parsed_timestamp.timestamp() if parsed_timestamp else 0.0
    return numeric_timestamp, str(entry.get("session_id", ""))


def selection_rules_from_manifest(
    manifest: dict[str, Any] | None,
) -> list[dict[str, Any]]:
    if manifest is None:
        return []
    selection_rules = manifest.get("selection_rules")
    if isinstance(selection_rules, list):
        return [rule for rule in selection_rules if isinstance(rule, dict)]
    selection_rule = manifest.get("selection_rule")
    if not isinstance(selection_rule, dict):
        return []
    sessions = manifest.get("sessions", [])
    source_machine = next(
        (
            session.get("source_machine")
            for session in sessions
            if isinstance(session, dict) and session.get("source_machine")
        ),
        "unknown",
    )
    return [{"source_machine": source_machine, **selection_rule}]


def source_machine_records(labels: set[str]) -> list[dict[str, str]]:
    preferred_order = {"mac-local": 0, "linux-laptop": 1}
    return [
        {
            "label": label,
            "status": "included",
            "notes": f"Sanitized local Codex sessions imported from {label}.",
        }
        for label in sorted(labels, key=lambda label: (preferred_order.get(label, 2), label))
    ]


def build_bundle(args: argparse.Namespace) -> int:
    source_root = Path(args.source_root).expanduser()
    output_root = Path(args.output_root).resolve()
    repo_root = args.repo_root or str(Path.cwd())
    patterns = literal_patterns(args)
    selected_session_ids = set(args.session_id)
    sessions_output = output_root / "sessions"
    included_session_ids: set[str] = set()
    manifest_path = output_root / "manifest.json"
    existing_manifest = load_json(manifest_path)
    existing_sessions = existing_manifest.get("sessions", []) if existing_manifest else []
    retained_sessions = [
        redact_json(session, patterns)
        for session in existing_sessions
        if isinstance(session, dict)
        and (
            session.get("source_machine") != args.source_machine
            or (
                selected_session_ids
                and session.get("session_id") not in selected_session_ids
            )
        )
    ]
    for session in retained_sessions:
        session["researcher_id"] = args.researcher_id
    replaced_sessions = [
        session
        for session in existing_sessions
        if isinstance(session, dict)
        and session.get("source_machine") == args.source_machine
        and (
            not selected_session_ids
            or session.get("session_id") in selected_session_ids
        )
    ]
    retained_session_ids = {
        session["session_id"]
        for session in retained_sessions
        if session.get("session_id")
    }
    retained_bundle_paths = {
        session["bundle_path"]
        for session in retained_sessions
        if session.get("bundle_path")
    }
    imported_sessions: list[dict[str, Any]] = []

    for source_path in iter_session_files(source_root):
        metadata = session_metadata(source_path)
        if metadata is None or metadata["cwd"] != repo_root:
            continue
        if selected_session_ids and metadata["session_id"] not in selected_session_ids:
            continue
        earliest, latest, source_line_count = session_window(source_path)
        if not overlaps_requested_window(earliest, latest):
            continue

        relative_path = relative_session_path(source_path)
        destination_path = sessions_output / relative_path
        bundle_path = str(Path("sessions") / relative_path)
        session_id = metadata["session_id"]
        if session_id in retained_session_ids:
            raise ValueError(
                f"session id {session_id} is already recorded for another source machine"
            )
        if bundle_path in retained_bundle_paths:
            raise ValueError(
                f"bundle path {bundle_path} is already used by another source machine"
            )
        output_line_count, digest = write_redacted_jsonl(
            source_path, destination_path, patterns
        )

        included_session_ids.add(session_id)
        imported_sessions.append(
            {
                "session_id": session_id,
                "source_machine": args.source_machine,
                "researcher_id": args.researcher_id,
                "original_path_redacted": redact_string(str(source_path), patterns),
                "bundle_path": bundle_path,
                "started_at": metadata["started_at"],
                "first_event_at": earliest.isoformat() if earliest else None,
                "last_event_at": latest.isoformat() if latest else None,
                "source_line_count": source_line_count,
                "sanitized_line_count": output_line_count,
                "sanitized_sha256": digest,
                "inclusion_reason": "session cwd matched repository and activity overlapped 2026-06-03 through 2026-06-27 inclusive",
                "redaction_version": REDACTION_VERSION,
            }
        )

    imported_bundle_paths = {session["bundle_path"] for session in imported_sessions}
    for session in replaced_sessions:
        bundle_path = session.get("bundle_path")
        if not bundle_path or bundle_path in imported_bundle_paths:
            continue
        stale_path = (output_root / bundle_path).resolve()
        if sessions_output not in stale_path.parents:
            raise ValueError(f"refusing to remove session outside bundle: {stale_path}")
        stale_path.unlink(missing_ok=True)

    if not selected_session_ids:
        for session in retained_sessions:
            bundle_path = session.get("bundle_path")
            if not bundle_path:
                raise ValueError("existing manifest session is missing bundle_path")
            session_path = output_root / bundle_path
            line_count, digest = rewrite_redacted_jsonl(session_path, patterns)
            session["sanitized_line_count"] = line_count
            session["sanitized_sha256"] = digest
            session["redaction_version"] = REDACTION_VERSION

    manifest_sessions = sorted(
        retained_sessions + imported_sessions,
        key=lambda session: (
            session.get("first_event_at") or session.get("started_at") or "",
            session.get("session_id") or "",
        ),
    )
    all_session_ids = {
        session["session_id"] for session in manifest_sessions if session.get("session_id")
    }
    source_machine_by_session_id = {
        session["session_id"]: session["source_machine"]
        for session in manifest_sessions
        if session.get("session_id") and session.get("source_machine")
    }

    history_path = Path(args.history_file).expanduser()
    history_output = output_root / "history.filtered.jsonl"
    history_entries = [
        redact_json(entry, patterns)
        for entry in load_jsonl(history_output)
        if entry.get("session_id") in retained_session_ids
    ]
    if history_path.exists():
        with history_path.open("r", encoding="utf-8") as input_handle:
            for raw_line in input_handle:
                obj = json.loads(raw_line)
                if obj.get("session_id") not in included_session_ids:
                    continue
                history_entries.append(redact_json(obj, patterns))
    for entry in history_entries:
        session_id = entry.get("session_id")
        source_machine = source_machine_by_session_id.get(session_id)
        if source_machine is None:
            raise ValueError(
                f"history entry refers to unmanifested session id {session_id}"
            )
        entry["researcher_id"] = args.researcher_id
        entry["source_machine"] = source_machine
    history_entries.sort(key=history_sort_key)
    with history_output.open("w", encoding="utf-8") as output_handle:
        for entry in history_entries:
            output_handle.write(
                json.dumps(entry, ensure_ascii=False, separators=(",", ":")) + "\n"
            )

    selection_rules = [
        redact_json(rule, patterns)
        for rule in selection_rules_from_manifest(existing_manifest)
        if rule.get("source_machine") != args.source_machine
    ]
    selection_rules.append(
        {
            "source_machine": args.source_machine,
            "source_root_redacted": redact_string(str(source_root), patterns),
            "repo_cwd_match_redacted": redact_string(repo_root, patterns),
            "include_if": "session metadata cwd matches repo and event timestamps overlap the requested UTC window",
        }
    )
    machine_labels = {
        session["source_machine"]
        for session in manifest_sessions
        if session.get("source_machine")
    }
    expected_machine_labels = {"mac-local", "linux-laptop"}
    if expected_machine_labels <= machine_labels:
        status = "complete: mac-local and linux-laptop logs included"
    else:
        missing_labels = ", ".join(sorted(expected_machine_labels - machine_labels))
        status = f"partial: pending logs from {missing_labels}"

    manifest = {
        "title": "Codex history for Codex-Homotopy-Group, 2026-06-03 through 2026-06-27",
        "status": status,
        "date_range_inclusive": {
            "start": "2026-06-03",
            "end": "2026-06-27",
            "timestamp_window_utc": {
                "start": DATE_START_UTC.isoformat(),
                "end_exclusive": DATE_END_EXCLUSIVE_UTC.isoformat(),
            },
        },
        "selection_rules": selection_rules,
        "redaction_version": REDACTION_VERSION,
        "private_redaction_term_count": len(args.redact_term),
        "researchers": [
            {
                "researcher_id": args.researcher_id,
                "source_machines": [
                    machine["label"] for machine in source_machine_records(machine_labels)
                ],
                "notes": "The same researcher prompted all included sessions across these source machines.",
            }
        ],
        "source_machines": source_machine_records(machine_labels),
        "session_count": len(manifest_sessions),
        "history_entry_count": len(history_entries),
        "sessions": manifest_sessions,
    }
    manifest_path.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    if all_session_ids != retained_session_ids | included_session_ids:
        raise ValueError("manifest session ids do not match retained and imported sessions")
    return len(imported_sessions)


def main() -> None:
    args = parse_args()
    count = build_bundle(args)
    print(f"wrote {count} sanitized sessions")


if __name__ == "__main__":
    main()
