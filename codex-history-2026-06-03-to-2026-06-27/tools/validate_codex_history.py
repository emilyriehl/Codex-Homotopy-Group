#!/usr/bin/env python3
"""Validate the structure and checksums of a sanitized Codex history bundle."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--bundle-root",
        default=str(Path(__file__).resolve().parents[1]),
        help="Bundle root containing sessions/, manifest.json, and history.filtered.jsonl.",
    )
    return parser.parse_args()


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_number, raw_line in enumerate(handle, start=1):
            try:
                entries.append(json.loads(raw_line))
            except json.JSONDecodeError as error:
                raise ValueError(f"invalid JSON in {path}:{line_number}: {error}") from error
    return entries


def jsonl_metadata(path: Path) -> tuple[int, str]:
    line_count = 0
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for raw_line in handle:
            line_count += 1
            try:
                json.loads(raw_line.decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError) as error:
                raise ValueError(f"invalid JSON in {path}:{line_count}: {error}") from error
            digest.update(raw_line)
    return line_count, digest.hexdigest()


def history_sort_key(entry: dict[str, Any]) -> tuple[float, str]:
    timestamp = entry.get("ts")
    if not isinstance(timestamp, (int, float)):
        raise ValueError(f"history entry has nonnumeric timestamp: {timestamp!r}")
    return float(timestamp), str(entry.get("session_id", ""))


def validate_bundle(bundle_root: Path) -> tuple[int, int]:
    manifest_path = bundle_root / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    sessions = manifest.get("sessions", [])
    if manifest.get("session_count") != len(sessions):
        raise ValueError("manifest session_count does not match sessions list")

    expected_paths = {session["bundle_path"] for session in sessions}
    actual_paths = {
        str(path.relative_to(bundle_root))
        for path in (bundle_root / "sessions").rglob("*.jsonl")
    }
    if expected_paths != actual_paths:
        missing = sorted(expected_paths - actual_paths)
        extra = sorted(actual_paths - expected_paths)
        raise ValueError(f"session path mismatch; missing={missing}, extra={extra}")

    researcher_ids = {
        researcher["researcher_id"] for researcher in manifest.get("researchers", [])
    }
    source_machines = {
        machine["label"] for machine in manifest.get("source_machines", [])
    }
    session_by_id: dict[str, dict[str, Any]] = {}
    for session in sessions:
        session_id = session["session_id"]
        if session_id in session_by_id:
            raise ValueError(f"duplicate manifest session id: {session_id}")
        if session.get("researcher_id") not in researcher_ids:
            raise ValueError(f"session researcher is absent from manifest: {session_id}")
        if session.get("source_machine") not in source_machines:
            raise ValueError(f"session source machine is absent from manifest: {session_id}")
        session_by_id[session_id] = session
        path = bundle_root / session["bundle_path"]
        line_count, digest = jsonl_metadata(path)
        if line_count != session["sanitized_line_count"]:
            raise ValueError(f"line-count mismatch for {session['bundle_path']}")
        if digest != session["sanitized_sha256"]:
            raise ValueError(f"checksum mismatch for {session['bundle_path']}")

    session_order = [
        (session.get("first_event_at") or session.get("started_at") or "", session["session_id"])
        for session in sessions
    ]
    if session_order != sorted(session_order):
        raise ValueError("manifest sessions are not globally ordered by first timestamp")

    history = load_jsonl(bundle_root / "history.filtered.jsonl")
    if manifest.get("history_entry_count") != len(history):
        raise ValueError("manifest history_entry_count does not match filtered history")
    if [history_sort_key(entry) for entry in history] != sorted(
        history_sort_key(entry) for entry in history
    ):
        raise ValueError("filtered history is not globally ordered by timestamp")

    for entry in history:
        session_id = entry.get("session_id")
        session = session_by_id.get(session_id)
        if session is None:
            raise ValueError(f"history entry has unknown session id: {session_id}")
        if entry.get("source_machine") != session.get("source_machine"):
            raise ValueError(f"history source machine mismatch for session {session_id}")
        if entry.get("researcher_id") != session.get("researcher_id"):
            raise ValueError(f"history researcher mismatch for session {session_id}")
        if entry.get("researcher_id") not in researcher_ids:
            raise ValueError(f"history researcher is absent from manifest: {session_id}")

    return len(sessions), len(history)


def main() -> None:
    args = parse_args()
    session_count, history_count = validate_bundle(Path(args.bundle_root).resolve())
    print(f"validated {session_count} sessions and {history_count} history entries")


if __name__ == "__main__":
    main()
