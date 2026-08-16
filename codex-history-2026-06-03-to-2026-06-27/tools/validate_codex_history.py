#!/usr/bin/env python3
"""Validate the structure and checksums of a sanitized Codex history bundle."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from generate_chronology_guide import render_guide


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


def validate_timezone_evidence(
    chronology: dict[str, Any], source_machines: set[str] | None = None
) -> None:
    for override in chronology.get("timezone_overrides", []):
        if (
            source_machines is not None
            and override.get("source_machine") not in source_machines
        ):
            continue
        expected_count = override.get("expected_prompt_count")
        observed_count = override.get("observed_prompt_count")
        if expected_count is not None and observed_count != expected_count:
            raise ValueError(
                f"timezone evidence prompt-count mismatch: expected {expected_count}, "
                f"observed {observed_count}"
            )
        observed_range = override.get("observed_prompt_time_range_local")
        window = override.get("daytime_window_local")
        if not observed_range or not window:
            raise ValueError("timezone evidence lacks an observed range or daytime window")
        start = window["start_inclusive"]
        end = window["end_exclusive"]
        if not (start <= observed_range["start"] < end):
            raise ValueError("earliest observed prompt falls outside daytime window")
        if not (start <= observed_range["end"] < end):
            raise ValueError("latest observed prompt falls outside daytime window")


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

    chronology = manifest.get("chronology_guide")
    if not isinstance(chronology, dict):
        raise ValueError("manifest lacks chronology_guide metadata")
    if chronology.get("prompt_count") != len(history):
        raise ValueError("chronology prompt_count does not match filtered history")

    guide_relative_path = Path(str(chronology.get("path", "")))
    if guide_relative_path.is_absolute() or ".." in guide_relative_path.parts:
        raise ValueError(f"invalid chronology guide path: {guide_relative_path}")
    guide_path = bundle_root / guide_relative_path
    if not guide_path.is_file():
        raise ValueError(f"chronology guide is missing: {guide_relative_path}")

    expected_guide, expected_metadata, segments = render_guide(manifest, history)
    if chronology != expected_metadata:
        raise ValueError("chronology metadata is stale or inconsistent")
    if guide_path.read_text(encoding="utf-8") != expected_guide:
        raise ValueError("chronology guide is stale or inconsistent")
    if sum(segment["prompt_count"] for segment in segments) != len(history):
        raise ValueError("chronology segments do not account for every prompt")
    validate_timezone_evidence(chronology, source_machines)

    return len(sessions), len(history)


def main() -> None:
    args = parse_args()
    session_count, history_count = validate_bundle(Path(args.bundle_root).resolve())
    print(f"validated {session_count} sessions and {history_count} history entries")


if __name__ == "__main__":
    main()
