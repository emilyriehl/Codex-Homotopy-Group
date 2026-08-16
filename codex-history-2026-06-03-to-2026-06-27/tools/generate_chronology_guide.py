#!/usr/bin/env python3
"""Generate a timezone-aware reading guide for a Codex history bundle."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
from pathlib import Path
from typing import Any
from zoneinfo import ZoneInfo


GUIDE_PATH = "CHRONOLOGY.md"
DEFAULT_TIMEZONE = "America/New_York"
TIMEZONE_OVERRIDES: list[dict[str, Any]] = [
    {
        "source_machine": "linux-laptop",
        "timezone": "Europe/Stockholm",
        "local_date_start": "2026-06-08",
        "local_date_end_inclusive": "2026-06-12",
        "start_utc": "2026-06-07T22:00:00+00:00",
        "end_exclusive_utc": "2026-06-12T22:00:00+00:00",
        "daytime_window_local": {
            "start_inclusive": "07:00",
            "end_exclusive": "21:00",
        },
        "expected_prompt_count": 67,
        "notes": "Researcher-reported timezone for this machine and date interval.",
    }
]


def parse_timestamp(value: str) -> dt.datetime:
    parsed = dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
    if parsed.tzinfo is None:
        raise ValueError(f"timestamp lacks timezone information: {value!r}")
    return parsed.astimezone(dt.timezone.utc)


def load_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_number, raw_line in enumerate(handle, start=1):
            try:
                entries.append(json.loads(raw_line))
            except json.JSONDecodeError as error:
                raise ValueError(f"invalid JSON in {path}:{line_number}: {error}") from error
    return entries


def chronology_policy_from_manifest(manifest: dict[str, Any]) -> dict[str, Any]:
    chronology = manifest.get("chronology_guide", {})
    return {
        "path": chronology.get("path", GUIDE_PATH),
        "default_timezone": chronology.get("default_timezone", DEFAULT_TIMEZONE),
        "timezone_overrides": chronology.get(
            "timezone_overrides", TIMEZONE_OVERRIDES
        ),
    }


def timezone_for_entry(
    entry: dict[str, Any], instant: dt.datetime, policy: dict[str, Any]
) -> tuple[ZoneInfo, dict[str, Any] | None]:
    for override in policy["timezone_overrides"]:
        if entry.get("source_machine") != override["source_machine"]:
            continue
        start = parse_timestamp(override["start_utc"])
        end = parse_timestamp(override["end_exclusive_utc"])
        if start <= instant < end:
            return ZoneInfo(override["timezone"]), override
    return ZoneInfo(policy["default_timezone"]), None


def history_sort_key(entry: dict[str, Any]) -> tuple[float, str]:
    timestamp = entry.get("ts")
    if not isinstance(timestamp, (int, float)):
        raise ValueError(f"history entry has nonnumeric timestamp: {timestamp!r}")
    return float(timestamp), str(entry.get("session_id", ""))


def transition_label(
    segment: dict[str, Any],
    previous: dict[str, Any] | None,
    seen_session_ids: set[str],
) -> str:
    session_id = segment["session_id"]
    if previous is None:
        return "Archive begins"
    if session_id == previous["session_id"]:
        if segment["timezone"] != previous["timezone"]:
            return "Continued session; display timezone changes"
        return "Continued session on a new local day"
    if session_id in seen_session_ids:
        if segment["source_machine"] != previous["source_machine"]:
            return "Machine handoff; resumed earlier session"
        return "Resumed earlier session"
    if segment["source_machine"] != previous["source_machine"]:
        return "Machine handoff to a new session"
    return "New session on the same machine"


def build_segments(
    manifest: dict[str, Any],
    history: list[dict[str, Any]],
    policy: dict[str, Any] | None = None,
) -> list[dict[str, Any]]:
    policy = policy or chronology_policy_from_manifest(manifest)
    sessions = {
        session["session_id"]: session for session in manifest.get("sessions", [])
    }
    segments: list[dict[str, Any]] = []

    for entry in sorted(history, key=history_sort_key):
        session_id = entry.get("session_id")
        session = sessions.get(session_id)
        if session is None:
            raise ValueError(f"history entry has unknown session id: {session_id}")
        if entry.get("source_machine") != session.get("source_machine"):
            raise ValueError(f"history source machine mismatch for session {session_id}")
        if entry.get("researcher_id") != session.get("researcher_id"):
            raise ValueError(f"history researcher mismatch for session {session_id}")

        instant = dt.datetime.fromtimestamp(float(entry["ts"]), tz=dt.timezone.utc)
        timezone, override = timezone_for_entry(entry, instant, policy)
        local = instant.astimezone(timezone)
        segment_key = (
            local.date().isoformat(),
            timezone.key,
            session_id,
            entry["source_machine"],
            entry["researcher_id"],
        )

        if not segments or segments[-1]["key"] != segment_key:
            segments.append(
                {
                    "key": segment_key,
                    "local_date": local.date().isoformat(),
                    "timezone": timezone.key,
                    "timezone_abbreviation": local.tzname(),
                    "timezone_override": override,
                    "session_id": session_id,
                    "session_started_at": session.get("started_at"),
                    "bundle_path": session["bundle_path"],
                    "source_machine": entry["source_machine"],
                    "researcher_id": entry["researcher_id"],
                    "first_timestamp": instant,
                    "last_timestamp": instant,
                    "first_local": local,
                    "last_local": local,
                    "prompt_count": 1,
                }
            )
        else:
            segment = segments[-1]
            segment["last_timestamp"] = instant
            segment["last_local"] = local
            segment["prompt_count"] += 1

    previous: dict[str, Any] | None = None
    seen_session_ids: set[str] = set()
    for segment in segments:
        segment["transition"] = transition_label(
            segment, previous, seen_session_ids
        )
        seen_session_ids.add(segment["session_id"])
        previous = segment
    return segments


def override_evidence(
    history: list[dict[str, Any]], policy: dict[str, Any]
) -> list[dict[str, Any]]:
    evidence: list[dict[str, Any]] = []
    for override in policy["timezone_overrides"]:
        timezone = ZoneInfo(override["timezone"])
        start = parse_timestamp(override["start_utc"])
        end = parse_timestamp(override["end_exclusive_utc"])
        local_times: list[dt.datetime] = []
        for entry in history:
            if entry.get("source_machine") != override["source_machine"]:
                continue
            instant = dt.datetime.fromtimestamp(float(entry["ts"]), tz=dt.timezone.utc)
            if start <= instant < end:
                local_times.append(instant.astimezone(timezone))
        observed = dict(override)
        observed["observed_prompt_count"] = len(local_times)
        observed["observed_prompt_time_range_local"] = (
            {
                "start": min(local_time.strftime("%H:%M") for local_time in local_times),
                "end": max(local_time.strftime("%H:%M") for local_time in local_times),
            }
            if local_times
            else None
        )
        evidence.append(observed)
    return evidence


def format_window(start: dt.datetime, end: dt.datetime, include_zone: bool) -> str:
    if start.date() == end.date():
        rendered = f"{start:%Y-%m-%d %H:%M}–{end:%H:%M}"
    else:
        rendered = f"{start:%Y-%m-%d %H:%M}–{end:%Y-%m-%d %H:%M}"
    if include_zone:
        rendered += f" {start.tzname()}"
    return rendered


def render_guide(
    manifest: dict[str, Any],
    history: list[dict[str, Any]],
    policy: dict[str, Any] | None = None,
) -> tuple[str, dict[str, Any], list[dict[str, Any]]]:
    policy = policy or chronology_policy_from_manifest(manifest)
    segments = build_segments(manifest, history, policy)
    evidence = override_evidence(history, policy)

    lines = [
        "# Chronological Reading Guide",
        "",
        "This is a derived navigation guide for the native Codex session logs in",
        "`sessions/`. It does not replace, split, or rewrite those files. Codex stores a",
        "continued session under the date on which that session began, so the rows below",
        "show when to continue in another file or return to an earlier one.",
        "",
        "Rows are ordered by the absolute prompt timestamp. A \"machine handoff\" means",
        "that the next recorded human prompt came from another machine; it does not claim",
        "that Codex created a native session boundary. All prompts were made by the same",
        "researcher, recorded under the stable pseudonym `<RESEARCHER_1>`.",
        "",
        "## Time zones",
        "",
        f"The default researcher-local display timezone is `{policy['default_timezone']}`.",
    ]
    for item in evidence:
        observed_range = item["observed_prompt_time_range_local"]
        observed_text = (
            f"{observed_range['start']}–{observed_range['end']}"
            if observed_range
            else "no prompts"
        )
        window = item["daytime_window_local"]
        lines.extend(
            [
                "",
                (
                    f"For `{item['source_machine']}` from {item['local_date_start']} through "
                    f"{item['local_date_end_inclusive']} inclusive, the display timezone is "
                    f"`{item['timezone']}`. The {item['observed_prompt_count']} prompts in "
                    f"that interval range from {observed_text} local time; validation checks "
                    f"that they remain within {window['start_inclusive']}–"
                    f"{window['end_exclusive']} local time."
                ),
            ]
        )

    lines.extend(
        [
            "",
            "## Reading order",
            "",
            (
                "| # | Researcher-local prompt window | UTC prompt window | "
                "Prompted by | Machine | Transition | Prompts | Native session |"
            ),
            "|---:|---|---|---|---|---|---:|---|",
        ]
    )
    for index, segment in enumerate(segments, start=1):
        local_window = format_window(
            segment["first_local"], segment["last_local"], include_zone=True
        )
        utc_window = format_window(
            segment["first_timestamp"],
            segment["last_timestamp"],
            include_zone=True,
        )
        session_start_path = "/".join(Path(segment["bundle_path"]).parts[1:4])
        session_label = f"{session_start_path} / {segment['session_id'][:8]}…"
        session_link = f"[{session_label}]({segment['bundle_path']})"
        lines.append(
            "| "
            + " | ".join(
                [
                    str(index),
                    local_window,
                    utc_window,
                    f"`{segment['researcher_id']}`",
                    f"`{segment['source_machine']}`",
                    segment["transition"],
                    str(segment["prompt_count"]),
                    session_link,
                ]
            )
            + " |"
        )
    lines.append("")
    rendered = "\n".join(lines)
    digest = hashlib.sha256(rendered.encode("utf-8")).hexdigest()
    metadata = {
        "path": policy["path"],
        "source": "history.filtered.jsonl",
        "default_timezone": policy["default_timezone"],
        "timezone_overrides": evidence,
        "segment_count": len(segments),
        "prompt_count": len(history),
        "sha256": digest,
    }
    return rendered, metadata, segments


def regenerate_guide(bundle_root: Path) -> tuple[int, int]:
    manifest_path = bundle_root / "manifest.json"
    manifest = load_json(manifest_path)
    history = load_jsonl(bundle_root / "history.filtered.jsonl")
    guide, metadata, segments = render_guide(manifest, history)
    guide_path = bundle_root / metadata["path"]
    guide_path.write_text(guide, encoding="utf-8")
    manifest["chronology_guide"] = metadata
    manifest_path.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    return len(segments), len(history)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--bundle-root",
        default=str(Path(__file__).resolve().parents[1]),
        help="Bundle root containing manifest.json and history.filtered.jsonl.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    segment_count, prompt_count = regenerate_guide(Path(args.bundle_root).resolve())
    print(f"wrote {segment_count} chronology segments for {prompt_count} prompts")


if __name__ == "__main__":
    main()
