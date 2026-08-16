#!/usr/bin/env python3

from __future__ import annotations

import copy
import datetime as dt
import importlib.util
import unittest
from pathlib import Path
from zoneinfo import ZoneInfo


SCRIPT_PATH = Path(__file__).with_name("generate_chronology_guide.py")
SPEC = importlib.util.spec_from_file_location("generate_chronology_guide", SCRIPT_PATH)
assert SPEC is not None and SPEC.loader is not None
CHRONOLOGY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHRONOLOGY)

VALIDATOR_PATH = Path(__file__).with_name("validate_codex_history.py")
VALIDATOR_SPEC = importlib.util.spec_from_file_location(
    "validate_codex_history", VALIDATOR_PATH
)
assert VALIDATOR_SPEC is not None and VALIDATOR_SPEC.loader is not None
VALIDATOR = importlib.util.module_from_spec(VALIDATOR_SPEC)
VALIDATOR_SPEC.loader.exec_module(VALIDATOR)


def epoch(local_timestamp: str, timezone: str) -> float:
    local = dt.datetime.fromisoformat(local_timestamp).replace(tzinfo=ZoneInfo(timezone))
    return local.timestamp()


def session(session_id: str, machine: str, day: str) -> dict[str, object]:
    return {
        "session_id": session_id,
        "source_machine": machine,
        "researcher_id": "<RESEARCHER_1>",
        "started_at": f"{day}T12:00:00Z",
        "bundle_path": f"sessions/{day.replace('-', '/')}/{session_id}.jsonl",
    }


def history_entry(session_id: str, machine: str, timestamp: float) -> dict[str, object]:
    return {
        "session_id": session_id,
        "source_machine": machine,
        "researcher_id": "<RESEARCHER_1>",
        "ts": timestamp,
        "text": "redacted test prompt",
    }


class ChronologyGuideTest(unittest.TestCase):
    def setUp(self) -> None:
        self.manifest = {
            "sessions": [
                session("linux-session", "linux-laptop", "2026-06-08"),
                session("mac-session", "mac-local", "2026-06-09"),
            ]
        }
        self.policy = {
            "path": "CHRONOLOGY.md",
            "default_timezone": "America/New_York",
            "timezone_overrides": [
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
                    "expected_prompt_count": 3,
                    "notes": "test override",
                }
            ],
        }

    def test_groups_days_and_labels_machine_handoffs(self) -> None:
        history = [
            history_entry(
                "linux-session",
                "linux-laptop",
                epoch("2026-06-08T09:00:00", "Europe/Stockholm"),
            ),
            history_entry(
                "linux-session",
                "linux-laptop",
                epoch("2026-06-09T10:00:00", "Europe/Stockholm"),
            ),
            history_entry(
                "mac-session",
                "mac-local",
                epoch("2026-06-09T10:00:00", "America/New_York"),
            ),
            history_entry(
                "linux-session",
                "linux-laptop",
                epoch("2026-06-09T18:00:00", "Europe/Stockholm"),
            ),
        ]

        guide, metadata, segments = CHRONOLOGY.render_guide(
            self.manifest, history, self.policy
        )

        self.assertEqual(metadata["prompt_count"], 4)
        self.assertEqual(metadata["segment_count"], 4)
        self.assertEqual(
            [segment["transition"] for segment in segments],
            [
                "Archive begins",
                "Continued session on a new local day",
                "Machine handoff to a new session",
                "Machine handoff; resumed earlier session",
            ],
        )
        evidence = metadata["timezone_overrides"][0]
        self.assertEqual(evidence["observed_prompt_count"], 3)
        self.assertEqual(
            evidence["observed_prompt_time_range_local"],
            {"start": "09:00", "end": "18:00"},
        )
        self.assertIn("`<RESEARCHER_1>`", guide)
        self.assertIn("sessions/2026/06/08/linux-session.jsonl", guide)

    def test_splits_when_the_display_timezone_changes(self) -> None:
        history = [
            history_entry(
                "linux-session",
                "linux-laptop",
                epoch("2026-06-12T20:00:00", "Europe/Stockholm"),
            ),
            history_entry(
                "linux-session",
                "linux-laptop",
                epoch("2026-06-13T00:30:00", "Europe/Stockholm"),
            ),
        ]

        segments = CHRONOLOGY.build_segments(self.manifest, history, self.policy)

        self.assertEqual(len(segments), 2)
        self.assertEqual(segments[0]["timezone"], "Europe/Stockholm")
        self.assertEqual(segments[1]["timezone"], "America/New_York")
        self.assertEqual(
            segments[1]["transition"],
            "Continued session; display timezone changes",
        )


    def test_validates_prompt_count_and_daytime_evidence(self) -> None:
        chronology = {
            "timezone_overrides": [
                {
                    "expected_prompt_count": 67,
                    "observed_prompt_count": 67,
                    "observed_prompt_time_range_local": {
                        "start": "09:07",
                        "end": "19:08",
                    },
                    "daytime_window_local": {
                        "start_inclusive": "07:00",
                        "end_exclusive": "21:00",
                    },
                }
            ]
        }
        VALIDATOR.validate_timezone_evidence(chronology)

        wrong_count = copy.deepcopy(chronology)
        wrong_count["timezone_overrides"][0]["observed_prompt_count"] = 66
        with self.assertRaisesRegex(ValueError, "prompt-count mismatch"):
            VALIDATOR.validate_timezone_evidence(wrong_count)

        outside_window = copy.deepcopy(chronology)
        outside_window["timezone_overrides"][0][
            "observed_prompt_time_range_local"
        ]["end"] = "21:00"
        with self.assertRaisesRegex(ValueError, "outside daytime window"):
            VALIDATOR.validate_timezone_evidence(outside_window)


if __name__ == "__main__":
    unittest.main()
