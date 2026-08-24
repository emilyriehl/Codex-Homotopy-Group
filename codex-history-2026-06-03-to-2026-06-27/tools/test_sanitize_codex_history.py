#!/usr/bin/env python3

from __future__ import annotations

import argparse
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


SCRIPT_PATH = Path(__file__).with_name("sanitize_codex_history.py")
SPEC = importlib.util.spec_from_file_location("sanitize_codex_history", SCRIPT_PATH)
assert SPEC is not None and SPEC.loader is not None
SANITIZER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SANITIZER)


def write_jsonl(path: Path, entries: list[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for entry in entries:
            handle.write(json.dumps(entry) + "\n")


class MergeBundleTest(unittest.TestCase):
    def test_preserves_existing_machine_and_sorts_combined_history(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            root = Path(temporary_directory)
            output_root = root / "bundle"
            source_root = root / "codex" / "sessions"
            history_file = root / "codex" / "history.jsonl"
            repo_root = "/home/researcher/Codex-Homotopy-Group"

            mac_bundle_path = Path("sessions/2026/06/03/mac.jsonl")
            mac_session_path = output_root / mac_bundle_path
            mac_entries = [
                {
                    "timestamp": "2026-06-03T12:00:00Z",
                    "type": "session_meta",
                    "payload": {
                        "id": "mac-session",
                        "timestamp": "2026-06-03T12:00:00Z",
                        "cwd": "/Users/researcher/Codex-Homotopy-Group",
                    },
                },
                {
                    "timestamp": "2026-06-03T12:01:00Z",
                    "type": "event_msg",
                    "payload": {"message": "Ada used the Mac."},
                },
            ]
            write_jsonl(mac_session_path, mac_entries)
            mac_line_count, mac_digest = SANITIZER.write_redacted_jsonl(
                mac_session_path, output_root / "mac-copy.jsonl", []
            )
            (output_root / "mac-copy.jsonl").unlink()

            existing_manifest = {
                "selection_rule": {
                    "source_root_redacted": "<HOME>/.codex/sessions",
                    "repo_cwd_match_redacted": "<REPO_ROOT>",
                    "include_if": "test selection rule",
                },
                "sessions": [
                    {
                        "session_id": "mac-session",
                        "source_machine": "mac-local",
                        "researcher_id": "<RESEARCHER_1>",
                        "original_path_redacted": "<HOME>/.codex/sessions/mac.jsonl",
                        "bundle_path": str(mac_bundle_path),
                        "started_at": "2026-06-03T12:00:00Z",
                        "first_event_at": "2026-06-03T12:00:00+00:00",
                        "last_event_at": "2026-06-03T12:01:00+00:00",
                        "source_line_count": mac_line_count,
                        "sanitized_line_count": mac_line_count,
                        "sanitized_sha256": mac_digest,
                        "source_machine_note": "existing Mac record",
                    }
                ],
            }
            output_root.mkdir(parents=True, exist_ok=True)
            (output_root / "manifest.json").write_text(
                json.dumps(existing_manifest), encoding="utf-8"
            )
            write_jsonl(
                output_root / "history.filtered.jsonl",
                [
                    {
                        "session_id": "mac-session",
                        "researcher_id": "<RESEARCHER_1>",
                        "source_machine": "mac-local",
                        "ts": 200,
                        "text": "Ada on Mac",
                    }
                ],
            )

            linux_session_path = (
                source_root / "2026/06/04/rollout-2026-06-04-linux.jsonl"
            )
            write_jsonl(
                linux_session_path,
                [
                    {
                        "timestamp": "2026-06-04T12:00:00Z",
                        "type": "session_meta",
                        "payload": {
                            "id": "linux-session",
                            "timestamp": "2026-06-04T12:00:00Z",
                            "cwd": repo_root,
                        },
                    },
                    {
                        "timestamp": "2026-06-04T12:01:00Z",
                        "type": "event_msg",
                        "payload": {"message": "Ada used Linux."},
                    },
                ],
            )
            write_jsonl(
                history_file,
                [
                    {
                        "session_id": "linux-session",
                        "ts": 100,
                        "text": "Ada on Linux",
                    }
                ],
            )

            args = argparse.Namespace(
                source_root=str(source_root),
                history_file=str(history_file),
                repo_root=repo_root,
                output_root=str(output_root),
                source_machine="linux-laptop",
                researcher_id="<RESEARCHER_1>",
                session_id=[],
                redact_term=["Ada=<RESEARCHER_1>"],
            )
            self.assertEqual(SANITIZER.build_bundle(args), 1)

            manifest = json.loads(
                (output_root / "manifest.json").read_text(encoding="utf-8")
            )
            self.assertEqual(manifest["session_count"], 2)
            self.assertEqual(manifest["history_entry_count"], 2)
            self.assertEqual(
                [machine["label"] for machine in manifest["source_machines"]],
                ["mac-local", "linux-laptop"],
            )
            self.assertEqual(
                [rule["source_machine"] for rule in manifest["selection_rules"]],
                ["mac-local", "linux-laptop"],
            )
            self.assertTrue(manifest["status"].startswith("complete:"))
            self.assertEqual(
                manifest["researchers"][0]["source_machines"],
                ["mac-local", "linux-laptop"],
            )
            self.assertTrue(
                all(
                    session["researcher_id"] == "<RESEARCHER_1>"
                    for session in manifest["sessions"]
                )
            )

            self.assertEqual(manifest["chronology_guide"]["prompt_count"], 2)
            self.assertEqual(manifest["chronology_guide"]["segment_count"], 2)
            chronology = (output_root / "CHRONOLOGY.md").read_text(
                encoding="utf-8"
            )
            self.assertIn("`<RESEARCHER_1>`", chronology)
            self.assertIn(str(mac_bundle_path), chronology)

            history = SANITIZER.load_jsonl(output_root / "history.filtered.jsonl")
            self.assertEqual([entry["ts"] for entry in history], [100, 200])
            self.assertEqual(
                [entry["source_machine"] for entry in history],
                ["linux-laptop", "mac-local"],
            )
            self.assertTrue(
                all(entry["researcher_id"] == "<RESEARCHER_1>" for entry in history)
            )
            self.assertTrue(
                all("Ada" not in json.dumps(entry) for entry in history), history
            )
            self.assertIn(
                "<RESEARCHER_1>", mac_session_path.read_text(encoding="utf-8")
            )

            self.assertEqual(SANITIZER.build_bundle(args), 1)
            rerun_manifest = json.loads(
                (output_root / "manifest.json").read_text(encoding="utf-8")
            )
            self.assertEqual(rerun_manifest["session_count"], 2)
            self.assertEqual(rerun_manifest["history_entry_count"], 2)

            args.session_id = ["linux-session"]
            self.assertEqual(SANITIZER.build_bundle(args), 1)
            targeted_manifest = json.loads(
                (output_root / "manifest.json").read_text(encoding="utf-8")
            )
            self.assertEqual(targeted_manifest["session_count"], 2)
            self.assertEqual(targeted_manifest["history_entry_count"], 2)

    def test_preserves_distinct_researchers_when_adding_a_machine(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            root = Path(temporary_directory)
            output_root = root / "bundle"
            source_root = root / "codex" / "sessions"
            history_file = root / "codex" / "history.jsonl"
            repo_root = "/Users/researcher-two/Codex-Homotopy-Group"

            existing_path = Path("sessions/2026/06/03/existing.jsonl")
            existing_session_path = output_root / existing_path
            existing_entries = [
                {
                    "timestamp": "2026-06-03T12:00:00Z",
                    "type": "session_meta",
                    "payload": {
                        "id": "existing",
                        "cwd": "<REPO_ROOT>",
                        "message": "Researcher One must remain unchanged.",
                    },
                }
            ]
            write_jsonl(existing_session_path, existing_entries)
            copy_path = output_root / "copy.jsonl"
            line_count, digest = SANITIZER.write_redacted_jsonl(
                existing_session_path, copy_path, []
            )
            copy_path.unlink()
            manifest = {
                "sessions": [
                    {
                        "session_id": "existing",
                        "source_machine": "mac-local",
                        "researcher_id": "<RESEARCHER_1>",
                        "bundle_path": str(existing_path),
                        "started_at": "2026-06-03T12:00:00Z",
                        "first_event_at": "2026-06-03T12:00:00+00:00",
                        "last_event_at": "2026-06-03T12:00:00+00:00",
                        "sanitized_line_count": line_count,
                        "sanitized_sha256": digest,
                    }
                ]
            }
            output_root.mkdir(parents=True, exist_ok=True)
            (output_root / "manifest.json").write_text(
                json.dumps(manifest), encoding="utf-8"
            )
            write_jsonl(
                output_root / "history.filtered.jsonl",
                [
                    {
                        "session_id": "existing",
                        "source_machine": "mac-local",
                        "researcher_id": "<RESEARCHER_1>",
                        "ts": 100,
                        "text": "Researcher One existing prompt",
                    }
                ],
            )

            new_path = source_root / "2026/06/04/new.jsonl"
            write_jsonl(
                new_path,
                [
                    {
                        "timestamp": "2026-06-04T12:00:00Z",
                        "type": "session_meta",
                        "payload": {
                            "id": "new",
                            "timestamp": "2026-06-04T12:00:00Z",
                            "cwd": repo_root,
                        },
                    }
                ],
            )
            write_jsonl(
                history_file,
                [{"session_id": "new", "ts": 200, "text": "new prompt"}],
            )
            args = argparse.Namespace(
                source_root=str(source_root),
                history_file=str(history_file),
                repo_root=repo_root,
                output_root=str(output_root),
                source_machine="third-machine",
                researcher_id="<RESEARCHER_2>",
                session_id=[],
                redact_term=["Researcher One=<RESEARCHER_2>"],
            )

            self.assertEqual(SANITIZER.build_bundle(args), 1)
            combined_manifest = json.loads(
                (output_root / "manifest.json").read_text(encoding="utf-8")
            )
            self.assertEqual(
                [session["researcher_id"] for session in combined_manifest["sessions"]],
                ["<RESEARCHER_1>", "<RESEARCHER_2>"],
            )
            self.assertEqual(
                [item["researcher_id"] for item in combined_manifest["researchers"]],
                ["<RESEARCHER_1>", "<RESEARCHER_2>"],
            )
            history = SANITIZER.load_jsonl(output_root / "history.filtered.jsonl")
            self.assertEqual(
                [entry["researcher_id"] for entry in history],
                ["<RESEARCHER_1>", "<RESEARCHER_2>"],
            )
            self.assertIn(
                "Researcher One",
                existing_session_path.read_text(encoding="utf-8"),
            )
            self.assertIn("Researcher One", history[0]["text"])
            chronology = (output_root / "CHRONOLOGY.md").read_text(encoding="utf-8")
            self.assertIn("prompts from 2 researchers", chronology)
            self.assertIn("Researcher handoff", chronology)

            args.redact_term = []
            args.global_redact_term = ["Researcher One=<RESEARCHER_2>"]
            self.assertEqual(SANITIZER.build_bundle(args), 1)
            globally_redacted_history = SANITIZER.load_jsonl(
                output_root / "history.filtered.jsonl"
            )
            self.assertNotIn(
                "Researcher One",
                existing_session_path.read_text(encoding="utf-8"),
            )
            self.assertNotIn("Researcher One", globally_redacted_history[0]["text"])


if __name__ == "__main__":
    unittest.main()
