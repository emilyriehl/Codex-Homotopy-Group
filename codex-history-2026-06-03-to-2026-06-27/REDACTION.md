# Redaction Policy

The goal is to preserve a transparent technical record while removing sensitive
or identifying details that are not needed to understand the autoformalization
work.

## Automated Redactions

The sanitizer replaces:

- personal names and account names with stable pseudonyms when supplied as
  private `--redact-term` arguments;
- macOS and Linux home paths with placeholders;
- absolute checkout paths with repository placeholders;
- email addresses;
- OpenAI API keys, organization ids, and project ids;
- GitHub access tokens;
- bearer tokens;
- repository remotes that contain a personal GitHub username.

The JSONL structure, event order, session ids, relative repository paths,
commit hashes, theorem names, Agda names, prompts, assistant responses, and tool
events are otherwise preserved.

The current macOS import used private literal redaction terms for researcher
names and local account names. The raw values are deliberately not recorded in
this repository.

## Manual Review Checklist

Before publishing or committing a regenerated bundle, validate that:

- every `.jsonl` file parses line-by-line as JSON;
- `manifest.json` session count matches the number of sanitized session files;
- `history.filtered.jsonl` contains only entries for included session ids;
- searches for likely secrets and private identifiers return no matches.

Suggested searches:

```sh
rg -n 'sk-|OPENAI_API_KEY|org-|proj_|github_pat_|ghp_|Authorization: Bearer' codex-history-2026-06-03-to-2026-06-27/sessions codex-history-2026-06-03-to-2026-06-27/history.filtered.jsonl codex-history-2026-06-03-to-2026-06-27/manifest.json
rg -n '/Users/|/home/|@' codex-history-2026-06-03-to-2026-06-27/sessions codex-history-2026-06-03-to-2026-06-27/history.filtered.jsonl codex-history-2026-06-03-to-2026-06-27/manifest.json
```

If a search finds a real sensitive value, update
`tools/sanitize_codex_history.py`, regenerate the bundle, and rerun the checks.
