#!/usr/bin/env node

import { execFileSync } from "node:child_process";
import { existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { homedir } from "node:os";
import { dirname, join, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const reportDir = dirname(fileURLToPath(import.meta.url));
const repoRoot = resolve(reportDir, "..");
const sessionsRoot =
  process.env.CODEX_MCP_SESSIONS_DIR ??
  join(homedir(), ".codex", "sessions", "2026", "06");
const logDb =
  process.env.CODEX_MCP_LOG_DB ??
  join(homedir(), ".codex", "logs_2.sqlite");
const outJson =
  process.env.MCP_EVIDENCE_JSON ?? join(reportDir, "mcp-evidence.json");
const outCsv =
  process.env.MCP_EVIDENCE_CSV ?? join(reportDir, "mcp-evidence.csv");

const categoryDefinitions = {
  auto_malformed_search_payload: {
    title: "agda_auto reports a CLI-flag parse error as a solution",
    expected:
      "A failed proof search should be `ok: false` or `hasSolution: false`, and CLI flags should not be parsed as Agda terms.",
  },
  ok_true_embedded_agda_error: {
    title: "Tool result is ok even though the payload contains an Agda error",
    expected:
      "If the main requested check/inference fails, the structured result should make that failure machine-readable.",
  },
  failed_status_but_ok_true: {
    title: "Structured result says ok even though the user-facing status is failed",
    expected:
      "`ok` should describe whether the requested MCP operation succeeded, not only whether the server returned a JSON payload.",
  },
  ok_true_no_checked_term: {
    title: "Context-check tool says ok but returns no checked term",
    expected:
      "A context-check tool should distinguish successfully checked terms from failed scope/type checks.",
  },
  state_change_success_after_reload_errors: {
    title: "State-changing tools report success after writing code that reloads with errors",
    expected:
      "Mutation tools should expose `editApplied`, `reloadOk`, and post-reload diagnostics separately, and should not present a failed reload as a solved goal.",
  },
  holes_reported_zero_goals: {
    title: "File has holes but reports zero visible and invisible goals",
    expected:
      "`goalCount` is useful, but completeness should clearly distinguish no interaction goals from no holes/metas.",
  },
  timeout_no_protocol_response: {
    title: "Load timed out after no protocol responses",
    expected:
      "Timeouts should report whether Agda is still checking, blocked, crashed, or not producing protocol output.",
  },
  timeout_diagnostic_overstates_crash: {
    title: "Timeout guidance suggests a crash when the evidence is only no response",
    expected:
      "Timeout diagnostics should not primarily suggest missing Agda/crash unless the subprocess actually exited or failed to start.",
  },
  wall_time_elapsed_mismatch: {
    title: "Outer wall time and MCP elapsedMs disagree substantially",
    expected:
      "A user-visible duration should explain queueing, protocol wait, Agda check time, and postprocessing time consistently.",
  },
  stale_reload_classification_flip: {
    title: "Stale reload changes classification without enough explanation",
    expected:
      "Reload output should explain whether classification changed because the file changed, cache was stale, or previous state was invalid.",
  },
  availability_or_startup_friction: {
    title: "MCP availability or startup friction",
    expected:
      "Tool discovery/startup failures should explain whether the server is missing, still starting, cancelled, or exited.",
  },
  raw_agda_required_as_acceptance_gate: {
    title: "Raw Agda remained necessary as the acceptance gate",
    expected:
      "If an MCP tool claims completeness, its meaning should be precise enough that users know whether raw Agda verification is still required.",
  },
};

function walkJsonl(dir, out = []) {
  if (!existsSync(dir)) return out;
  for (const entry of execFileSync("find", [dir, "-type", "f", "-name", "*.jsonl", "-print"], {
    encoding: "utf8",
  })
    .split("\n")
    .filter(Boolean)) {
    out.push(entry);
  }
  return out.sort();
}

function parseJson(line) {
  try {
    return JSON.parse(line);
  } catch {
    return null;
  }
}

function safeString(value) {
  if (value == null) return "";
  if (typeof value === "string") return value;
  try {
    return JSON.stringify(value);
  } catch {
    return String(value);
  }
}

function redact(text, max = 700) {
  return safeString(text)
    .replaceAll(homedir(), "~")
    .replaceAll(repoRoot, "$REPO")
    .replace(/rollout-[0-9T:-]+-[0-9a-f-]+\.jsonl/g, "rollout-SESSION.jsonl")
    .replace(/\s+/g, " ")
    .trim()
    .slice(0, max);
}

function summarizeArgs(args) {
  const copy = JSON.parse(JSON.stringify(args ?? {}));
  if (typeof copy.expr === "string" && copy.expr.length > 220) {
    copy.expr = `${copy.expr.slice(0, 220)}...`;
  }
  return copy;
}

function structuredFromEndPayload(payload) {
  const ok = payload?.result?.Ok;
  if (!ok) return null;
  return ok.structuredContent ?? null;
}

function contentTextFromEndPayload(payload) {
  const content = payload?.result?.Ok?.content;
  if (!Array.isArray(content)) return "";
  return content.map((item) => item.text ?? "").join("\n");
}

function parseVisibleToolJson(output) {
  const text = safeString(output);
  const index = text.indexOf('{"tool":"agda_');
  if (index < 0) return null;
  try {
    return JSON.parse(text.slice(index));
  } catch {
    return null;
  }
}

function parseWallTimeMs(output) {
  const m = /^Wall time: ([0-9.]+) seconds/m.exec(safeString(output));
  return m ? Math.round(Number(m[1]) * 1000) : null;
}

function ensureCall(calls, callId) {
  if (!calls.has(callId)) calls.set(callId, { callId });
  return calls.get(callId);
}

function collectSessionCalls(files) {
  const calls = new Map();
  const nonToolEvidence = [];
  const nonToolEvidenceSeen = new Set();
  const sessionMetas = [];

  function pushNonToolEvidence(item) {
    const key = `${item.category}\0${item.excerpt}`;
    if (nonToolEvidenceSeen.has(key)) return;
    nonToolEvidenceSeen.add(key);
    nonToolEvidence.push(item);
  }

  for (const file of files) {
    const relFile = relative(sessionsRoot, file);
    const lines = readFileSync(file, "utf8").split("\n").filter(Boolean);
    for (let i = 0; i < lines.length; i += 1) {
      const event = parseJson(lines[i]);
      if (!event) continue;
      const payload = event.payload ?? {};
      const line = i + 1;

      if (event.type === "session_meta" || payload.type === "session_meta") {
        sessionMetas.push({ file: relFile, line, timestamp: event.timestamp, payload });
      }

      if (
        payload.type === "custom_tool_call" &&
        typeof payload.name === "string" &&
        payload.name.startsWith("agda_")
      ) {
        const call = ensureCall(calls, payload.call_id);
        Object.assign(call, {
          callId: payload.call_id,
          tool: payload.name,
          startTimestamp: event.timestamp,
          callFile: relFile,
          callLine: line,
          arguments: safeString(payload.input),
        });
      }

      if (
        payload.type === "mcp_tool_call_end" &&
        payload.invocation?.server === "agda"
      ) {
        const call = ensureCall(calls, payload.call_id);
        const structured = structuredFromEndPayload(payload);
        Object.assign(call, {
          callId: payload.call_id,
          tool: payload.invocation.tool,
          arguments: summarizeArgs(payload.invocation.arguments),
          endTimestamp: event.timestamp,
          endFile: relFile,
          endLine: line,
          durationMs:
            payload.duration != null
              ? payload.duration.secs * 1000 + Math.round(payload.duration.nanos / 1e6)
              : null,
          structured,
          contentText: contentTextFromEndPayload(payload),
        });
      }

      if (payload.type === "function_call_output") {
        const call = calls.get(payload.call_id);
        if (call) {
          const visibleJson = parseVisibleToolJson(payload.output);
          call.outputFile = relFile;
          call.outputLine = line;
          call.visibleOutput = safeString(payload.output);
          call.wallTimeMs = parseWallTimeMs(payload.output);
          if (!call.structured && visibleJson) call.structured = visibleJson;
        }

        const output = safeString(payload.output);
        if (
          /Output:\s*#!\/usr\/bin\/env bash\s+# Sound Agda verification[\s\S]{0,900}Use THIS \(raw agda\), NOT the agda-mcp-server/.test(
            output,
          )
        ) {
          pushNonToolEvidence({
            source: "session-jsonl",
            file: relFile,
            line,
            timestamp: event.timestamp,
            category: "raw_agda_required_as_acceptance_gate",
            excerpt: redact(output),
          });
        }
      }
    }
  }

  return { calls: [...calls.values()].filter((c) => c.tool?.startsWith("agda_")), nonToolEvidence, sessionMetas };
}

function classifyCall(call) {
  const categories = new Set();
  const structured = call.structured ?? {};
  const data = structured.data ?? {};
  const text = [
    safeString(structured),
    call.contentText,
    call.visibleOutput,
  ].join("\n");

  if (
    call.tool === "agda_auto" &&
    /Not in scope:\s+-d/.test(text) &&
    /hasSolution"?\s*:\s*true/.test(text)
  ) {
    categories.add("auto_malformed_search_payload");
  }

  if (
    structured.ok === true &&
    /error: \[[A-Za-z]/.test(text)
  ) {
    categories.add("ok_true_embedded_agda_error");
  }

  if (
    structured.ok === true &&
    (/\*\*Status:\*\* FAILED/.test(text) ||
      structured.classification === "type-error" ||
      structured.classification === "tool-error")
  ) {
    categories.add("failed_status_but_ok_true");
  }

  if (
    structured.ok === true &&
    call.tool === "agda_goal_type_context_check" &&
    /no checked term returned/.test(text)
  ) {
    categories.add("ok_true_no_checked_term");
  }

  if (
    structured.ok === true &&
    /Reloaded with errors/i.test(text) &&
    /Goal diff:/i.test(text)
  ) {
    categories.add("state_change_success_after_reload_errors");
  }

  if (
    structured.classification === "ok-with-holes" &&
    data.hasHoles === true &&
    data.goalCount === 0 &&
    (data.invisibleGoalCount ?? 0) === 0
  ) {
    categories.add("holes_reported_zero_goals");
  }

  if (
    structured.classification === "process-error" ||
    /sendCommand timed out after 120000ms/.test(text)
  ) {
    categories.add("timeout_no_protocol_response");
  }

  if (
    /sendCommand timed out after 120000ms/.test(text) &&
    /subprocess crashed or could not be started/.test(text)
  ) {
    categories.add("timeout_diagnostic_overstates_crash");
  }

  if (
    typeof call.wallTimeMs === "number" &&
    typeof structured.elapsedMs === "number" &&
    call.wallTimeMs > 30000 &&
    call.wallTimeMs > structured.elapsedMs * 5
  ) {
    categories.add("wall_time_elapsed_mismatch");
  }

  if (
    data.staleBeforeLoad === true &&
    data.previousClassification &&
    data.previousClassification !== structured.classification
  ) {
    categories.add("stale_reload_classification_flip");
  }

  return [...categories];
}

function callEvidence(call, categories) {
  const structured = call.structured ?? {};
  const data = structured.data ?? {};
  return {
    call_id: call.callId,
    tool: call.tool,
    timestamp: call.endTimestamp ?? call.startTimestamp ?? null,
    source_file: call.endFile ?? call.callFile ?? call.outputFile ?? null,
    source_line: call.endLine ?? call.callLine ?? call.outputLine ?? null,
    categories,
    ok: structured.ok ?? null,
    classification: structured.classification ?? null,
    goal_count: data.goalCount ?? null,
    invisible_goal_count: data.invisibleGoalCount ?? null,
    has_holes: data.hasHoles ?? null,
    is_complete: data.isComplete ?? null,
    elapsed_ms: structured.elapsedMs ?? null,
    wall_time_ms: call.wallTimeMs ?? null,
    duration_ms: call.durationMs ?? null,
    server_version: structured.provenance?.serverVersion ?? null,
    agda_version: structured.provenance?.agdaVersion ?? null,
    arguments: call.arguments,
    excerpt: redact(
      call.contentText ||
        structured.summary ||
        call.visibleOutput ||
        structured.data?.text ||
        "",
    ),
  };
}

function collectRuntimeEvidence() {
  if (!existsSync(logDb)) return [];
  const query = `
    SELECT datetime(ts,'unixepoch') AS time, level, target,
           substr(feedback_log_body, 1, 900) AS body
      FROM logs
     WHERE lower(target) LIKE '%mcp%'
        OR lower(feedback_log_body) LIKE '%mcp%'
        OR lower(feedback_log_body) LIKE '%server_name=agda%'
        OR lower(feedback_log_body) LIKE '%task cancelled%'
        OR lower(feedback_log_body) LIKE '%sigterm%'
     ORDER BY ts, ts_nanos;
  `;
  let rows = [];
  try {
    rows = JSON.parse(execFileSync("sqlite3", ["-json", logDb, query], { encoding: "utf8" }));
  } catch {
    return [];
  }
  return rows
    .filter((row) => !/run_sampling_request|session_loop/.test(row.body ?? ""))
    .filter((row) =>
      /list_tools_for_server\{server_name=agda|server_name=agda[^}]*startup_complete=false|serve_inner: (task cancelled|Child exited|serve finished|deregistering)|SIGTERM|codex_mcp|rmcp/i.test(
        row.body ?? "",
      ),
    )
    .slice(0, 80)
    .map((row) => ({
      source: "logs_2.sqlite",
      category: "availability_or_startup_friction",
      timestamp: row.time,
      level: row.level,
      target: row.target,
      excerpt: redact(row.body),
    }));
}

function csvEscape(value) {
  const text = safeString(value);
  if (/[",\n]/.test(text)) return `"${text.replaceAll('"', '""')}"`;
  return text;
}

function writeCsv(rows) {
  const headers = [
    "category",
    "timestamp",
    "source_file",
    "source_line",
    "tool",
    "classification",
    "ok",
    "goal_count",
    "has_holes",
    "elapsed_ms",
    "wall_time_ms",
    "excerpt",
  ];
  const body = [
    headers.join(","),
    ...rows.map((row) =>
      headers
        .map((header) =>
          csvEscape(
            header === "category"
              ? row.categories?.join(";") ?? row.category
              : row[header],
          ),
        )
        .join(","),
    ),
  ].join("\n");
  writeFileSync(outCsv, `${body}\n`);
}

function main() {
  const files = walkJsonl(sessionsRoot);
  const { calls, nonToolEvidence, sessionMetas } = collectSessionCalls(files);
  const runtimeEvidence = collectRuntimeEvidence();

  const toolCounts = {};
  const classificationCounts = {};
  const serverVersions = new Set();
  const agdaVersions = new Set();
  const categoryOccurrences = {};
  const allOccurrences = [];
  const unclassifiedSuspicious = [];
  let correctlySurfacedAgdaErrors = 0;

  for (const call of calls) {
    toolCounts[call.tool] = (toolCounts[call.tool] ?? 0) + 1;
    const structured = call.structured ?? {};
    if (structured.classification) {
      classificationCounts[structured.classification] =
        (classificationCounts[structured.classification] ?? 0) + 1;
    }
    if (structured.provenance?.serverVersion) serverVersions.add(structured.provenance.serverVersion);
    if (structured.provenance?.agdaVersion) agdaVersions.add(structured.provenance.agdaVersion);

    const categories = classifyCall(call);
    const text = safeString(structured) + "\n" + safeString(call.contentText);
    const hasAgdaError = /error: \[[A-Za-z]/.test(text);
    if (
      hasAgdaError &&
      structured.ok === false &&
      structured.classification !== "process-error"
    ) {
      correctlySurfacedAgdaErrors += 1;
    }
    if (categories.length > 0) {
      const evidence = callEvidence(call, categories);
      allOccurrences.push(evidence);
      for (const category of categories) {
        (categoryOccurrences[category] ??= []).push(evidence);
      }
    } else if (
      structured.ok === true &&
      (/error: \[[A-Za-z]/.test(text) || /no checked term returned/.test(text))
    ) {
      unclassifiedSuspicious.push(callEvidence(call, []));
    }
  }

  for (const evidence of [...nonToolEvidence, ...runtimeEvidence]) {
    (categoryOccurrences[evidence.category] ??= []).push(evidence);
  }

  const categorySummary = Object.entries(categoryDefinitions).map(([id, definition]) => {
    const occurrences = categoryOccurrences[id] ?? [];
    return {
      id,
      ...definition,
      count: occurrences.length,
      representative_evidence: occurrences.slice(0, 5),
    };
  });

  const evidence = {
    generated_at: new Date().toISOString(),
    generator: relative(repoRoot, fileURLToPath(import.meta.url)),
    sources: {
      sessions_root: sessionsRoot.replace(homedir(), "~"),
      session_files_scanned: files.map((file) => relative(sessionsRoot, file)),
      log_db: existsSync(logDb) ? logDb.replace(homedir(), "~") : null,
    },
    environment_observed: {
      server_versions: [...serverVersions].sort(),
      agda_versions: [...agdaVersions].sort(),
      session_cli_versions: [
        ...new Set(sessionMetas.map((m) => m.payload?.cli_version).filter(Boolean)),
      ].sort(),
    },
    totals: {
      agda_mcp_calls: calls.length,
      anomalous_call_occurrences: allOccurrences.length,
      non_tool_evidence_items: nonToolEvidence.length,
      runtime_evidence_items: runtimeEvidence.length,
      unclassified_suspicious_items: unclassifiedSuspicious.length,
      correctly_surfaced_agda_error_calls: correctlySurfacedAgdaErrors,
    },
    tool_counts: Object.fromEntries(Object.entries(toolCounts).sort()),
    classification_counts: Object.fromEntries(Object.entries(classificationCounts).sort()),
    category_summary: categorySummary,
    all_classified_call_occurrences: allOccurrences,
    non_tool_evidence: nonToolEvidence,
    runtime_evidence: runtimeEvidence,
    unclassified_suspicious: unclassifiedSuspicious,
    completeness_notes: [
      "All session JSONL files under sources.sessions_root were parsed.",
      "Every agda_* MCP call found in custom_tool_call or mcp_tool_call_end events was counted.",
      "Anomaly categories are symptom-based; repeated instances are retained in all_classified_call_occurrences and summarized by category.",
      "Ordinary Agda type errors surfaced as ok:false are counted separately as correctly_surfaced_agda_error_calls, not as MCP bugs.",
      "Sensitive or irrelevant transcript text is not copied verbatim; excerpts are shortened and home/repo paths are redacted.",
    ],
  };

  mkdirSync(dirname(outJson), { recursive: true });
  writeFileSync(outJson, `${JSON.stringify(evidence, null, 2)}\n`);
  writeCsv([...allOccurrences, ...nonToolEvidence, ...runtimeEvidence]);

  console.log(`Scanned ${files.length} session files.`);
  console.log(`Counted ${calls.length} Agda MCP calls.`);
  console.log(`Wrote ${relative(repoRoot, outJson)} and ${relative(repoRoot, outCsv)}.`);
  console.log(`Unclassified suspicious items: ${unclassifiedSuspicious.length}.`);
}

main();
