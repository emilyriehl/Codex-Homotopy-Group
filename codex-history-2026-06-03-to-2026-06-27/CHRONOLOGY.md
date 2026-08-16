# Chronological Reading Guide

This is a derived navigation guide for the native Codex session logs in
`sessions/`. It does not replace, split, or rewrite those files. Codex stores a
continued session under the date on which that session began, so the rows below
show when to continue in another file or return to an earlier one.

Rows are ordered by the absolute prompt timestamp. A "machine handoff" means
that the next recorded human prompt came from another machine; it does not claim
that Codex created a native session boundary. All prompts were made by the same
researcher, recorded under the stable pseudonym `<RESEARCHER_1>`.

## Time zones

The default researcher-local display timezone is `America/New_York`.

For `linux-laptop` from 2026-06-08 through 2026-06-12 inclusive, the display timezone is `Europe/Stockholm`. The 67 prompts in that interval range from 09:07–19:08 local time.

## Reading order

| # | Researcher-local prompt window | UTC prompt window | Prompted by | Machine | Transition | Prompts | Native session |
|---:|---|---|---|---|---|---:|---|
| 1 | 2026-06-03 12:39–12:45 EDT | 2026-06-03 16:39–16:45 UTC | `<RESEARCHER_1>` | `mac-local` | Archive begins | 5 | [2026/06/03 / 019e8e5a…](sessions/2026/06/03/rollout-2026-06-03T12-39-35-019e8e5a-cbb6-7dd3-a831-bdc9c70f9d7e.jsonl) |
| 2 | 2026-06-03 13:05–13:14 EDT | 2026-06-03 17:05–17:14 UTC | `<RESEARCHER_1>` | `mac-local` | New session on the same machine | 2 | [2026/06/03 / 019e8e6e…](sessions/2026/06/03/rollout-2026-06-03T13-01-33-019e8e6e-e65d-7cc2-bb1d-b15a3c73a937.jsonl) |
| 3 | 2026-06-03 13:17–17:59 EDT | 2026-06-03 17:17–21:59 UTC | `<RESEARCHER_1>` | `mac-local` | New session on the same machine | 17 | [2026/06/03 / 019e8e7c…](sessions/2026/06/03/rollout-2026-06-03T13-16-32-019e8e7c-9e68-77a0-9e93-44f7d1a9702d.jsonl) |
| 4 | 2026-06-04 11:22–12:22 EDT | 2026-06-04 15:22–16:22 UTC | `<RESEARCHER_1>` | `mac-local` | Continued session on a new local day | 5 | [2026/06/03 / 019e8e7c…](sessions/2026/06/03/rollout-2026-06-03T13-16-32-019e8e7c-9e68-77a0-9e93-44f7d1a9702d.jsonl) |
| 5 | 2026-06-04 14:28–14:28 EDT | 2026-06-04 18:28–18:28 UTC | `<RESEARCHER_1>` | `linux-laptop` | Machine handoff to a new session | 1 | [2026/06/04 / 019e93e4…](sessions/2026/06/04/rollout-2026-06-04T14-28-11-019e93e4-93d8-7eb3-8326-44ddebe76a80.jsonl) |
| 6 | 2026-06-05 15:27–16:50 EDT | 2026-06-05 19:27–20:50 UTC | `<RESEARCHER_1>` | `mac-local` | Machine handoff to a new session | 13 | [2026/06/05 / 019e9937…](sessions/2026/06/05/rollout-2026-06-05T15-16-19-019e9937-00a3-7422-b0f1-e35aac5023f5.jsonl) |
| 7 | 2026-06-08 09:41–09:41 CEST | 2026-06-08 07:41–07:41 UTC | `<RESEARCHER_1>` | `linux-laptop` | Machine handoff to a new session | 1 | [2026/06/08 / 019ea62e…](sessions/2026/06/08/rollout-2026-06-08T09-41-37-019ea62e-0f8f-7dc1-b299-d0a9524f612d.jsonl) |
| 8 | 2026-06-09 09:34–09:35 CEST | 2026-06-09 07:34–07:35 UTC | `<RESEARCHER_1>` | `linux-laptop` | New session on the same machine | 2 | [2026/06/09 / 019eab4c…](sessions/2026/06/09/rollout-2026-06-09T09-33-07-019eab4c-a3e3-7ba1-9c9d-8de6f19d9c99.jsonl) |
| 9 | 2026-06-09 09:42–09:42 CEST | 2026-06-09 07:42–07:42 UTC | `<RESEARCHER_1>` | `linux-laptop` | New session on the same machine | 1 | [2026/06/09 / 019eab53…](sessions/2026/06/09/rollout-2026-06-09T09-40-05-019eab53-05f6-7293-916d-8863329cd314.jsonl) |
| 10 | 2026-06-09 09:48–19:08 CEST | 2026-06-09 07:48–17:08 UTC | `<RESEARCHER_1>` | `linux-laptop` | New session on the same machine | 10 | [2026/06/09 / 019eab59…](sessions/2026/06/09/rollout-2026-06-09T09-47-19-019eab59-a52c-7ac0-b9f3-468aa4421fb7.jsonl) |
| 11 | 2026-06-10 11:59–14:26 CEST | 2026-06-10 09:59–12:26 UTC | `<RESEARCHER_1>` | `linux-laptop` | Continued session on a new local day | 30 | [2026/06/09 / 019eab59…](sessions/2026/06/09/rollout-2026-06-09T09-47-19-019eab59-a52c-7ac0-b9f3-468aa4421fb7.jsonl) |
| 12 | 2026-06-11 09:07–09:47 CEST | 2026-06-11 07:07–07:47 UTC | `<RESEARCHER_1>` | `linux-laptop` | Continued session on a new local day | 5 | [2026/06/09 / 019eab59…](sessions/2026/06/09/rollout-2026-06-09T09-47-19-019eab59-a52c-7ac0-b9f3-468aa4421fb7.jsonl) |
| 13 | 2026-06-11 09:58–09:58 CEST | 2026-06-11 07:58–07:58 UTC | `<RESEARCHER_1>` | `linux-laptop` | New session on the same machine | 1 | [2026/06/11 / 019eb5b1…](sessions/2026/06/11/rollout-2026-06-11T09-58-57-019eb5b1-0256-7453-b1b2-ab02cbe2d5bd.jsonl) |
| 14 | 2026-06-11 10:07–14:58 CEST | 2026-06-11 08:07–12:58 UTC | `<RESEARCHER_1>` | `linux-laptop` | Resumed earlier session | 14 | [2026/06/09 / 019eab59…](sessions/2026/06/09/rollout-2026-06-09T09-47-19-019eab59-a52c-7ac0-b9f3-468aa4421fb7.jsonl) |
| 15 | 2026-06-12 18:19–18:20 CEST | 2026-06-12 16:19–16:20 UTC | `<RESEARCHER_1>` | `linux-laptop` | Continued session on a new local day | 3 | [2026/06/09 / 019eab59…](sessions/2026/06/09/rollout-2026-06-09T09-47-19-019eab59-a52c-7ac0-b9f3-468aa4421fb7.jsonl) |
| 16 | 2026-06-12 20:07–21:25 EDT | 2026-06-13 00:07–01:25 UTC | `<RESEARCHER_1>` | `linux-laptop` | Continued session; display timezone changes | 3 | [2026/06/09 / 019eab59…](sessions/2026/06/09/rollout-2026-06-09T09-47-19-019eab59-a52c-7ac0-b9f3-468aa4421fb7.jsonl) |
| 17 | 2026-06-13 10:34–10:34 EDT | 2026-06-13 14:34–14:34 UTC | `<RESEARCHER_1>` | `linux-laptop` | New session on the same machine | 1 | [2026/06/13 / 019ec168…](sessions/2026/06/13/rollout-2026-06-13T10-34-51-019ec168-304b-7360-a955-692b30bfcdfa.jsonl) |
| 18 | 2026-06-13 10:35–22:56 EDT | 2026-06-13 14:35–2026-06-14 02:56 UTC | `<RESEARCHER_1>` | `linux-laptop` | Resumed earlier session | 6 | [2026/06/09 / 019eab59…](sessions/2026/06/09/rollout-2026-06-09T09-47-19-019eab59-a52c-7ac0-b9f3-468aa4421fb7.jsonl) |
| 19 | 2026-06-15 19:16–19:18 EDT | 2026-06-15 23:16–23:18 UTC | `<RESEARCHER_1>` | `linux-laptop` | Continued session on a new local day | 2 | [2026/06/09 / 019eab59…](sessions/2026/06/09/rollout-2026-06-09T09-47-19-019eab59-a52c-7ac0-b9f3-468aa4421fb7.jsonl) |
| 20 | 2026-06-16 08:23–08:23 EDT | 2026-06-16 12:23–12:23 UTC | `<RESEARCHER_1>` | `linux-laptop` | Continued session on a new local day | 1 | [2026/06/09 / 019eab59…](sessions/2026/06/09/rollout-2026-06-09T09-47-19-019eab59-a52c-7ac0-b9f3-468aa4421fb7.jsonl) |
| 21 | 2026-06-16 16:41–18:06 EDT | 2026-06-16 20:41–22:06 UTC | `<RESEARCHER_1>` | `mac-local` | Machine handoff to a new session | 9 | [2026/06/16 / 019ed22a…](sessions/2026/06/16/rollout-2026-06-16T16-40-50-019ed22a-546e-7b41-82fe-08a9944c64ec.jsonl) |
| 22 | 2026-06-17 19:46–19:46 EDT | 2026-06-17 23:46–23:46 UTC | `<RESEARCHER_1>` | `linux-laptop` | Machine handoff to a new session | 1 | [2026/06/17 / 019ed7fb…](sessions/2026/06/17/rollout-2026-06-17T19-46-53-019ed7fb-0992-72c3-b12c-0b2c7e1bd69f.jsonl) |
| 23 | 2026-06-17 19:48–21:21 EDT | 2026-06-17 23:48–2026-06-18 01:21 UTC | `<RESEARCHER_1>` | `linux-laptop` | New session on the same machine | 7 | [2026/06/17 / 019ed7fb…](sessions/2026/06/17/rollout-2026-06-17T19-47-43-019ed7fb-c934-71a3-9a01-61f564cef3e9.jsonl) |
| 24 | 2026-06-18 07:09–07:12 EDT | 2026-06-18 11:09–11:12 UTC | `<RESEARCHER_1>` | `linux-laptop` | Continued session on a new local day | 2 | [2026/06/17 / 019ed7fb…](sessions/2026/06/17/rollout-2026-06-17T19-47-43-019ed7fb-c934-71a3-9a01-61f564cef3e9.jsonl) |
| 25 | 2026-06-18 15:42–16:14 EDT | 2026-06-18 19:42–20:14 UTC | `<RESEARCHER_1>` | `mac-local` | Machine handoff to a new session | 7 | [2026/06/18 / 019edc41…](sessions/2026/06/18/rollout-2026-06-18T15-41-50-019edc41-0859-7512-a810-3d2182fd6563.jsonl) |
| 26 | 2026-06-18 16:28–16:44 EDT | 2026-06-18 20:28–20:44 UTC | `<RESEARCHER_1>` | `mac-local` | New session on the same machine | 6 | [2026/06/18 / 019edc6b…](sessions/2026/06/18/rollout-2026-06-18T16-28-07-019edc6b-6b4b-7d61-bd99-e144991bc81f.jsonl) |
| 27 | 2026-06-19 09:59–13:53 EDT | 2026-06-19 13:59–17:53 UTC | `<RESEARCHER_1>` | `mac-local` | Continued session on a new local day | 12 | [2026/06/18 / 019edc6b…](sessions/2026/06/18/rollout-2026-06-18T16-28-07-019edc6b-6b4b-7d61-bd99-e144991bc81f.jsonl) |
| 28 | 2026-06-19 19:00–21:42 EDT | 2026-06-19 23:00–2026-06-20 01:42 UTC | `<RESEARCHER_1>` | `linux-laptop` | Machine handoff to a new session | 14 | [2026/06/19 / 019ee21d…](sessions/2026/06/19/rollout-2026-06-19T19-00-19-019ee21d-1e42-7ae0-9434-f8c02df69a20.jsonl) |
| 29 | 2026-06-20 16:58–17:01 EDT | 2026-06-20 20:58–21:01 UTC | `<RESEARCHER_1>` | `linux-laptop` | Continued session on a new local day | 2 | [2026/06/19 / 019ee21d…](sessions/2026/06/19/rollout-2026-06-19T19-00-19-019ee21d-1e42-7ae0-9434-f8c02df69a20.jsonl) |
| 30 | 2026-06-21 07:36–22:02 EDT | 2026-06-21 11:36–2026-06-22 02:02 UTC | `<RESEARCHER_1>` | `linux-laptop` | Continued session on a new local day | 35 | [2026/06/19 / 019ee21d…](sessions/2026/06/19/rollout-2026-06-19T19-00-19-019ee21d-1e42-7ae0-9434-f8c02df69a20.jsonl) |
| 31 | 2026-06-22 10:10–17:27 EDT | 2026-06-22 14:10–21:27 UTC | `<RESEARCHER_1>` | `mac-local` | Machine handoff to a new session | 16 | [2026/06/22 / 019eefaa…](sessions/2026/06/22/rollout-2026-06-22T10-10-09-019eefaa-d066-73b3-a28b-9a01db6764ab.jsonl) |
| 32 | 2026-06-23 17:45–17:59 EDT | 2026-06-23 21:45–21:59 UTC | `<RESEARCHER_1>` | `mac-local` | Continued session on a new local day | 7 | [2026/06/22 / 019eefaa…](sessions/2026/06/22/rollout-2026-06-22T10-10-09-019eefaa-d066-73b3-a28b-9a01db6764ab.jsonl) |
| 33 | 2026-06-24 09:08–19:02 EDT | 2026-06-24 13:08–23:02 UTC | `<RESEARCHER_1>` | `mac-local` | Continued session on a new local day | 15 | [2026/06/22 / 019eefaa…](sessions/2026/06/22/rollout-2026-06-22T10-10-09-019eefaa-d066-73b3-a28b-9a01db6764ab.jsonl) |
| 34 | 2026-06-25 09:30–18:20 EDT | 2026-06-25 13:30–22:20 UTC | `<RESEARCHER_1>` | `mac-local` | Continued session on a new local day | 23 | [2026/06/22 / 019eefaa…](sessions/2026/06/22/rollout-2026-06-22T10-10-09-019eefaa-d066-73b3-a28b-9a01db6764ab.jsonl) |
| 35 | 2026-06-25 18:48–21:53 EDT | 2026-06-25 22:48–2026-06-26 01:53 UTC | `<RESEARCHER_1>` | `linux-laptop` | Machine handoff; resumed earlier session | 11 | [2026/06/19 / 019ee21d…](sessions/2026/06/19/rollout-2026-06-19T19-00-19-019ee21d-1e42-7ae0-9434-f8c02df69a20.jsonl) |
| 36 | 2026-06-26 09:58–17:42 EDT | 2026-06-26 13:58–21:42 UTC | `<RESEARCHER_1>` | `mac-local` | Machine handoff; resumed earlier session | 35 | [2026/06/22 / 019eefaa…](sessions/2026/06/22/rollout-2026-06-22T10-10-09-019eefaa-d066-73b3-a28b-9a01db6764ab.jsonl) |
| 37 | 2026-06-27 14:23–22:50 EDT | 2026-06-27 18:23–2026-06-28 02:50 UTC | `<RESEARCHER_1>` | `linux-laptop` | Machine handoff to a new session | 14 | [2026/06/27 / 019f0a51…](sessions/2026/06/27/rollout-2026-06-27T14-22-41-019f0a51-d0ad-76b3-9688-a1efa101a5f4.jsonl) |
