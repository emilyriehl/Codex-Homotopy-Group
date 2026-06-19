# Project Agent Instructions

These instructions apply to all AI coding agents working in this repository.

## Formalization Priorities

For Agda formalization work, prioritize elegant, reusable constructions and
proofs that could ultimately enter the upstream `agda-unimath` library. Do not
optimize only for closing a local hole if the result would leave behind a
noncanonical bridge that is hard to reuse or explain.

When a theorem can be proved either by a local transport trick or by exposing
the natural homotopy-theoretic structure, prefer the structural proof. Local
image/kernel transports are useful diagnostics and may be appropriate
intermediate lemmas, but the preferred final route should package the native
definitions, equivalences, fiber sequences, and exactness statements at the
mathematical abstraction level where they belong.

## Commit And Push Policy

At the end of every run that changes repository-tracked files, make a git
commit for the agent's intentional changes. Stage only files changed for the
current request; leave unrelated user or tool changes unstaged unless the user
explicitly asks to include them. If no tracked files changed, report that there
is nothing to commit.

Push after any commit that represents significant progress, including a checked
formalization result, a resolved blocker, an important status or instruction
update, or a user-requested handoff. If pushing fails, report the exact reason
and leave the commit in the local branch.

## Commit Messages

When making a commit, include the standard commit-message contents plus a short
description of the session. The session description should record the history
of the development in enough detail for later readers to understand the work:
who did the prompting, which agent did the implementation, and what the main
request/action sequence was.

## Agda MCP Server

At the start of Agda formalization work, check whether Agda MCP tools are
available to the agent. If they are not visible, alert the user that this
repository supports optional Agda MCP setup and point them to `MCP-SETUP.md`.
The MCP server is useful for interactive proof development, but final proof
acceptance still requires `./check.sh <file>`.
