# Project Agent Instructions

These instructions apply to all AI coding agents working in this repository.

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
