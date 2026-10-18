# Changelog

All notable changes to this project are documented in this file.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- Initial template: a minimal verified Lean 4 library skeleton (one
  `lean_lib` + a `cli` executable), Nix flake with the `native`/`check`/`cli`
  target split and a `lean4`-scoped dev shell.
- The byte-count example, mirroring the F* template's three-layer module shape:
  `Example.Count.Types` (pure spec), `Example.Count` (pure algorithm with a
  proved `countAcc_eq_count`), and `Example.Count.CLI` (the `cli` entry point).
  The F* `Example.Majority.Pulse` leaf is omitted (Pulse has no Lean
  counterpart). The example domain is small enough that its correctness theorem
  is actually *proved* (a one-line induction), unlike the F* Boyer–Moore
  example whose deep invariant is left as prose.

### Notes

- Every project built from this template should set its own
  `## [0.1.0] — initial release` section with package-accurate module and
  target names, and keep this Keep-a-Changelog format.
