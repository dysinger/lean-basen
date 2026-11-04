# Changelog

All notable changes to `basen` (Lean package `basen`, module namespace `BaseN`).

Format: dated sections, newest first. This file records _what landed and why_;
the OpenSpec ledger in the sibling `lean-codec` repo
(`openspec/changes/lean-basen/`) records the task-level detail, and `AGENTS.md`
records the conventions.

## 2026-11-04 — Pre-archive audit: the proof gate made real

A hypercritical pre-archive audit compared this repo against `lean-codec` on
four axes (project uniformity, theorem coverage, code quality, archive
readiness). It found three release blockers plus a set of smaller defects.
Findings are recorded as `§6.1`–`§6.10` in the ledger's `tasks.md`.

### The proof gate was not enforced (blocker)

`lakefile.lean`'s `lean_lib basen` had no
`moreLeanArgs := #["-DwarningAsError=true"]`, while `lean-codec`'s
`lean_lib codec` does. A `sorry` therefore produced only
`warning: declaration uses 'sorry'` and the build exited **0** — verified by
stubbing a theorem. That made three files' claims false (`AGENTS.md`,
`README.md`, `default.nix` all called zero-`sorry` "the gate").

The flag is now set on **both** target libraries — `basen` (so every consumer
path, including `bench` and the sandboxed `nix build .#checks.lean`, inherits it)
and `Axioms` (so a `sorry` reaching the `#guard_msgs` gate also fails). Verified
load-bearing: the stubbed theorem now yields
`error: declaration uses 'sorry'` / `error: build failed`, and reverting the stub
leaves `lake build` green.

### Smaller fixes

- `Axioms.lean` now gates four more laws that an audit found referenced only by
  their own declarations: `b64Split_shape`, `b32Split_shape`,
  `b64BlockUnapply_one`, `b64BlockUnapply_two`. They are true and
  the natural load-bearing facts for any future split-level argument, so they
  were gated rather than deleted. Gating them exposed that all four are
  `[propext]`-only, not `[propext, Quot.sound]` — the gate caught it.
- Renamed six snake_case declarations to camelCase, matching the rest of the
  codebase: `decodeFull_b64Tail_of_encode` → `decodeFullB64TailOfEncode`,
  `b64_boundary_pin` → `b64BoundaryPin`,
  `b64_block_run_of_boundary` → `b64BlockRunOfBoundary`, and the same three for
  base32.
- Removed a stray empty `openspec/` directory: git cannot track empty
  directories, so it was local debris, and it was misleading because the ledger
  lives in `lean-codec`.
- Added this `CHANGELOG.md` (companion to `lean-codec`'s).

## 2026-11-02 — Documentation and polish

- `README.md`: replaced three false claims an earlier review followed into the
  source. It documented a `BaseN.roundtrip` dispatcher over an `inductive Base`
  (neither exists — `BaseN.lean` is re-exports only, by design), claimed every
  base proves `roundtrip : decode (encode bs) = some bs` (the real shape is
  `encode bs = some ⟨n, s⟩ → decodeFull … n s = some bs`, and base32/64 name
  theirs `decodeFullB{32,64}_roundtrip`), and its Usage block called
  `Base16.encode`/`Base16.decode`, which do not exist. Every `#eval` output in
  the new text was pasted from a real run.
- `Base8.lean`: deleted nine lemmas that `BaseN/Common.lean` already provides
  (`Productive_*`, `Unambiguous_*`, `Rel_count_satisfy_len`,
  `count_satisfy_unambiguous`). Because a local declaration **shadows** an
  opened one, Base8 had been using its own copies while the other five
  fixed-width bases used `Common`'s — two proofs of the same lemma, free to
  drift apart with no build signal. 731 → 591 lines.
- `Base16.lean`: replaced 30 deprecated tactic uses (`if_neg` → `ite_eq_right`
  ×17, `if_pos` → `ite_eq_left` ×12, `if_true` → `ite_true` ×1). Purely
  mechanical; no statement or proof structure changed. `lake build` is now
  warning-free.

## 2026-11-01 — `bench` wired as a Nix package

`default.nix` gained a `bench` derivation and `flake.nix` exposes
`packages.bench`. Two deliberate choices, both recorded in the file headers:

- it is a **package, not a `checks` entry** — the lane value-checks known
  vectors, which is evidence, not proof, so it must not be able to fail the
  proof gate;
- its `installPhase` **runs** the executable. The vectors are
  `example … := rfl`, which Lake only elaborates while compiling, so a build
  that is not run has verified nothing.

## 2026-10-27 — RFC 4648 conformance theorems

Landed the rejection/canonicality layer (change
`basen-rfc-conformance-theorems`, archived): `decodeFullB{32,64}_conv`,
`_char`, `_char_via_type`, the canonical `B32`/`B64` spine bijection, and the
rejection laws (trailing data after `=`, bad arity, pad at a low slot, invalid
character at any index, overflow for base8/base10).

## 2026-10-20 — Uniform `Codec`-value surface

Landed `basen-uniform-leaf-api` (archived): all seven bases re-expressed as
`codec` `Codec` values over `satisfy`/`count`/`iso` plus the repetition layer,
deleting the bespoke `encode`/`decode` surface. Each base now proves the
inherited roundtrip law, `[propext, Quot.sound]`-only.

## 2026-10-18 — Initial port

Ported `fstar-basen`'s four RFC 4648 bases (Base08/16/32/64) to
`BaseN.Base8/16/32/64` and added Base2/Base4/Base10, which the F* reference
does not have. Repo initialised from `lean-nix-flake-template`, with `codec`
as a flake input injected via `default.nix` so the sandboxed build needs no
network.

## Conventions worth knowing when reading this file

- **`lake build` fails on `sorry`.** The flag is on the library, not on one
  consumer, so every path that compiles `BaseN` inherits it.
- **`lake build Axioms` is the axiom gate.** `Axioms.lean` is a
  `@[default_target]` library of `#guard_msgs` checks, so a
  `Classical.choice` regression fails the build. It is a _sample_ of the laws,
  not full coverage — see `tasks.md` §6.4.
- **`flake.lock` is the only pin.** `lakefile.lean`'s `@ "master"` is a floating
  dev-loop ref that `default.nix` rewrites away; `lake-manifest.json` is
  gitignored and is not a pin.
