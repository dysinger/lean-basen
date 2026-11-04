import Lake
open Lake DSL
open System

/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

package basen

/- `@ "master"` is the *floating* dev-loop ref, deliberately: `lake build` from
this checkout tracks the tip of `lean-codec`'s default branch (which really is
`master`, not the template's `main` — the template predates this repo and the
branch was never renamed). This ref is **not** the reproducibility anchor for a
Nix build: `flake.nix` pins `codec` as a flake input and `default.nix` rewrites
this `require` into `require codec from "./codec-src"`, so a Nix build uses the
locked revision in `flake.lock` and this line is never even read.

The two therefore disagree only outside Nix, which is exactly what is wanted: a
fast-moving dev loop here, a pinned revision there. Do not "pin" this line to a
commit SHA — that only makes `lake build` fail after a `flake.lock` bump (the
`bad import` symptom described in the sibling `lean-codec` AGENTS.md), without
adding reproducibility that `flake.lock` does not already provide. -/
require codec from git "https://github.com/dysinger/lean-codec.git" @ "master"

@[default_target]
lean_lib basen where
  roots := #[`BaseN]
  /- The proof gate, made real. `lake build` only *warns* on `sorry`
  (`declaration uses 'sorry'`), so a plain build goes green with an incomplete
  proof — verified in this repo by stubbing a theorem: exit 0 with a warning.
  `-DwarningAsError=true` promotes that warning to an error, making the
  **compiler** the authority instead of a parallel `sorry` lint that could drift
  (`admit`, a tactic-generated `sorryAx`, ...). This mirrors
  `lean-codec/lakefile.lean`, which does the same for `lean_lib codec`; the flag
  belongs on the *library* rather than on one consumer so every path that
  compiles `BaseN` inherits it (including `bench` and the sandboxed
  `nix build .#checks.lean`). This is what lets `AGENTS.md` and `README.md` call
  zero-`sorry` *enforced* rather than merely *observed*. -/
  moreLeanArgs := #["-DwarningAsError=true"]

@[default_target]
lean_lib Axioms where
  roots := #[`Axioms]
  /- The same flag, for the same reason. `Axioms` is the `#guard_msgs` gate
  library, so a `sorry` reaching it must fail too — otherwise the gate could be
  satisfied by an unproven law. -/
  moreLeanArgs := #["-DwarningAsError=true"]

lean_exe bench where
  root := `Bench
