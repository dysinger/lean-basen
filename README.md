# demo — minimal verified Lean 4 project template

Copyright 2026 Department of Code LLC.
SPDX-License-Identifier: AGPL-3.0-or-later

A minimal, self-contained [Lean 4](https://lean-lang.org/) library that
demonstrates the full verified-to-runnable pipeline: a proved byte-counting
library (one `lean_lib`) is checked with `lake build` (zero `sorry`) and run
through a packaged `cli` executable — all driven by
[Nix flakes](https://nixos.wiki/wiki/Flakes).

This is the Lean counterpart of the `fstar-nix-flake-template`: the same
`native` / `check` / `cli` target split and the same dependency-injection
convention (a package is a flake whose _consumers_ pull its source + pre-verified
artifacts as inputs), adapted to Lake. Start every `lean-*` package from this
skeleton.

## Getting started

```bash
# 1. Initialize a new Lean project (copies the template into the current dir).
nix flake init -t github:dysinger/lean-nix-flake-template

# 2. Rename it (see "Renaming" below): rename the module files, their
#    `module X` / `namespace X` headers, and the `pname` in default.nix.

# 3. Build everything.
nix build .#native .#cli

# 4. Run the CLI.
nix run .#cli    # prints `countAcc 0 [0, 1, 0, 2, 0, 1, 0] = 4`; exits 0

# 5. Drop into the dev loop (lean + lake + elan + clang on PATH).
nix develop
lake build
```

## The three build layers

| File            | Responsibility                          | Works without flakes?        |
| --------------- | --------------------------------------- | ---------------------------- |
| `flake.nix`     | inputs/outputs + `devShell` only        | no (needs flakes)            |
| `default.nix`   | builds every target                     | yes (`nix-build` / `import`) |
| `lakefile.lean` | the Lake build (module roots + targets) | yes (plain `lake` on PATH)   |

`flake.nix` pins nixpkgs and passes plain nixpkgs `lean4` to `default.nix` by
named argument. `default.nix` runs `lake build` for each target; `lakefile.lean`
owns the module roots and the `cli` executable. The editor LSP
(`lean --server`) is a dev-loop aid only — `nix build .#native` is the
verification gate (a build that encounters a `sorry` fails).

## What the template demonstrates

The example is a **byte-count** library — count the occurrences of a byte value
in a byte string — split into the same three layers as the F* template, minus
the Pulse leaf (Pulse is an F*-specific mutable-heap construct with no Lean
counterpart; in Lean the extractable leaf is the `cli` executable's
C-extraction seam):

| Module               | Layer          | Purpose                                             |
| -------------------- | -------------- | --------------------------------------------------- |
| `Example.Count.Types`| pure spec      | `count` over `UInt8` + `lemma_count_empty`          |
| `Example.Count`      | pure algorithm | tail-recursive `countAcc` + `countAcc_eq_count`     |
| `Example.Count.CLI`  | CLI entry      | `main` over a fixed byte string, returns exit status|

- `Example.Count.Types` defines `count b xs` (the number of `b` occurrences)
  over `UInt8` — the `codec` substrate's element type — and proves the empty
  base case.
- `Example.Count` implements a tail-recursive accumulator scan `countAcc` and
  **proves** `countAcc b xs 0 = count b xs` (the accumulator equals the spec),
  by induction.
- `Example.Count.CLI` runs the scan over a fixed
  `[0, 1, 0, 2, 0, 1, 0]` string (expecting `4` zeros) and exits `0` on a
  match, `1` otherwise. It is the `cli` executable's `main`.

The example is deliberately small so the *correctness theorem is actually
proved*, not stated as prose: unlike the F* template's Boyer–Moore example
(whose deep invariant is left unproved), `countAcc_eq_count` is a short
induction.

### The omitted Pulse layer

The F* template has a fourth module, `Example.Majority.Pulse`, that re-implements
the scan over a mutable `Pulse.Lib.Array` and extracts to C via Custard. Lean
has no Pulse/`#lang-pulse` construct, so this module is intentionally absent;
its role (the extractable, heap-level leaf) is played by the `cli` executable's
C-extraction seam. A real `lean-*` package that needs a mutable-array leaf adds
it back as an `@[extern]` C seam, not as a Pulse module.

- `Example.Count.Types` is the _thing you rename out_. It exists only so a
  fresh project starts with a compiling, proof-gated library rather than an empty
  shell.

## Renaming

The template ships with Lean package name `demo` (git repo
`lean-nix-flake-template`). The placeholder is `demo` rather than `example`
because `example` is a reserved word in Lean and cannot be a `package` /
`lean_lib` name. To start a real package, e.g. `vbin` (git repo
`lean-vbin`):

1. Rename `Example.lean` → `Vbin.lean` and `Example/Count/*.lean` →
   `Vbin/Count/*.lean` (or your real module names), updating each `module X`
   / `namespace X` header accordingly.
2. Edit `lakefile.lean`: `package demo` → `package vbin`, and the
   `lean_lib demo` `roots := #[`Example]`→`roots := #[`Vbin]`.
3. Edit `default.nix` and `flake.nix`: `pname = "demo"` → `pname = "vbin"`
   and the `description`/`name`/`echo` strings.
4. `git init` and push to the new repo.

## Depending on another `lean-*` package

The stack convention (see the sibling `lean-codec`, `fstar-codec`,
`fstar-basen`, …) is **dependency injection via flake inputs**: a package pulls
its dependencies' _source_ and _pre-built library_ as flake inputs, then hands
them to its own `default.nix`.

In `flake.nix`:

```nix
inputs = {
  # … nixpkgs / flake-utils / treefmt-nix …
  lean-codec.url = "github:dysinger/lean-codec";
};

# in outputs …:
codec-src = lean-codec;
codec-lib = lean-codec.packages.${system}.native;
```

For the dev loop (no flakes), Lake resolves deps via `require … from git`:

```lean
require codec from git "https://github.com/dysinger/lean-codec.git" @ "main"
```

## License

AGPL-3.0-or-later (or a commercial license from the author). See `LICENSE.md`.
