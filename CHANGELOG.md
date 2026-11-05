# Changelog

All notable changes to `basen` (Lean package `basen`, module namespace `BaseN`).

Format: dated sections, newest first. This file records _what landed and why_;
the OpenSpec ledger in the sibling `lean-codec` repo
(`openspec/changes/lean-basen/`) records the task-level detail, and `AGENTS.md`
records the conventions.

## 2026-11-05 — full axiom-gate coverage, and every lint suppression removed

Two pre-archive audit findings (ledger §6.4 / §6.5), plus the toolchain question
(§6.10) answered.

### Coverage: 418/418 public theorems gated (was 91/404)

`Axioms.lean`'s own docstring says "an un-gated law is not protected", and by
its own standard roughly three quarters of the library was unprotected. Every
remaining public `theorem` is now pinned by a `#guard_msgs` block.

**Measured before writing anything, and the answer was the reassuring one:** all
315 then-ungated theorems were `#print axioms`'d in a single probe, and every one
was already clean — 272 `[propext, Quot.sound]`, 32 `[propext]`, 11 axiom-free,
**zero** `Classical.choice`. So the gap was coverage debt, not a discipline
failure; no proof needed repair. Final distribution across all 418: 367 / 42 / 12.

The new gates were verified **load-bearing by a real leak**, not a `sorry` stub:
injecting `Classical.choice` into `Common.Productive_iso` trips three separate
guards (that law plus two downstream consumers), so a leak fails transitively.
That is the stronger check — it exercises the axiom half rather than the
completeness half.

### Lint: every `set_option linter.… false` is gone

Three file-wide switches (`Common.lean`, `Base64.lean`, `Bench.lean`) hid 24
genuine redundancies — 1 + 2 `unnecessarySimpa` hits and 21 unused `simp only`
arguments — all now **fixed rather than suppressed**. The bench lane was re-verified after
minimising its `simp only` sets — corrupting one expected byte (`0x76` → `0x77`
in the `Zm9v` vector) still fails the build, so tightening the simp sets did not
turn the value check into a tautology.

### Toolchain: upgraded to Lean 4.35.0

`lean4` 4.34.1 → **4.35.0** (nixpkgs `1d06008`, 2026-11-03), and `codec` →
`3277d48`. This was taken because the cost turned out to be **one line**, not a
rebuild: the 4.35.0 toolchain is a cache substitution (`cache.nixos.org` serves
it, HTTP 200), and compiling both libraries against it first showed `basen`
needed **no** source changes at all — `lake build` 25, `bench` 45, `Axioms` 24,
all green as-is. The single break was in `codec`, `Codec/Packed.lean`'s
`decodeFullArraySearch_cons`, where 4.35.0 closes the goal at the `conv`+`rw`
that 4.34.1 left open; the fix is a `first | (tail) | skip` wrapper chosen so
the law stays green on _both_ toolchains.

**A segfault worth knowing about:** immediately after the bump,
`lake build bench` aborted with `lean::exception: unsupported IRType` (exit
139). That was **not** the upgrade — it was stale `.lake` artifacts from the
4.34 build. `rm -rf .lake` and the same command is green (28 jobs). After a
toolchain bump, clean the build directory before believing a crash.

### Toolchain pin (§6.10): corrected to match what builds

Before the upgrade, `lean-toolchain` said `v4.30.0` while **nothing honoured it**: `lake build -v`
showed `…-lean4-4.34.1/bin/lean`, and `default.nix` takes nixpkgs `lean4` with no
reference to the file (elan has 4.30.0 installed, but the dev shell's lean
shadows it on PATH). It was corrected to `v4.34.1`, and now to `v4.35.0` to match the bump.

**This is not a `flake.lock` fix and not an upgrade.** The lock pins a nixpkgs
that legitimately provides 4.34.1, so the lock was always right — only the
`lean-toolchain` text was wrong. The edit is one line, with **no** `flake.lock`
change, no `nix flake update`, and no toolchain rebuild; the gates were re-run to
confirm nothing moved (13 / 25 / 45 / 24 jobs).

For context, since "is 4.34.1 current?" came up: upstream's stable is 4.35.0
(2026-10-12) and nixpkgs master now carries it, so 4.34.1 is **one release (18
days) behind** — current, not stale. Moving to 4.35.0 was declined as an
unnecessary rebuild, which is a separate decision from this fix. The remaining
honest option, if ever wanted, is to _delete_ the file rather than maintain a pin
nothing reads; that is an owner call, but it is no longer an inconsistency.

## 2026-11-05 — `Zh==` and `Zm9=` are rejected, whole-input

The base64 half of the same story as the entry below. Commit `9d5074e` implied
that the non-canonical pad-bit vectors `Zh==` / `Zm9=` were rejected, but
`b64Zh` and `b64Zm9` were **orphaned definitions**: `grep -rn '\bb64Zh\b'`
returned one hit, the definition itself. The rejection was true (`#eval` said
`none`) and unstated. This release adds the whole-input theorem
(ledger §6.2 / §6.3a).

### Added

- `b64Zm9_chars`, `b64BlockApply_b64Zm9_chars`, `b64TailApply_b64Zm9_chars` —
  the `Zm9=` block-level triple, twin of the `Zh==` one that already existed.
  The first is axiom-free, the other two `[propext]`-only.
- `decodeFullB64_reject_b64Zh : decodeFullB64 b64Zh = none` — the whole-input
  rejection of the non-canonical **1-byte** tail. `[propext, Quot.sound]`-only.
- `decodeFullB64_reject_b64Zm9 : decodeFullB64 b64Zm9 = none` — the whole-input
  rejection of the non-canonical **2-byte** tail. `[propext, Quot.sound]`-only.

All five are gated in `Axioms.lean` under a §6.2 block, verified
**load-bearing** by mutation (stubbing `decodeFullB64_reject_b64Zh` to `sorry`
fails `lake build` with `error: BaseN/Base64.lean:3480:8: declaration uses
'sorry'`; restoring it is green, 25 jobs). Both vectors are also
`example`-checked in `Bench.lean` (`lake build bench`, 45 jobs).

### Notes on the proof

The lift is factored as **one** private theorem,
`decodeFullB64_none_of_rejected_tail`, plus two thin instances — not duplicated
per vector. It is parameterised by the pad **position** `kp : Fin 4`, which is
not an accident: the two tails pad at different widths (`Zh==` at index 2,
`Zm9=` at index 3), so the "a twin transfers the proof shape, never the
constants" rule bites _inside_ base64, not only across bases.

The recorded history of this item said it was "blocked on `Suffix`/`splice`
index bookkeeping in the `blocks = []` branch". That was **wrong**, and the
`#eval` check that refuted it was re-run first this time:
`decodeRepeat b64BlockElem b64BlockConsumesByte 4 b64Zh` yields exactly one
decomposition, `(blocks.length, t.remaining) = (0, 4)` — a base64 full block is
4 bytes, so a 4-byte input cannot populate the block run at all. The proof kills
the `cons` branch anyway (a two-line `omega`: `4 ≤ 4 - t.remaining` against
`¬ (kp.val < 4 - t.remaining)`), because a theorem must not rest on a `#eval`
about one literal. No `splice` reasoning and no index transport were needed.

The cost that did appear was in the plumbing: `splice_prefix_read` needs its
`hm : m ≤ n` argument supplied explicitly, and the pad fact must be stated at
`Fin 4` on the _input_ type — `Bytes n` is a function, so `Fin s.length` is not
even well typed, and an `omega` inside a statement's index annotation is
elaborated without the `have`s that make it true.

## 2026-11-05 — `MZ======` is rejected, for real this time

Commit `3dfc249` said in its message that `MZ======` "is not an encoding of
anything". No theorem, definition or vector named `MZ` existed in the file —
`grep -rn 'MZ' BaseN/Base32.lean` returned zero hits. This release adds the
theorem that claim was missing (ledger §6.3b).

### Added

- `MZ : Bytes 8` — the `MZ======` character block itself.
- `b32BlockApply_b32Mz_chars : b32BlockApply MZ-charblock = none` — the §3.5
  rejection at the block decoder, which is where the RFC puts the constraint.
  `[propext]`-only.
- `b32TailApply_b32Mz_chars` — the same, lifted to the tail element.
  `[propext]`-only.
- `not_rel_b32TailElem_of_apply_none` — the bridge from a block-level `none` to
  the tail element's relation; the base32 twin of the base64 one.
  `[propext, Quot.sound]`-only.
- `decodeFullB32_reject_MZ : decodeFullB32 MZ = none` — the whole-input
  theorem. `[propext, Quot.sound]`-only, zero `Classical.choice`.

All four laws are gated in `Axioms.lean`, and the gate was verified
**load-bearing** by mutation: stubbing `decodeFullB32_reject_MZ` to `sorry`
fails `lake build` with `error: declaration uses 'sorry'` naming the
declaration; restoring it is green (25 jobs).

### Notes on the proof

The block-level law needed `b32BlockUnapply [0x66] = some [0x4D, 0x59, …]`
(`MY======`), **not** the `Zg`-analogue one would guess from the base64 twin:
`102 / 8 = 12` → `M` and `(102 % 8) * 4 = 24` → `Y`. The re-encoded literal is
a value in each base's own alphabet, so a ported rejection lemma transfers its
_shape_ but not its constants — `decide` caught the guess.

The whole-input lift mirrors `decodeFullB64_reject_ZgAAAA`: an 8-char input
admits no full block containing `=` (a full-block element is alphabet-only), so
the block run is empty and the single tail element consumes all 8 bytes, at
which point the bridge applies. This is why §6.3b was simpler than §6.2 and not
entangled with its `Suffix`/`splice` bookkeeping — **§6.2's base64 whole-input
lift remains open**; this does not close it.

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
