# AGENTS.md

Guidance for AI coding agents working in this repository.

## Project

`basen` — a verified base-`N` encoding/decoding library in Lean 4 (repo
`lean-basen`, package `basen`, module namespace `BaseN`). One package covering
base 2, 4, 8, 10, 16, 32, 64, each with a byte-list encoder + decoder and a
proved roundtrip law. Pure Lean (no C seam, no per-format C), stdlib-only (no
mathlib), `[propext, Quot.sound]`-only laws, zero `sorry`.

This is a downstream leaf of `codec` (sibling repo `../lean-codec`). It is
initialized from `lean-nix-flake-template` and depends on `codec` via
`require codec from git` (flake-input injection for Nix).

## Toolchain / environment

Same convention as `codec`: a Nix flake project. Enter the dev shell first:

```bash
nix develop   # pinned lean/lake/elan
lake build    # the proof gate: zero sorry, zero warnings
```

The `codec` dependency is fetched by `lake` from
`https://github.com/dysinger/lean-codec.git @ master` (see `lakefile.lean`) —
the floating dev-loop ref. A **Nix** build ignores that line entirely (see the
`codec` pin note under "Map of the repo"). `lake-manifest.json` is gitignored
and is not a pin; `flake.lock` is.

## Map of the repo

- `BaseN.lean` — the facade: module re-exports of the seven per-base modules
  only. There is **no** `Base` inductive, no `encode (b : Base)` dispatcher and
  no `BaseN.roundtrip` dispatch: each base is its own `Codec` value and the
  radix lives in the value the caller holds, never on a dispatch index.
- `BaseN/Common.lean` — the shared generic productivity/unambiguity lemmas
  (`Productive_iso`/`_seq_left`/`_count_succ`/`_satisfy`/
  `_count_satisfy_succ`, `Unambiguous_satisfy`/`_iso`, `Rel_count_satisfy_len`,
  `count_satisfy_unambiguous`). Each new base `open BaseN.Common` and reuses
  these instead of re-deriving them.
- `BaseN/Base2.lean`, `Base4.lean`, `Base8.lean`, `Base10.lean`, `Base16.lean`,
  `Base32.lean`, `Base64.lean` — **all seven bases are landed**, each a `Codec`
  value: the fixed-width five (`2/4/8/10/16`) have element `Codec UInt8` and the
  padded two (`32/64`) are a full-block `Run` (the derived `many`) followed by
  an at-most-one-block terminal-tail element `iso`-ed to `B32`/`B64`. Every base
  has the productive repetition triple `decode* = decodeRepeat elem …` /
  `encode* = encodeRepeat elem` / `rel* = relRepeat (Rel elem)` and an inherited
  `roundtrip`. **No bespoke `encode`/`decode`** — that surface was deleted by
  `basen-uniform-leaf-api` (archived).

  **`Base16.lean` additionally carries RFC 4648 §8 case-insensitive decoding**
  (it does **not** weaken `Iso.law`). The variation is a length-preserving ASCII
  case fold (`foldByte`/`foldList`/`foldByteBytes`) folded **up** so the canonical
  uppercase encoding is a fixed point, with the quotient in the _object_ via
  `codec`'s `Codec.Normal`: `hexBlockIsoF : Iso UInt8 (Normal (List UInt8)
foldList)` is an **ordinary** `Iso`. The case-insensitive surface is decode-only
  (`decodeHexBlockFold`, `decodeHexFold`); the strict `hexElem`/`hexRun`/
  `encodeHex` are untouched and `encodeHex` still emits uppercase only. Do not
  restate the §8 widening as an identity — `hexBlockApply (foldList cs) =
hexBlockApply cs` is **false** (`['6','f']` is rejected, folds to the accepted
  `['6','F']`); the law is the one-directional `hexBlockApply_foldList`, and the
  refutation is `hexBlockApply_foldList_ne`.

  **Do not reintroduce the `Classical.choice` leak.** `decide_eq_true (by
omega)` on a **disjunction** goal drags in classical logic (omega case-splits);
  build the disjunct explicitly. A `match` on a `Bool` **in the goal** leaks too;
  split the lemma into `_true`/`_false`.

- `lakefile.lean` / `flake.nix` / `default.nix` / `treefmt.nix` — build shape
  from the template (renamed to `basen`), with `native`/`check`/`bench` Nix
  targets. **The vector lane's checks fire at BUILD time, not run time**: every
  check in `Bench.lean` is an `example` closed by `rfl` or `by native_decide`, and
  Lake elaborates both while compiling the module. `Bench.lean`'s `main` is
  `pure ()` — there is no runtime lane — so `nix build .#bench` proves that the lane
  **builds in the sandbox** (dependency injection resolves, every vector is checked
  by elaboration, the executable links), and its `installPhase` runs the binary only
  as a smoke test that it starts and exits 0. An earlier version of this bullet said
  the lane had to be _run_ for its checks to happen and that "a build that is not run
  has verified nothing"; both were false of the code (`codec-audit-round-six` R7-16,
  design §D4) and misled three documents. `bench` is a **package, not a `checks`
  entry**, on purpose: known vectors are evidence, not a proof, so they must not be
  able to fail the proof gate. For a fast loop use the dev-shell form —
  `lake build bench` — which does not go through Nix at all. Running the binary adds
  nothing to the verification — `main` is `pure ()`, so the binary's only observable
  behaviour is exiting 0.
- `openspec/` lives in the **`lean-codec`** repo (`openspec/changes/lean-basen/`),
  not here — the planning ledger is cross-referenced from the codec repo.

### Two files that look like they pin `codec` but do not

- **`lakefile.lean`'s `require codec from git … @ "master"`** is the _floating_
  dev-loop ref (`master`, not the template's `main`, is genuinely this ecosystem's
  default branch). It is never read by a Nix build: `default.nix` rewrites the
  `require` to `require codec from "./codec-src"`. Do not pin it to a SHA.
- **`lake-manifest.json` is gitignored and is NOT a pin.** It is whatever the
  last local `lake update` wrote, so it drifts silently between checkouts. The
  only reproducibility anchor is **`flake.lock`'s `nodes.codec.locked.rev`** —
  that is the revision to quote, compare, or bump, and the one to check when a
  sandboxed build reports a `bad import` for an import that plainly exists here.

### The validated `codec` revision — read `flake.lock`, never a number here

The revision this package's gate was last known green against is
`flake.lock` → `nodes.codec.locked.rev`. **Do not trust a SHA written in prose,
including this line** — that is exactly the class of defect
`codec-audit-round-five` R6-09/R6-34 found: three prose sites quoted the pin from
memory and all three were stale while the lock had moved. To read it:

```bash
python3 -c "import json;print(json.load(open('flake.lock'))['nodes']['codec']['locked']['rev'])"
```

The `basen` spec delta also requires that this revision be either the sibling
tree's current default-branch commit or a recorded lag with its reason. Bumping is
targeted — `nix flake update codec` then `lake update codec`, never all inputs —
and must be followed by `lake build`, `lake build bench` and `nix build '.#bench'`
before the new revision is called validated. `CHANGELOG.md` names the rev that a _historical_ entry landed with; those entries
are history, not the current pin.

## Active work: none in this repo — the ledger is in `lean-codec`

The `Codec`-value rewrite (`basen-uniform-leaf-api`) and the RFC-conformance work
(`basen-rfc-conformance-theorems`) are both **archived**. All seven bases are
landed, the facade is re-exports only, the bench lane value-checks every base,
and the gate is green.

**What remains is mechanical polish**, tracked as tasks 5.2/5.3/5.4/5.8/5.9/5.12/
5.13 of `lean-basen` in `../lean-codec/openspec/changes/lean-basen/tasks.md`. Do
not open a new change here for it, and do not re-litigate the base32/64 shape —
that is settled and proved (see the note below, kept because the reasoning is
still what a future edit to `Base32.lean`/`Base64.lean` needs).

## Why base32/64 are shaped differently (settled, do not re-litigate)

base2/4/8/10/16 have element `Codec UInt8` (one byte per element), so their block
`Iso` (`k` digits ↔ one byte) is a clean bijection — both `law` directions close
with `omega`. Base32/64 are **cross-byte bit-packing** (5 bytes = 40 bits = 8
five-bit chars; 3 bytes = 24 bits = 4 six-bit chars), so the element is
`Codec (List UInt8)` (5/3 bytes) via `iso blockIso (count 8 (satisfy b32OrPad))`,
and its block `Iso.law` needs a **backward** direction (`apply cs = bs →
unapply bs = cs`) that is **encode-injectivity / char reconstruction**.

The byte-reconstruction identities that direction rests on are named
`byte0Of`…`byte4Of` in `Base32.lean` and `byte0Of`…`byte2Of` in `Base64.lean`
(renamed from the bare `byte0`…`byte4`; they are exported, so use the `Of`
names). They are proved per-shape by `by_cases` on each `cᵢ = 61`/
`b32Valid cᵢ` condition (close impossible branches with `simp at h` + `omega`),
recover `b32ToVal cᵢ` from the `byte*Of` identities read in reverse, then a
`char_eq_valToB32_of_valid` lemma (`c.toNat = valToB32 i` when `b32Valid c =
true ∧ b32ToVal c.toNat = i`). base32 = 5 shapes (1/2/3/4/5-byte tails),
base64 = 3 shapes (1/2/3-byte tails).

**Do NOT use `by_contra`** (needs `Classical.choice`, breaks the
`[propext, Quot.sound]` gate).

## Proof pattern (established this session — follow it, do not re-derive)

Each base follows the same shape, proven `[propext, Quot.sound]`-only:

1. **`Nat`-level core + a thin `UInt8` surface.** `encodeN : List Nat → List Nat`
   and `decodeN : List Nat → Option (List Nat)` carry the proofs; `encode : List
UInt8 → List UInt8` / `decode : List UInt8 → Option (List UInt8)` are the spec
   surface, and `roundtrip : decode (encode bs) = some bs` is proved by induction
   over the `Nat` core with the `UInt8 ↔ Nat(<256)` correspondence made
   transparent. Every alphabet byte is ASCII `< 256`, so `UInt8.ofNat`/`.toNat`
   truncation vanishes via `UInt8.toNat_ofNat'` + `Nat.mod_eq_of_lt`. `UInt8`
   bounds come from `UInt8.toNat_lt` (→ `b.toNat < 256`), and reconstruction from
   `UInt8.ofNat_toNat`.

2. **Character bijection lemmas.** For each base, prove
   `*ToVal_valTo* : *ToVal (valToX d) = d` (the nibble/digit ↔ char bijection),
   `valToX_valid : isValid (valToX d) = true`, and `valToX_lt_256`. For
   single-contiguous alphabets use `by_cases` on the range + `simp only […,
ite_true, ite_false]` + `omega`. For multi-range alphabets (base32/64), use
   `exact decide_eq_false_iff_not.mpr (by omega)` for the "never the pad byte"
   fact and `rcases (show d = k ∨ d = k+1 by omega) with rfl | rfl <;> decide`
   for the final finite tail.

3. **`roundtripN (bs) : (∀ b ∈ bs, b < 256) → decodeN (encodeN bs) = some bs`**
   via a `decodeN_block`/`decodeN_*_single` helper and structural induction;
   `encodeN` distributes over cons/append (`simp [encodeN]`), and `decodeN` of
   a concatenation recurses on the tail.

4. **`roundtrip` (UInt8)** by induction + `change decode (encode [b] ++ encode
bs) = some (b :: bs)` + the `toByte_valTo*`/`valTo*_valid`/`*ToVal_valTo*`
   rewrites + a final `omega`/`simp` on the digit-sum identity.

### Digits over powers of two (Base2/Base4)

The bit/quartet sum identity (`Σ (v/2^k % 2) * 2^k = v`) needs
`bitAt v i = (v / 2^(7-i)) % 2`, then **`simp only [Nat.reducePow,
Nat.reduceSub]`** to turn `2^(7-i)` into a concrete power before `omega` —
`omega` handles the concrete `v/128%2*128 + … + v%2 = v` for `v < 256`, but does
NOT unfold `2^(7-i)` on its own.

### Stdlib-only proof fact (no mathlib)

This repo (like `codec`) has **no `norm_num`, `nlinarith`, `ring`, `fin_cases`,
`interval_cases`** — only `omega`/`simp`/`rw`/`rcases`/`by_cases`/`decide`.
`omega` does **not** expand `if`/`ite` branches; always `by_cases`/`simp only`
each condition to a concrete branch first. `decide` closes closed `Bool`/
`Decidable` propositions and is `[propext, Quot.sound]`-safe (unlike
`native_decide`).

## Git conventions

- Commit individual files; print the exact staged set before committing.
- `flake.lock` (Nix) is tracked; `lake-manifest.json` is gitignored.
- The `prepare-commit-msg`/`nix fmt` pre-commit hook (in `.githooks/`) runs
  `nix fmt` and refuses a commit that leaves a staged file unformatted — `git
add` the reformatted file and re-commit.
