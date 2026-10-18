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
`https://github.com/dysinger/lean-codec.git @ master` (see `lakefile.lean`).
`lake-manifest.json` is gitignored.

## Map of the repo

- `BaseN.lean` — the facade: re-exports the per-base modules + an inductive
  `Base` (currently scoped to B2/B4/B8/B10/B16; B32/B64 are in progress) and a
  single `BaseN.roundtrip` dispatching per-base by `cases`.
- `BaseN/Base2.lean`, `Base4.lean`, `Base8.lean`, `Base10.lean`, `Base16.lean` —
  the five landed bases, each with `encode`/`decode` + `roundtrip`.
  (`Base32.lean`/`Base64.lean` are the remaining work — tasks 2.3/2.4.)
- `lakefile.lean` / `flake.nix` / `default.nix` / `treefmt.nix` — build shape
  from the template (renamed to `basen`), with `native`/`check` Nix targets.
- `openspec/` lives in the **`lean-codec`** repo (`openspec/changes/lean-basen/`),
  not here — the planning ledger is cross-referenced from the codec repo.

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
