# basen — verified base-N encodings

Copyright 2026 Department of Code LLC.
SPDX-License-Identifier: AGPL-3.0-or-later

A verified [Lean 4](https://lean-lang.org/) library of base-`N` byte encodings:
base **2, 4, 8, 10, 16, 32, 64**, each with a `List UInt8 → List UInt8` encoder,
a `List UInt8 → Option (List UInt8)` decoder, and a proved roundtrip law
`decode (encode bs) = some bs` — every law `[propext, Quot.sound]`-only, zero
`sorry`.

This is the second leaf off the `codec` core in the Lean ecosystem ordering
(`codec` → `basen`), porting the four RFC 4648 encodings from `fstar-basen`
and adding Base2/4/10.

## Status

| Base   | RFC     | Alph. / padding                    | Status         |
| ------ | ------- | ---------------------------------- | -------------- |
| Base2  | —       | `0`/`1`, 8 chars/byte, MSB-first   | ✅ proven      |
| Base4  | —       | `0-3`, 4 chars/byte                | ✅ proven      |
| Base8  | —       | `0-7`, 3 digits/byte               | ✅ proven      |
| Base10 | —       | `0-9`, 3 digits/byte, no sign      | ✅ proven      |
| Base16 | 4648 §8 | `0-9A-F` (case-insensitive decode) | ✅ proven      |
| Base32 | 4648 §6 | `A-Z2-7`, `=` padding              | ⏳ in progress |
| Base64 | 4648 §4 | `A-Za-z0-9+/`, `=` padding         | ⏳ in progress |

The `BaseN` facade re-exports the per-base modules and dispatches a single
`BaseN.roundtrip` over an inductive `Base`. Base32/Base64 are in progress;
see `openspec/changes/lean-basen/tasks.md` (tasks 2.3/2.4).

## Usage

```lean
import BaseN

#eval BaseN.Base16.encode [0x66, 0x6f, 0x6f]  -- [54,54,54,70,54,70] = "666F6F"
#eval BaseN.Base16.decode [54,54,54,70,54,70]  -- some [0x66, 0x6f, 0x6f]
```

## The substrate and proof discipline

Every codec is a pure function over `List UInt8` (the `codec` `Bytes n` element
type) — no `String`, no opaque buffer, no `@[extern]` C seam. Each `BaseN.BaseX`
proves `roundtrip : decode (encode bs) = some bs` (the `Option` is the only
partiality — malformed input returns `none`), and `#print axioms` reports only
`[propext, Quot.sound]`.

The digit math is done in `Nat` (`UInt8.toNat`) with a thin `UInt8` surface; the
alphabet is ASCII (48-122, all `< 256`), so `UInt8.ofNat`/`.toNat` are
transparent. See `AGENTS.md`/`PAPER.md` in the sibling `lean-codec` for the
two-layer trust-seam posture this package inherits (pure-Lean spec, no Layer-2 C
here).

## Build

```bash
nix develop            # lean + lake + elan + clang on PATH
lake build             # the proof gate: zero `sorry`, zero warnings
nix build .#native     # the Nix verification gate
```

## License

AGPL-3.0-or-later (or a commercial license from the author). See `LICENSE.md`.
