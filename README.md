# basen — verified base-N encodings

Copyright 2026 Department of Code LLC.
SPDX-License-Identifier: AGPL-3.0-or-later

A verified [Lean 4](https://lean-lang.org/) library of base-`N` byte encodings:
base **2, 4, 8, 10, 16, 32, 64**, each expressed as a
[`codec`](https://github.com/dysinger/lean-codec) `Codec` value over the
`Bytes n := Fin n → UInt8` substrate, and decoded/encoded by the **single
uniform** `Codec` operations — the radix lives in the value the caller holds,
never on a dispatch index. Every law is `[propext, Quot.sound]`-only, with zero
`sorry`.

This is the second leaf off the `codec` core in the Lean ecosystem ordering
(`codec` → `basen`), porting the four RFC 4648 encodings from `fstar-basen`
and adding Base2/4/10.

## Status

| Base   | RFC     | Alph. / padding                    | Status    |
| ------ | ------- | ---------------------------------- | --------- |
| Base2  | —       | `0`/`1`, 8 chars/byte, MSB-first   | ✅ proven |
| Base4  | —       | `0-3`, 4 chars/byte                | ✅ proven |
| Base8  | —       | `0-7`, 3 digits/byte               | ✅ proven |
| Base10 | —       | `0-9`, 3 digits/byte, no sign      | ✅ proven |
| Base16 | 4648 §8 | `0-9A-F` (case-insensitive decode) | ✅ proven |
| Base32 | 4648 §6 | `A-Z2-7`, `=` padding              | ✅ proven |
| Base64 | 4648 §4 | `A-Za-z0-9+/`, `=` padding         | ✅ proven |

The `BaseN` module **re-exports the seven per-base modules and nothing else**.
There is deliberately **no** `Base` inductive and **no** `BaseN.roundtrip`
dispatcher: each base is its own value, and a dispatcher over a radix enum would
re-introduce exactly the dispatch index this design removes.

**The law is per base, and its shape is worth stating exactly**, because the
obvious paraphrase is wrong. For the five fixed-width bases it is

```lean
theorem roundtrip (bs : List UInt8) {n : Nat} {s : Bytes n} :
    encode{X} bs = some ⟨n, s⟩ → decodeFull {x}Elem {x}ConsumesByte n s = some bs
```

i.e. _given_ the encoder's output `⟨n, s⟩`, the whole-input decoder returns the
original bytes. It is not `decode (encode bs) = some bs` — there is no total
`decode : List UInt8 → Option (List UInt8)` in this surface. The two padded
bases prove the same fact under the names
`decodeFullB32_roundtrip` / `decodeFullB64_roundtrip`, whose statement is
`encodeB{32,64} bs = some ⟨n, s⟩ → decodeFullB{32,64} s = some bs`.

`Bench.lean` (the `bench` executable) value-checks each base byte-for-byte
against RFC 4648 §10 (16/32/64) and hand vectors (2/4/8/10), plus the
rejection/canonicality cases. The checks are `example … := rfl`, so they run at
**elaboration** time: a wrong vector fails the build.

## Usage

Each base exposes a block-level `apply`/`unapply` pair (characters → bytes and
back) plus the `Codec` value and its run. The block pair has a `Repr`, so it is
what you can print directly:

```lean
import BaseN

-- Base16: one byte → two uppercase hex chars, and back.
#eval BaseN.Base16.hexBlockUnapply 0x66            -- some [54, 54] = "66"
#eval BaseN.Base16.hexBlockApply [0x36, 0x36]      -- some 102   = 0x66

-- Base64: three bytes → four base64 chars, and back.
#eval BaseN.Base64.b64BlockUnapply [0x66, 0x6F, 0x6F]        -- some [90,109,57,118] = "Zm9v"
#eval BaseN.Base64.b64BlockApply [0x5A, 0x6D, 0x39, 0x76]    -- some [102,111,111]  = [0x66,0x6F,0x6F]
```

For whole strings use the run: `encodeHex : List UInt8 → Option (Sigma fun n =>
Bytes n)` with `decodeFull hexElem hexConsumesByte : … → Option (List UInt8)`,
and `encodeB64` / `decodeFullB64` for base64. (Those return `Sigma`/`Bytes`,
which have no `Repr`, so they are checked in `Bench.lean` rather than `#eval`'d
here.)

## The substrate and proof discipline

Every codec is a pure function over the `codec` `Bytes n` (= `Fin n → UInt8`)
substrate — no `String`, no opaque buffer, no `@[extern]` C seam, no per-format
C. The `Option` in the encoder is the only partiality; a malformed input decodes
to `none`.

Beyond roundtrip, each base proves the properties that make the encoding a
**bijection with a canonical form**, not merely an invertible function:

- `encode_injective` (and `encodeB{32,64}_injective`) — encode is injective;
- the converse / canonicality law — roundtrip alone does **not** imply it — stated
  at the library's real types (`decodeFull : … → Bytes n → Option (List UInt8)`,
  `encode… : List UInt8 → Option (Σ n, Bytes n)`), e.g.

  ```
  decodeFullB32 s = some v  →  encodeB32 v = some ⟨n, s⟩     (decodeFullB32_conv)
  decodeFull digElem digConsumesByte n s = some v → encodeDig v = some ⟨n, s⟩
                                                             (decode_encode_inverse)
  ```

  **An earlier revision rendered this as `decode c = some b → encode b = c`**, and
  that matches **no declaration** in the package (`BaseN.Base16.decode` does not
  exist; `` `decode `` is `Codec.decode` in the dependency, a _list_-returning
  decoder, not this partial one). It also used the shorthand this very README
  forbids further down (`codec-audit-round-five` R6-20/R6-32). The `Σ n, Bytes n`
  in the encoder's result is the length index: the two sides are different types, so
  an equation between `c` and `b` cannot be stated without it;

- `decodeFull*_char` — a string decodes **iff** it is the canonical encoding of
  some byte list, which is what rejects non-zero pad bits
  (§3.5: `"Zh=="` and `"Zm9="` are not canonical and decode to `none`);
- per-base `rejects_overflow` where an overflow is reachable (base8 `"400"`,
  base10 `"256"`; base2/4 top out at exactly 255, so no such input exists).

The digit math is done in `Nat` (`UInt8.toNat`) with a thin `UInt8` surface; the
alphabet characters are ASCII and the **union across the seven bases is 43-122**
(`+`=43 and `/`=47 for base64, `0`-`9`=48-57, `A`-`Z`=65-90, `a`-`z`=97-122), all
`< 256`, so `UInt8.ofNat`/`.toNat` are transparent. (An earlier revision said
"48-122"; that is the union **excluding** base64's two symbols, so it was wrong for
the base where the range matters most — `codec-audit-round-five` R6-21. The `< 256`
conclusion is true either way, which is why nothing in the proofs moves.) See
`AGENTS.md`/`PAPER.md` in the sibling `lean-codec` for the
two-layer trust-seam posture this package inherits (pure-Lean spec, no Layer-2 C
here).

## Build

```bash
nix develop            # lean + lake + elan + clang on PATH
lake build             # the proof gate: zero `sorry`, zero warnings
lake build bench       # the vector lane (a wrong vector fails the build)
nix build .#native     # the Nix verification gate
nix build .#bench      # the vector lane, sandboxed (builds and runs it)
```

`Axioms.lean` is a `@[default_target]` library, so `lake build` also runs its
`#guard_msgs` gates: a `Classical.choice` regression fails the build.

## License

AGPL-3.0-or-later (or a commercial license from the author). See `LICENSE.md`.
