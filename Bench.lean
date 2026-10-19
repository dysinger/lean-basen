/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import BaseN

/-!
# Byte-exact vector bench lane

Value-checks each base **byte-for-byte** against the authoritative vectors:

  * base16/32/64 — RFC 4648 §10 (pinned in the sibling `lean-codec` repo's
    `openspec/changes/lean-basen/rfc4648.md`).
  * base2/4/8/10 — hand vectors for this package's own spec (no RFC).

Each base is now a `Codec` value over `satisfy`/`count`/`iso` plus the
repetition layer, so the byte-exact checks are at the *block* level (the block
`Iso`'s `unapply` direction, which computes the concrete char bytes), and the
roundtrip laws are re-instantiated over the inherited `roundtrip` theorems.
-/

namespace Bench

open BaseN

/-- RFC 4648 §10 byte-strings. -/
def f : List UInt8 := [0x66]
def fo : List UInt8 := [0x66, 0x6F]
def foo : List UInt8 := [0x66, 0x6F, 0x6F]
def foob : List UInt8 := [0x66, 0x6F, 0x6F, 0x62]
def fooba : List UInt8 := [0x66, 0x6F, 0x6F, 0x62, 0x61]
def foobar : List UInt8 := [0x66, 0x6F, 0x6F, 0x62, 0x61, 0x72]

-- Base16 (RFC 4648 §8/§10, uppercase canonical): one byte → two hex chars.

example : Base16.hexBlockUnapply 0x66 = some [0x36, 0x36] := rfl            -- "66"
example : Base16.hexBlockUnapply 0x6F = some [0x36, 0x46] := rfl            -- "6F"

-- Base32 (RFC 4648 §6/§10): 5 bytes → 8 chars; tails padded.

example : Base32.b32BlockUnapply [0x66] = some [0x4D, 0x59, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D] := rfl -- "MY======"
example : Base32.b32BlockUnapply [0x66, 0x6F] = some [0x4D, 0x5A, 0x58, 0x51, 0x3D, 0x3D, 0x3D, 0x3D] := rfl -- "MZXQ===="
example : Base32.b32BlockUnapply [0x66, 0x6F, 0x6F] = some [0x4D, 0x5A, 0x58, 0x57, 0x36, 0x3D, 0x3D, 0x3D] := rfl -- "MZXW6==="
example : Base32.b32BlockUnapply [0x66, 0x6F, 0x6F, 0x62] = some [0x4D, 0x5A, 0x58, 0x57, 0x36, 0x59, 0x51, 0x3D] := rfl -- "MZXW6YQ="
example : Base32.b32BlockUnapply [0x66, 0x6F, 0x6F, 0x62, 0x61] = some [0x4D, 0x5A, 0x58, 0x57, 0x36, 0x59, 0x54, 0x42] := rfl -- "MZXW6YTB"

-- Base64 (RFC 4648 §4/§10): 3 bytes → 4 chars; tails padded.

example : Base64.b64BlockUnapply [0x66] = some [0x5A, 0x67, 0x3D, 0x3D] := rfl        -- "Zg=="
example : Base64.b64BlockUnapply [0x66, 0x6F] = some [0x5A, 0x6D, 0x38, 0x3D] := rfl    -- "Zm8="
example : Base64.b64BlockUnapply [0x66, 0x6F, 0x6F] = some [0x5A, 0x6D, 0x39, 0x76] := rfl -- "Zm9v"

-- Base2/4/8/10 — hand vectors (this package's own spec).

example : Base2.bitBlockUnapply 0x66 = some [0x30, 0x31, 0x31, 0x30, 0x30, 0x31, 0x31, 0x30] := rfl -- "01100110"
example : Base4.quartetBlockUnapply 0x66 = some [0x31, 0x32, 0x31, 0x32] := rfl          -- "1212"
example : Base8.octBlockUnapply 0x66 = some [0x31, 0x34, 0x36] := rfl                     -- "146"
example : Base10.digBlockUnapply 0x66 = some [0x31, 0x30, 0x32] := rfl                     -- "102"

-- Roundtrip laws, re-instantiated over the RFC byte-strings.

example (n : Nat) (s : Bytes n) : Base16.encodeHex foobar = some ⟨n, s⟩ →
    Codec.decodeFull Base16.hexElem Base16.hexConsumesByte n s = some foobar :=
  Base16.roundtrip foobar

example (n : Nat) (s : Bytes n) : Base2.encodeBit foobar = some ⟨n, s⟩ →
    Codec.decodeFull Base2.bitElem Base2.bitConsumesByte n s = some foobar :=
  Base2.roundtrip foobar

example (n : Nat) (s : Bytes n) : Base4.encodeQuartet foobar = some ⟨n, s⟩ →
    Codec.decodeFull Base4.quartetElem Base4.quartetConsumesByte n s = some foobar :=
  Base4.roundtrip foobar

example (n : Nat) (s : Bytes n) : Base8.encodeOct foobar = some ⟨n, s⟩ →
    Codec.decodeFull Base8.octElem Base8.octConsumesByte n s = some foobar :=
  Base8.roundtrip foobar

example (n : Nat) (s : Bytes n) : Base10.encodeDig foobar = some ⟨n, s⟩ →
    Codec.decodeFull Base10.digElem Base10.digConsumesByte n s = some foobar :=
  Base10.roundtrip foobar

example (n : Nat) (s : Bytes n) : Base32.encodeB32 [[0x66, 0x6F, 0x6F, 0x62, 0x61], [0x72]] = some ⟨n, s⟩ →
    Codec.decodeFull Base32.b32Elem Base32.b32ConsumesByte n s = some [[0x66, 0x6F, 0x6F, 0x62, 0x61], [0x72]] :=
  Base32.roundtrip [[0x66, 0x6F, 0x6F, 0x62, 0x61], [0x72]]

example (n : Nat) (s : Bytes n) : Base64.encodeB64 [[0x66, 0x6F, 0x6F], [0x62, 0x61, 0x72]] = some ⟨n, s⟩ →
    Codec.decodeFull Base64.b64Elem Base64.b64ConsumesByte n s = some [[0x66, 0x6F, 0x6F], [0x62, 0x61, 0x72]] :=
  Base64.roundtrip [[0x66, 0x6F, 0x6F], [0x62, 0x61, 0x72]]

end Bench

/-- `main` runs and exits 0 (type-checks are the gate; no runtime smoke here). -/
def main : IO Unit :=
  pure ()
