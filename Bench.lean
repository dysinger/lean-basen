/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import BaseN
import Codec

/-!
# Byte-exact vector bench lane

Value-checks each base **byte-for-byte** against the authoritative vectors:

  * base16/32/64 — RFC 4648 §10 (pinned in the sibling `lean-codec` repo's
    `openspec/changes/lean-basen/rfc4648.md`).
  * base2/4/8/10 — hand vectors for this package's own spec (no RFC).

The fixed-width bases are `Codec` values over `satisfy`/`count`/`iso` + the
repetition layer (value `List UInt8`); the padded bases (32/64) are **strict**
over the terminal-tail value `B32`/`B64` (`encodeB32Strict`/`decodeB32Strict`,
`encodeB64Strict`/`decodeB64Strict`), so the terminal-pad class is *rejected*
structurally (`decode… = none`), not filtered.
-/

namespace Bench

open BaseN
open Codec

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

-- Roundtrip laws, re-instantiated over the RFC byte-strings (fixed-width bases).

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

-- Strict base32/64: roundtrip, canonical encoding, and rejection vectors.

example : Base64.decodeB64Strict (Base64.encodeB64Strict (Base64.B64.full 0x66 0x6F 0x6F Base64.B64.nil)) =
    some (Base64.B64.full 0x66 0x6F 0x6F Base64.B64.nil) := rfl

example : Base32.decodeB32Strict (Base32.encodeB32Strict (Base32.B32.full 0x66 0x6F 0x6F 0x62 0x61 Base32.B32.nil)) =
    some (Base32.B32.full 0x66 0x6F 0x6F 0x62 0x61 Base32.B32.nil) := rfl

-- Canonical encoding: the RFC vectors re-expressed over the strict surface.

example : Base64.encodeB64Strict (Base64.B64.tail1 0x66) = [0x5A, 0x67, 0x3D, 0x3D] := rfl -- "Zg=="
example : Base64.encodeB64Strict (Base64.B64.tail2 0x66 0x6F) = [0x5A, 0x6D, 0x38, 0x3D] := rfl -- "Zm8="
example : Base64.encodeB64Strict (Base64.B64.full 0x66 0x6F 0x6F Base64.B64.nil) = [0x5A, 0x6D, 0x39, 0x76] := rfl -- "Zm9v"

example : Base32.encodeB32Strict (Base32.B32.tail1 0x66) = [0x4D, 0x59, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D] := rfl -- "MY======"
example : Base32.encodeB32Strict (Base32.B32.full 0x66 0x6F 0x6F 0x62 0x61 Base32.B32.nil) = [0x4D, 0x5A, 0x58, 0x57, 0x36, 0x59, 0x54, 0x42] := rfl -- "MZXW6YTB"

-- Rejection vectors: trailing data after a terminal `=` is `none` (structural).

example : Base64.decodeB64Strict [0x5A, 0x67, 0x3D, 0x3D, 0x41, 0x41, 0x41, 0x41] = none :=
  Base64.rejects_trailing

example : Base32.decodeB32Strict [0x4D, 0x59, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41] = none :=
  Base32.rejects_trailing

end Bench

/-- `main` runs and exits 0 (type-checks are the gate; no runtime smoke here). -/
def main : IO Unit :=
  pure ()
