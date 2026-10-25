/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import BaseN
import Codec

/-!
# Byte-exact vector bench lane

Value-checks each base **byte-for-byte** against the authoritative vectors, all
through the **uniform surface** (`Codec.decodeFull`/`Codec.encode` on each base's
own value, and `decodeFullB64`/`encodeB64`/`decodeFullB32`/`encodeB32` for the
padded bases).  There is **no** bespoke per-format function and **no** facade:
each `example` names the base's value, never a dispatch index.

  * base16/32/64 — RFC 4648 §10 (pinned in the sibling `lean-codec` repo's
    `openspec/changes/lean-basen/rfc4648.md`).
  * base2/4/8/10 — hand vectors for this package's own spec (no RFC).

The padded bases (32/64) are the **composition** — a full-block `Run` (the
derived `many`) followed by an at-most-one-block terminal tail — so the
terminal-pad class (`Zg==AAAA` / `MY======AAAAAAAA`) is *rejected* by the `≤ 1`
terminal-tail guard (`decodeFullB64`/`decodeFullB32 = none`), not filtered.
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

-- Roundtrip laws, re-instantiated over the RFC byte-string `foobar`.

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

-- Base32/64 roundtrip through the uniform composition (`Codec`-value surface).

example (n : Nat) (s : Bytes n) : Base64.encodeB64 foobar = some ⟨n, s⟩ →
    Base64.decodeFullB64 s = some foobar :=
  Base64.decodeFullB64_roundtrip foobar

example (n : Nat) (s : Bytes n) : Base32.encodeB32 foobar = some ⟨n, s⟩ →
    Base32.decodeFullB32 s = some foobar :=
  Base32.decodeFullB32_roundtrip foobar

-- Canonical encoding (alphabet-only blocks + terminal, arity-correct pad):
-- `encodeB64_canonical` decomposes any encoded output into alphabet-only full
-- blocks plus a single RFC-arity padded tail.

example (n : Nat) (s : Bytes n) (he : Base64.encodeB64 foobar = some ⟨n, s⟩) :
    ∃ (blocks : List (List UInt8)) (m₁ m₂ : Nat) (blkBytes : Bytes m₁) (tailBytes : Bytes m₂),
      Codec.encodeRepeat Base64.b64BlockElem blocks = some ⟨m₁, blkBytes⟩ ∧
      Base64.encodeB64Tail (Base64.b64Split_ofBytes (Base64.b64OfBytes foobar)).2 =
        some ⟨m₂, tailBytes⟩ ∧
      List.ofFn s = List.ofFn blkBytes ++ List.ofFn tailBytes := by
  obtain ⟨blocks, m₁, m₂, blkBytes, tailBytes, hblk, htail, hlen, _, _⟩ :=
    Base64.encodeB64_canonical foobar he
  exact ⟨blocks, m₁, m₂, blkBytes, tailBytes, hblk, htail, hlen⟩

example (n : Nat) (s : Bytes n) (he : Base32.encodeB32 foobar = some ⟨n, s⟩) :
    ∃ (blocks : List (List UInt8)) (m₁ m₂ : Nat) (blkBytes : Bytes m₁) (tailBytes : Bytes m₂),
      Codec.encodeRepeat Base32.b32BlockElem blocks = some ⟨m₁, blkBytes⟩ ∧
      Base32.encodeB32Tail (Base32.b32Split_ofBytes (Base32.b32OfBytes foobar)).2 =
        some ⟨m₂, tailBytes⟩ ∧
      List.ofFn s = List.ofFn blkBytes ++ List.ofFn tailBytes := by
  obtain ⟨blocks, m₁, m₂, blkBytes, tailBytes, hblk, htail, hlen, _, _⟩ :=
    Base32.encodeB32_canonical foobar he
  exact ⟨blocks, m₁, m₂, blkBytes, tailBytes, hblk, htail, hlen⟩

-- Rejection vectors: trailing data after a terminal `=` is `none`.

example : Base64.decodeFullB64 Base64.zgAAAA = none :=
  Base64.decodeFullB64_reject_ZgAAAA

example : Base32.decodeFullB32 Base32.myAAAA = none :=
  Base32.decodeFullB32_reject_MYAAAA

/-- `Zg==` as a `Bytes 4` (a canonical 1-byte base64 tail). -/
def zgEqEq : Bytes 4 := fun i => [0x5A, 0x67, 0x3D, 0x3D][i]

/-- `MY======` as a `Bytes 8` (a canonical 1-byte base32 tail). -/
def myEqEq : Bytes 8 := fun i =>
  [0x4D, 0x59, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D][i]

-- Converse: a successful decode re-encodes to exactly the input (canonical).

example (h : Base64.decodeFullB64 zgEqEq = some f) :
    Base64.encodeB64 f = some ⟨4, zgEqEq⟩ :=
  Base64.decodeFullB64_conv zgEqEq f h

example (h : Base32.decodeFullB32 myEqEq = some f) :
    Base32.encodeB32 f = some ⟨8, myEqEq⟩ :=
  Base32.decodeFullB32_conv myEqEq f h

-- Injectivity: a byte list has a unique encoding.

example (n : Nat) (s : Bytes n) (v v' : List UInt8)
    (h : Base64.encodeB64 v = some ⟨n, s⟩) (h' : Base64.encodeB64 v' = some ⟨n, s⟩) :
    v = v' :=
  Base64.encodeB64_injective h h'

example (n : Nat) (s : Bytes n) (v v' : List UInt8)
    (h : Base32.encodeB32 v = some ⟨n, s⟩) (h' : Base32.encodeB32 v' = some ⟨n, s⟩) :
    v = v' :=
  Base32.encodeB32_injective h h'

example (n : Nat) (s : Bytes n) (v v' : List UInt8)
    (h : Base16.encodeHex v = some ⟨n, s⟩) (h' : Base16.encodeHex v' = some ⟨n, s⟩) :
    v = v' :=
  Base16.encode_injective h h'

-- Fixed-width converse + overflow vectors (through the uniform `decodeFull`).

example (n : Nat) (s : Bytes n) (v : List UInt8)
    (h : Codec.decodeFull Base16.hexElem Base16.hexConsumesByte n s = some v) :
    Base16.encodeHex v = some ⟨n, s⟩ :=
  Base16.decode_encode_inverse v h

example : Codec.decodeFull Base8.octElem Base8.octConsumesByte 3
    (fun i : Fin 3 => [0x34, 0x30, 0x30][i]) = none :=
  Base8.rejects_overflow

example : Codec.decodeFull Base10.digElem Base10.digConsumesByte 3
    (fun i : Fin 3 => [0x32, 0x35, 0x36][i]) = none :=
  Base10.rejects_overflow

-- Base16 non-goal (recorded, not a passing vector): lowercase `6f` is rejected.

example : Codec.decodeFull Base16.hexElem Base16.hexConsumesByte 1
    (fun _ => 0x66) = none :=
  Base16.rejects_lowercase

end Bench

/-- `main` runs and exits 0 (type-checks are the gate; no runtime smoke here). -/
def main : IO Unit :=
  pure ()
