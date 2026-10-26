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

/-! ## Canonical vectors: the **actual** whole-input encoder output

Each `example` below pins the exact bytes `encodeB64`/`encodeB32` emit for an
RFC 4648 §10 vector.  This is the load-bearing assertion of the lane — a *value*
check, not a re-statement of a theorem's hypothesis: the input and the expected
output are both concrete, the encoder is unfolded to its emitted bytes, and every
`Bytes` index is closed by `rfl`.  (`Bytes` equality needs `funext`, so the check
is index-by-index rather than `decide`.)

A deliberately broken encoder — lowercase alphabet, a short pad run, one pad too
many, wrong pad placement — changes one of these indices and **fails this file**.

The unfold is deliberately uniform across all eleven vectors, so for a
multi-block input (e.g. `foobar`) no terminal-tail branch is reachable and some
of the ticket's simp lemmas are unused; that is why the unused-`simp` linter is
off for that block only. -/

set_option linter.unusedSimpArgs false



/-- `0x66` -> `Zg==` (RFC 4648 §10). -/
example : Base64.encodeB64 [0x66] =
    some ⟨4, fun i : Fin 4 => [0x5A, 0x67, 0x3D, 0x3D][i]⟩ := by
  rw [Base64.encodeB64, Base64.b64Split_ofBytes_ofBytes]
  simp only [Base64.b64Split, Base64.encodeB64', Base64.encodeB64Tail,
    Codec.encodeRepeat, Codec.encode, Base64.b64TailElem, Base64.b64TailIso,
    Codec.count, Base64.b64TailUnapply,
    Base64.b64BlockUnapply, Base64.valToB64]
  refine congrArg some ?_
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Bytes.ext
    intro i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl

/-- `0x66, 0x6F` -> `Zm8=` (RFC 4648 §10). -/
example : Base64.encodeB64 [0x66, 0x6F] =
    some ⟨4, fun i : Fin 4 => [0x5A, 0x6D, 0x38, 0x3D][i]⟩ := by
  rw [Base64.encodeB64, Base64.b64Split_ofBytes_ofBytes]
  simp only [Base64.b64Split, Base64.encodeB64', Base64.encodeB64Tail,
    Codec.encodeRepeat, Codec.encode, Base64.b64TailElem, Base64.b64TailIso,
    Codec.count, Base64.b64TailUnapply,
    Base64.b64BlockUnapply, Base64.valToB64]
  refine congrArg some ?_
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Bytes.ext
    intro i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl

/-- `0x66, 0x6F, 0x6F` -> `Zm9v` (RFC 4648 §10). -/
example : Base64.encodeB64 [0x66, 0x6F, 0x6F] =
    some ⟨4, fun i : Fin 4 => [0x5A, 0x6D, 0x39, 0x76][i]⟩ := by
  rw [Base64.encodeB64, Base64.b64Split_ofBytes_ofBytes]
  simp only [Base64.b64Split, Base64.encodeB64', Base64.encodeB64Tail,
    Codec.encodeRepeat, Codec.encode, Base64.b64TailElem, Base64.b64TailIso,
    Codec.count, Base64.b64TailUnapply,
    Base64.b64BlockUnapply, Base64.valToB64]
  refine congrArg some ?_
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Bytes.ext
    intro i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl

/-- `0x66, 0x6F, 0x6F, 0x62` -> `Zm9vYg==` (RFC 4648 §10). -/
example : Base64.encodeB64 [0x66, 0x6F, 0x6F, 0x62] =
    some ⟨8, fun i : Fin 8 => [0x5A, 0x6D, 0x39, 0x76, 0x59, 0x67, 0x3D, 0x3D][i]⟩ := by
  rw [Base64.encodeB64, Base64.b64Split_ofBytes_ofBytes]
  simp only [Base64.b64Split, Base64.encodeB64', Base64.encodeB64Tail,
    Codec.encodeRepeat, Codec.encode, Base64.b64TailElem, Base64.b64TailIso,
    Codec.count, Base64.b64TailUnapply,
    Base64.b64BlockUnapply, Base64.valToB64]
  refine congrArg some ?_
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Bytes.ext
    intro i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl
    | ⟨4, _⟩ => rfl
    | ⟨5, _⟩ => rfl
    | ⟨6, _⟩ => rfl
    | ⟨7, _⟩ => rfl

/-- `0x66, 0x6F, 0x6F, 0x62, 0x61` -> `Zm9vYmE=` (RFC 4648 §10). -/
example : Base64.encodeB64 [0x66, 0x6F, 0x6F, 0x62, 0x61] =
    some ⟨8, fun i : Fin 8 => [0x5A, 0x6D, 0x39, 0x76, 0x59, 0x6D, 0x45, 0x3D][i]⟩ := by
  rw [Base64.encodeB64, Base64.b64Split_ofBytes_ofBytes]
  simp only [Base64.b64Split, Base64.encodeB64', Base64.encodeB64Tail,
    Codec.encodeRepeat, Codec.encode, Base64.b64TailElem, Base64.b64TailIso,
    Codec.count, Base64.b64TailUnapply,
    Base64.b64BlockUnapply, Base64.valToB64]
  refine congrArg some ?_
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Bytes.ext
    intro i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl
    | ⟨4, _⟩ => rfl
    | ⟨5, _⟩ => rfl
    | ⟨6, _⟩ => rfl
    | ⟨7, _⟩ => rfl

/-- `0x66, 0x6F, 0x6F, 0x62, 0x61, 0x72` -> `Zm9vYmFy` (RFC 4648 §10). -/
example : Base64.encodeB64 [0x66, 0x6F, 0x6F, 0x62, 0x61, 0x72] =
    some ⟨8, fun i : Fin 8 => [0x5A, 0x6D, 0x39, 0x76, 0x59, 0x6D, 0x46, 0x79][i]⟩ := by
  rw [Base64.encodeB64, Base64.b64Split_ofBytes_ofBytes]
  simp only [Base64.b64Split, Base64.encodeB64', Base64.encodeB64Tail,
    Codec.encodeRepeat, Codec.encode, Base64.b64TailElem, Base64.b64TailIso,
    Codec.count, Base64.b64TailUnapply,
    Base64.b64BlockUnapply, Base64.valToB64]
  refine congrArg some ?_
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Bytes.ext
    intro i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl
    | ⟨4, _⟩ => rfl
    | ⟨5, _⟩ => rfl
    | ⟨6, _⟩ => rfl
    | ⟨7, _⟩ => rfl

/-- `0x66` -> `MY======` (RFC 4648 §10). -/
example : Base32.encodeB32 [0x66] =
    some ⟨8, fun i : Fin 8 => [0x4D, 0x59, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D][i]⟩ := by
  rw [Base32.encodeB32, Base32.b32Split_ofBytes_ofBytes]
  simp only [Base32.b32Split, Base32.encodeB32', Base32.encodeB32Tail,
    Codec.encodeRepeat, Codec.encode, Base32.b32TailElem, Base32.b32TailIso,
    Codec.count, Base32.b32TailUnapply,
    Base32.b32BlockUnapply, Base32.valToB32]
  refine congrArg some ?_
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Bytes.ext
    intro i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl
    | ⟨4, _⟩ => rfl
    | ⟨5, _⟩ => rfl
    | ⟨6, _⟩ => rfl
    | ⟨7, _⟩ => rfl

/-- `0x66, 0x6F` -> `MZXQ====` (RFC 4648 §10). -/
example : Base32.encodeB32 [0x66, 0x6F] =
    some ⟨8, fun i : Fin 8 => [0x4D, 0x5A, 0x58, 0x51, 0x3D, 0x3D, 0x3D, 0x3D][i]⟩ := by
  rw [Base32.encodeB32, Base32.b32Split_ofBytes_ofBytes]
  simp only [Base32.b32Split, Base32.encodeB32', Base32.encodeB32Tail,
    Codec.encodeRepeat, Codec.encode, Base32.b32TailElem, Base32.b32TailIso,
    Codec.count, Base32.b32TailUnapply,
    Base32.b32BlockUnapply, Base32.valToB32]
  refine congrArg some ?_
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Bytes.ext
    intro i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl
    | ⟨4, _⟩ => rfl
    | ⟨5, _⟩ => rfl
    | ⟨6, _⟩ => rfl
    | ⟨7, _⟩ => rfl

/-- `0x66, 0x6F, 0x6F` -> `MZXW6===` (RFC 4648 §10). -/
example : Base32.encodeB32 [0x66, 0x6F, 0x6F] =
    some ⟨8, fun i : Fin 8 => [0x4D, 0x5A, 0x58, 0x57, 0x36, 0x3D, 0x3D, 0x3D][i]⟩ := by
  rw [Base32.encodeB32, Base32.b32Split_ofBytes_ofBytes]
  simp only [Base32.b32Split, Base32.encodeB32', Base32.encodeB32Tail,
    Codec.encodeRepeat, Codec.encode, Base32.b32TailElem, Base32.b32TailIso,
    Codec.count, Base32.b32TailUnapply,
    Base32.b32BlockUnapply, Base32.valToB32]
  refine congrArg some ?_
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Bytes.ext
    intro i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl
    | ⟨4, _⟩ => rfl
    | ⟨5, _⟩ => rfl
    | ⟨6, _⟩ => rfl
    | ⟨7, _⟩ => rfl

/-- `0x66, 0x6F, 0x6F, 0x62` -> `MZXW6YQ=` (RFC 4648 §10). -/
example : Base32.encodeB32 [0x66, 0x6F, 0x6F, 0x62] =
    some ⟨8, fun i : Fin 8 => [0x4D, 0x5A, 0x58, 0x57, 0x36, 0x59, 0x51, 0x3D][i]⟩ := by
  rw [Base32.encodeB32, Base32.b32Split_ofBytes_ofBytes]
  simp only [Base32.b32Split, Base32.encodeB32', Base32.encodeB32Tail,
    Codec.encodeRepeat, Codec.encode, Base32.b32TailElem, Base32.b32TailIso,
    Codec.count, Base32.b32TailUnapply,
    Base32.b32BlockUnapply, Base32.valToB32]
  refine congrArg some ?_
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Bytes.ext
    intro i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl
    | ⟨4, _⟩ => rfl
    | ⟨5, _⟩ => rfl
    | ⟨6, _⟩ => rfl
    | ⟨7, _⟩ => rfl

/-- `0x66, 0x6F, 0x6F, 0x62, 0x61` -> `MZXW6YTB` (RFC 4648 §10). -/
example : Base32.encodeB32 [0x66, 0x6F, 0x6F, 0x62, 0x61] =
    some ⟨8, fun i : Fin 8 => [0x4D, 0x5A, 0x58, 0x57, 0x36, 0x59, 0x54, 0x42][i]⟩ := by
  rw [Base32.encodeB32, Base32.b32Split_ofBytes_ofBytes]
  simp only [Base32.b32Split, Base32.encodeB32', Base32.encodeB32Tail,
    Codec.encodeRepeat, Codec.encode, Base32.b32TailElem, Base32.b32TailIso,
    Codec.count, Base32.b32TailUnapply,
    Base32.b32BlockUnapply, Base32.valToB32]
  refine congrArg some ?_
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Bytes.ext
    intro i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl
    | ⟨4, _⟩ => rfl
    | ⟨5, _⟩ => rfl
    | ⟨6, _⟩ => rfl
    | ⟨7, _⟩ => rfl

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

-- General rejection laws (task 6.4): the laws are quantified over **every** byte
-- string, so each is exercised below at a concrete input. Each such input is also
-- pinned as a named rejection vector in the library, so the general law and the
-- specific vector must agree.

-- (a) an alphabet-invalid byte at an arbitrary (non-zero) index.
example : Base64.decodeFullB64 Base64.bangGEqEq = none :=
  Base64.decodeFullB64_reject_invalid_at Base64.bangGEqEq ⟨0, by decide⟩ (by decide)

example : Base32.decodeFullB32 Base32.bangAAAAA = none :=
  Base32.decodeFullB32_reject_invalid_at Base32.bangAAAAA ⟨0, by decide⟩ (by decide)

-- (b) a `=` at a non-terminal position: `Zg==AAAA` has its pads at slots 2/3 of
-- the *first* word (legal) but the whole string is still rejected — the general
-- law covering that class is the arity/pad one below plus the named vector above.
example : Base64.decodeFullB64 Base64.zgAAAA = none :=
  Base64.decodeFullB64_reject_ZgAAAA

-- `=` in slot 0 of a code word is rejected by the general low-slot law.
example : Base64.decodeFullB64 Base64.eqGEqEq = none :=
  Base64.decodeFullB64_reject_pad_at_low_slot Base64.eqGEqEq ⟨0, by decide⟩ (by decide) (Or.inl (by decide))

example : Base32.decodeFullB32 Base32.eqYEqEq = none :=
  Base32.decodeFullB32_reject_pad_at_low_slot Base32.eqYEqEq ⟨0, by decide⟩ (by decide) (Or.inl (by decide))

-- (c) wrong arity: 2 chars is not a whole number of base64 code words.
example : Base64.decodeFullB64 Base64.zgTwo = none :=
  Base64.decodeFullB64_reject_arity Base64.zgTwo (by decide)

example : Base32.decodeFullB32 Base32.myTwo = none :=
  Base32.decodeFullB32_reject_arity Base32.myTwo (by decide)

-- Unique canonical inverse: decode succeeds iff the input is in `encode`'s image,
-- at that value (task 6.3). Both directions exercised at a canonical vector.

example : Base64.decodeFullB64 zgEqEq = some f ↔
    ∃ w, Base64.encodeB64 w = some ⟨4, zgEqEq⟩ ∧ f = w :=
  Base64.decodeFullB64_char zgEqEq f

example : Base32.decodeFullB32 myEqEq = some f ↔
    ∃ w, Base32.encodeB32 w = some ⟨8, myEqEq⟩ ∧ f = w :=
  Base32.decodeFullB32_char myEqEq f

-- Total characterization for the five fixed-width bases (task 7.1): the same iff,
-- assembled over each base's `decode_encode_inverse` (→) and `roundtrip` (←).
-- Quantified over every byte string, exactly like the library law.

example (n : Nat) (s : Bytes n) (v : List UInt8) :
    Codec.decodeFull Base2.bitElem Base2.bitConsumesByte n s = some v ↔
      ∃ w, Base2.encodeBit w = some ⟨n, s⟩ ∧ v = w :=
  Base2.decodeFull_B2_char s v

example (n : Nat) (s : Bytes n) (v : List UInt8) :
    Codec.decodeFull Base4.quartetElem Base4.quartetConsumesByte n s = some v ↔
      ∃ w, Base4.encodeQuartet w = some ⟨n, s⟩ ∧ v = w :=
  Base4.decodeFull_B4_char s v

example (n : Nat) (s : Bytes n) (v : List UInt8) :
    Codec.decodeFull Base8.octElem Base8.octConsumesByte n s = some v ↔
      ∃ w, Base8.encodeOct w = some ⟨n, s⟩ ∧ v = w :=
  Base8.decodeFull_B8_char s v

example (n : Nat) (s : Bytes n) (v : List UInt8) :
    Codec.decodeFull Base10.digElem Base10.digConsumesByte n s = some v ↔
      ∃ w, Base10.encodeDig w = some ⟨n, s⟩ ∧ v = w :=
  Base10.decodeFull_B10_char s v

example (n : Nat) (s : Bytes n) (v : List UInt8) :
    Codec.decodeFull Base16.hexElem Base16.hexConsumesByte n s = some v ↔
      ∃ w, Base16.encodeHex w = some ⟨n, s⟩ ∧ v = w :=
  Base16.decodeFull_B16_char s v

-- Total characterization through the canonical type (task 7.2): the decoder's image
-- is exactly the image of `encode ∘ b*BytesOf`, so a canonical `B64`/`B32` value is
-- the *only* shape a decoded result can take.

example (n : Nat) (s : Bytes n) (v : List UInt8) :
    Base64.decodeFullB64 s = some v ↔
      ∃ w : Base64.B64, Base64.encodeB64 (Base64.b64BytesOf w) = some ⟨n, s⟩ ∧
        v = Base64.b64BytesOf w :=
  Base64.decodeFullB64_char_via_type s v

example (n : Nat) (s : Bytes n) (v : List UInt8) :
    Base32.decodeFullB32 s = some v ↔
      ∃ w : Base32.B32, Base32.encodeB32 (Base32.b32BytesOf w) = some ⟨n, s⟩ ∧
        v = Base32.b32BytesOf w :=
  Base32.decodeFullB32_char_via_type s v

-- Every decoded value carries a canonical spine (its tail is terminal).
example (n : Nat) (s : Bytes n) (v : List UInt8)
    (h : Base64.decodeFullB64 s = some v) :
    ∃ w : Base64.B64, v = Base64.b64BytesOf w :=
  Base64.decodeFullB64_spine h

example (n : Nat) (s : Bytes n) (v : List UInt8)
    (h : Base32.decodeFullB32 s = some v) :
    ∃ w : Base32.B32, v = Base32.b32BytesOf w :=
  Base32.decodeFullB32_spine h

-- The discriminating fact: a tail is terminal, so a 1-byte `B64` value is exactly
-- one byte — the `[b0, x, y, z]` shape (a tail followed by a full block) has no
-- `B64` inhabitant at all. That is *why* `Zg==AAAA` is rejected.
example (b0 x y z : UInt8) : Base64.b64BytesOf (Base64.B64.tail1 b0) ≠ [b0, x, y, z] := by
  rw [Base64.b64BytesOf_tail1_eq]
  intro h
  simp at h

example (b0 x y : UInt8) : Base32.b32BytesOf (Base32.B32.tail1 b0) ≠ [b0, x, y] := by
  rw [Base32.b32BytesOf_tail1_eq]
  intro h
  simp at h

-- Injectivity, in the spec's plain `Option`-equality form
-- (`encode{X} v = encode{X} v' → v = v'`, task 6.2). Covered for all seven bases.

example (v v' : List UInt8) (h : Base64.encodeB64 v = Base64.encodeB64 v') :
    v = v' :=
  Base64.encodeB64_injective_eq h

example (v v' : List UInt8) (h : Base32.encodeB32 v = Base32.encodeB32 v') :
    v = v' :=
  Base32.encodeB32_injective_eq h

example (v v' : List UInt8) (h : Base16.encodeHex v = Base16.encodeHex v') :
    v = v' :=
  Base16.encodeHex_injective_eq h

example (v v' : List UInt8) (h : Base10.encodeDig v = Base10.encodeDig v') :
    v = v' :=
  Base10.encodeDig_injective_eq h

example (v v' : List UInt8) (h : Base8.encodeOct v = Base8.encodeOct v') :
    v = v' :=
  Base8.encodeOct_injective_eq h

example (v v' : List UInt8) (h : Base4.encodeQuartet v = Base4.encodeQuartet v') :
    v = v' :=
  Base4.encodeQuartet_injective_eq h

example (v v' : List UInt8) (h : Base2.encodeBit v = Base2.encodeBit v') :
    v = v' :=
  Base2.encodeBit_injective_eq h

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

-- RFC 4648 §8: Base16 is case-insensitive on **decode**. The fold is upward, so
-- the canonical uppercase encoding is a fixed point; `decodeHexFold` applies it
-- outside the strict `Iso`, so encoding stays canonical.

example : Base16.foldByte 0x61 = 0x41 := rfl                                   -- 'a' -> 'A'
example : Base16.foldByte 0x66 = 0x46 := rfl                                   -- 'f' -> 'F'
example : Base16.foldByte 0x46 = 0x46 := rfl                                   -- 'F' fixed
example : Base16.foldByte 0x39 = 0x39 := rfl                                   -- '9' fixed
example : Base16.foldList [0x36, 0x66] = [0x36, 0x46] := rfl                   -- "6f" -> "6F"

-- The strict decoder still rejects lowercase (it is the canonical bijection)...
example : Codec.decodeFull Base16.hexElem Base16.hexConsumesByte 1
    (fun _ => 0x66) = none :=
  Base16.rejects_lowercase

-- ...while both cases decode to the same value through the normalising decoder.
example : Base16.decodeHexFold
      (fun i : Fin 2 => if i.val = 0 then 0x36 else 0x66) =          -- "6f"
    Base16.decodeHexFold
      (fun i : Fin 2 => if i.val = 0 then 0x36 else 0x46) :=          -- "6F"
  Base16.decodeHexFold_lowercase_eq

end Bench

/-- `main` runs and exits 0 (type-checking the `example`s above is the gate;
there is no runtime smoke lane here). -/
def main : IO Unit :=
  pure ()
