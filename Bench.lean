/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import BaseN

/-!
# Byte-exact vector bench lane

Value-checks each base **byte-for-byte** against the authoritative vectors:

  * base16/32/64 — RFC 4648 §10 (pinned in the sibling `lean-codec` repo's
    `openspec/changes/lean-basen/rfc4648.md`).
  * base2/4/8/10 — hand vectors for this package's own spec (no RFC).

Each vector is an `example` theorem closed by `decide`/`rfl`, so the bench lane
is a *proof* that the encoder emits exactly the expected bytes (not just a length
check), and the roundtrip laws (`BaseN.roundtrip` and each `BaseX.roundtrip`) are
re-instantiated over the vector byte-strings.
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

-- Base16 (RFC 4648 §8/§10, uppercase canonical)

example : Base16.encode ([] : List UInt8) = [] := rfl
example : Base16.encode f = [0x36, 0x36] := rfl                       -- "66"
example : Base16.encode fo = [0x36, 0x36, 0x36, 0x46] := rfl          -- "666F"
example : Base16.encode foo = [0x36, 0x36, 0x36, 0x46, 0x36, 0x46] := rfl            -- "666F6F"
example : Base16.encode foob = [0x36, 0x36, 0x36, 0x46, 0x36, 0x46, 0x36, 0x32] := rfl            -- "666F6F62"
example : Base16.encode fooba = [0x36, 0x36, 0x36, 0x46, 0x36, 0x46, 0x36, 0x32, 0x36, 0x31] := rfl  -- "666F6F6261"
example : Base16.encode foobar = [0x36, 0x36, 0x36, 0x46, 0x36, 0x46, 0x36, 0x32, 0x36, 0x31, 0x37, 0x32] := rfl -- "666F6F626172"

-- Base32 (RFC 4648 §6/§10)

example : Base32.encode ([] : List UInt8) = [] := rfl
example : Base32.encode f = [0x4D, 0x59, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D] := rfl -- "MY======"
example : Base32.encode fo = [0x4D, 0x5A, 0x58, 0x51, 0x3D, 0x3D, 0x3D, 0x3D] := rfl -- "MZXQ===="
example : Base32.encode foo = [0x4D, 0x5A, 0x58, 0x57, 0x36, 0x3D, 0x3D, 0x3D] := rfl -- "MZXW6==="
example : Base32.encode foob = [0x4D, 0x5A, 0x58, 0x57, 0x36, 0x59, 0x51, 0x3D] := rfl -- "MZXW6YQ="
example : Base32.encode fooba = [0x4D, 0x5A, 0x58, 0x57, 0x36, 0x59, 0x54, 0x42] := rfl -- "MZXW6YTB"
example : Base32.encode foobar =
    [0x4D, 0x5A, 0x58, 0x57, 0x36, 0x59, 0x54, 0x42, 0x4F, 0x49, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D] := rfl -- "MZXW6YTBOI======"

-- Base64 (RFC 4648 §4/§10)

example : Base64.encode ([] : List UInt8) = [] := rfl
example : Base64.encode f = [0x5A, 0x67, 0x3D, 0x3D] := rfl           -- "Zg=="
example : Base64.encode fo = [0x5A, 0x6D, 0x38, 0x3D] := rfl          -- "Zm8="
example : Base64.encode foo = [0x5A, 0x6D, 0x39, 0x76] := rfl         -- "Zm9v"
example : Base64.encode foob = [0x5A, 0x6D, 0x39, 0x76, 0x59, 0x67, 0x3D, 0x3D] := rfl -- "Zm9vYg=="
example : Base64.encode fooba = [0x5A, 0x6D, 0x39, 0x76, 0x59, 0x6D, 0x45, 0x3D] := rfl -- "Zm9vYmE="
example : Base64.encode foobar = [0x5A, 0x6D, 0x39, 0x76, 0x59, 0x6D, 0x46, 0x79] := rfl -- "Zm9vYmFy"

-- Base2/4/8/10 — hand vectors (this package's own spec)

example : Base2.encode [0x66] = [0x30, 0x31, 0x31, 0x30, 0x30, 0x31, 0x31, 0x30] := rfl -- "01100110"
example : Base2.encode [0x66, 0x6F] =
    [0x30, 0x31, 0x31, 0x30, 0x30, 0x31, 0x31, 0x30, 0x30, 0x31, 0x31, 0x30, 0x31, 0x31, 0x31, 0x31] := rfl -- "01100110" ++ "01101111"

example : Base4.encode [0x66] = [0x31, 0x32, 0x31, 0x32] := rfl  -- "1212"
example : Base4.encode [0x66, 0x6F] = [0x31, 0x32, 0x31, 0x32, 0x31, 0x32, 0x33, 0x33] := rfl -- "12121233"

example : Base8.encode [0x66] = [0x31, 0x34, 0x36] := rfl   -- "146"
example : Base8.encode [0xFF] = [0x33, 0x37, 0x37] := rfl   -- "377"

example : Base10.encode [0x66] = [0x31, 0x30, 0x32] := rfl  -- "102"
example : Base10.encode [0xFF] = [0x32, 0x35, 0x35] := rfl  -- "255"

-- Roundtrip laws, re-instantiated over the RFC byte-strings.

example : Base16.decode (Base16.encode foobar) = some foobar := Base16.roundtrip foobar
example : Base32.decode (Base32.encode foobar) = some foobar := Base32.roundtrip foobar
example : Base64.decode (Base64.encode foobar) = some foobar := Base64.roundtrip foobar
example : Base2.decode (Base2.encode foobar) = some foobar := Base2.roundtrip foobar
example : Base4.decode (Base4.encode foobar) = some foobar := Base4.roundtrip foobar
example : Base8.decode (Base8.encode foobar) = some foobar := Base8.roundtrip foobar
example : Base10.decode (Base10.encode foobar) = some foobar := Base10.roundtrip foobar

-- The facade dispatch, over every base (type-checked).

#check (BaseN.roundtrip Base.B2 foobar)
#check (BaseN.roundtrip Base.B4 foobar)
#check (BaseN.roundtrip Base.B8 foobar)
#check (BaseN.roundtrip Base.B10 foobar)
#check (BaseN.roundtrip Base.B16 foobar)
#check (BaseN.roundtrip Base.B32 foobar)
#check (BaseN.roundtrip Base.B64 foobar)

/-- The byte-exact smoke checks, as a runnable `#eval` assertion (returns `true`). -/
def smoke : Bool :=
  Base32.encode f == [0x4D, 0x59, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D] &&
  Base64.encode f == [0x5A, 0x67, 0x3D, 0x3D] &&
  Base64.encode foobar == [0x5A, 0x6D, 0x39, 0x76, 0x59, 0x6D, 0x46, 0x79] &&
  Base32.decode (Base32.encode foobar) == some foobar &&
  Base64.decode (Base64.encode foobar) == some foobar

#eval smoke  -- true

end Bench

/-- `main` runs the smoke checks and exits non-zero on a mismatch. -/
def main : IO Unit := do
  if !(Bench.smoke) then
    IO.eprintln "vector mismatch"
    IO.Process.exit 1
