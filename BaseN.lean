/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# BaseN

The base-`N` encoding/decoding package: one verified package covering base 2, 4,
8, 10, 16, 32, and 64, each with a byte-list encoder and decoder (over `UInt8`,
the `codec` `Bytes n` element type), a roundtrip law proved `[propext,
Quot.sound]`-only, and UTF-8/ASCII alphabets per RFC 4648.

This facade re-exports the seven per-base modules and dispatches a single
`roundtrip` theorem over a small inductive `Base`.

  * `BaseN.Base2`  — one bit per `0`/`1` char, 8 chars per byte, MSB-first
  * `BaseN.Base4`  — one quartet per `0`-`3` char, 4 chars per byte
  * `BaseN.Base8`  — octal, 3 digits per byte (RFC-adjacent, no padding)
  * `BaseN.Base10` — decimal digit math, byte-oriented, no sign
  * `BaseN.Base16` — hex, `0-9A-F`, uppercase, no padding (RFC 4648 §8)
  * `BaseN.Base32` — `A-Z2-7`, `=` padding (RFC 4648 §6)
  * `BaseN.Base64` — `A-Za-z0-9+/`, `=` padding (RFC 4648 §4)
-/

import BaseN.Base2
import BaseN.Base4
import BaseN.Base8
import BaseN.Base10
import BaseN.Base16
import BaseN.Base32
import BaseN.Base64

namespace BaseN

/-- The seven bases. -/
inductive Base where
  | B2 | B4 | B8 | B10 | B16 | B32 | B64
  deriving DecidableEq, Repr, Inhabited

/-- `encode b bs` — encode `bs` in base `b`. -/
def encode (b : Base) : List UInt8 → List UInt8 :=
  match b with
  | .B2 => Base2.encode
  | .B4 => Base4.encode
  | .B8 => Base8.encode
  | .B10 => Base10.encode
  | .B16 => Base16.encode
  | .B32 => Base32.encode
  | .B64 => Base64.encode

/-- `decode b bs` — decode `bs` from base `b`, or `none` on malformed input. -/
def decode (b : Base) : List UInt8 → Option (List UInt8) :=
  match b with
  | .B2 => Base2.decode
  | .B4 => Base4.decode
  | .B8 => Base8.decode
  | .B10 => Base10.decode
  | .B16 => Base16.decode
  | .B32 => Base32.decode
  | .B64 => Base64.decode

/-- Every base satisfies the roundtrip law: `decode b (encode b bs) = some bs`. -/
theorem roundtrip (b : Base) (bs : List UInt8) :
    decode b (encode b bs) = some bs := by
  cases b <;> simp [encode, decode, Base2.roundtrip, Base4.roundtrip,
    Base8.roundtrip, Base10.roundtrip, Base16.roundtrip,
    Base32.roundtrip, Base64.roundtrip]

end BaseN
