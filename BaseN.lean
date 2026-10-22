/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# BaseN

The base-`N` encoding/decoding package: one verified package covering base 2, 4,
8, 10, 16, 32, and 64, each re-expressed as a `codec` `Codec` value over the
`satisfy`/`count`/`iso` primitives plus the productive repetition layer —
decoded and encoded by the single `Codec` operations, "only the codec changes."

Each base is a *run triple* inherited from the repetition layer:

  * `relX`    — `relRepeat (Rel xElem)` (the least-fixpoint relation)
  * `decodeX` — `decodeRepeat xElem xConsumesByte` (the backtracking decoder)
  * `encodeX` — `encodeRepeat xElem` (the partial encoder)
  * `roundtrip` — the inherited `decodeRepeat_spec`/`encodeRepeat_rel` law

The fixed-width bases (2/4/8/10/16) have element `Codec UInt8` (one byte per
element); the cross-byte bit-packing bases (32/64) have element
`Codec (List UInt8)` (a 5-byte / 3-byte block).  No bespoke `encode`/`decode`;
every law is `[propext, Quot.sound]`-only.

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
import BaseN.Bridge

namespace BaseN

/-- The seven bases. -/
inductive Base where
  | B2 | B4 | B8 | B10 | B16 | B32 | B64
  deriving DecidableEq, Repr, Inhabited

/-! ## The uniform facade: one value type `List UInt8`

The four fixed-width bases (2/4/8/10/16) are `Codec UInt8` values decoded by
`Codec.decodeFull` over `Bytes n`; the padded bases (32/64) are the terminal-tail
`B32`/`B64` values (so illegal "data after `=`" is unrepresentable) transported to
`List UInt8` via their bijective byte flatten.  The single facade `encode`/`decode`
dispatches by `cases b`, normalizing everything to the one value type `List UInt8`. -/

open BaseN.Bridge

/-- The uniform total encoder: `List UInt8 → List UInt8`, dispatching by base. -/
def encode (b : Base) (bs : List UInt8) : List UInt8 :=
  match b with
  | Base.B2 => Base2.encodeBit bs |>.map (fun s => bytesToList s.2) |>.getD []
  | Base.B4 => Base4.encodeQuartet bs |>.map (fun s => bytesToList s.2) |>.getD []
  | Base.B8 => Base8.encodeOct bs |>.map (fun s => bytesToList s.2) |>.getD []
  | Base.B10 => Base10.encodeDig bs |>.map (fun s => bytesToList s.2) |>.getD []
  | Base.B16 => Base16.encodeHex bs |>.map (fun s => bytesToList s.2) |>.getD []
  | Base.B32 => Base32.encodeBytes bs
  | Base.B64 => Base64.encodeBytes bs

/-- The uniform partial decoder: `List UInt8 → Option (List UInt8)`, dispatching
by base. -/
def decode (b : Base) (s : List UInt8) : Option (List UInt8) :=
  match b with
  | Base.B2 => Codec.decodeFull Base2.bitElem Base2.bitConsumesByte s.length (listToBytes s)
  | Base.B4 => Codec.decodeFull Base4.quartetElem Base4.quartetConsumesByte s.length (listToBytes s)
  | Base.B8 => Codec.decodeFull Base8.octElem Base8.octConsumesByte s.length (listToBytes s)
  | Base.B10 => Codec.decodeFull Base10.digElem Base10.digConsumesByte s.length (listToBytes s)
  | Base.B16 => Codec.decodeFull Base16.hexElem Base16.hexConsumesByte s.length (listToBytes s)
  | Base.B32 => Base32.decodeBytes s
  | Base.B64 => Base64.decodeBytes s

end BaseN
