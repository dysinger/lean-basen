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

namespace BaseN

/-- The seven bases. -/
inductive Base where
  | B2 | B4 | B8 | B10 | B16 | B32 | B64
  deriving DecidableEq, Repr, Inhabited

end BaseN
