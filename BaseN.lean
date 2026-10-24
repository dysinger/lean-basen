/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# BaseN

The base-`N` encoding/decoding package: one verified package covering base 2, 4,
8, 10, 16, 32, and 64, each re-expressed as a `codec` `Codec` value over the
`satisfy`/`count`/`iso` primitives plus the productive repetition layer —
decoded and encoded by the single `Codec.decode`/`Codec.encode` operations,
"only the codec changes."

Each base is a `Codec` value (fixed-width `Codec UInt8`, padded a full-block
`Run` + terminal-tail composition `iso`-ed to `B32`/`B64`), decoded/encoded by the
*uniform* `Codec` operations:

  * `Codec.decodeFull hexElem hexConsumesByte n s` / `encodeHex bs`
  * `decodeFullB64 s` / `encodeB64 bs` / `decodeFullB32 s` / `encodeB32 bs`

There is **no** `Base` enum and **no** `encode (b : Base)` / `decode (b : Base)`
facade: the radix lives in the value the caller already holds, never on a
dispatch index.  The value type is `List UInt8` (the whole byte list); `B32`/`B64`
is the canonical block/tail spine used only to specify the full-block +
terminal-tail split, and rejection is a `decodeFullB64`/`decodeFullB32 = none`
inequation over the composition.

  * `BaseN.Base2`  — one bit per `0`/`1` char, 8 chars per byte, MSB-first
  * `BaseN.Base4`  — one quartet per `0`-`3` char, 4 chars per byte
  * `BaseN.Base8`  — octal, 3 digits per byte (RFC-adjacent, no padding)
  * `BaseN.Base10` — decimal digit math, byte-oriented, no sign
  * `BaseN.Base16` — hex, `0-9A-F`, uppercase, no padding (RFC 4648 §8)
  * `BaseN.Base32` — `A-Z2-7`, `=` padding (RFC 4648 §6)
  * `BaseN.Base64` — `A-Za-z0-9+/`, `=` padding (RFC 4648 §4)

Every law is `[propext, Quot.sound]`-only.  There is no `BaseN.Bridge`, no
strict per-format parser triple, and no bespoke per-base facade.
-/

import BaseN.Base2
import BaseN.Base4
import BaseN.Base8
import BaseN.Base10
import BaseN.Base16
import BaseN.Base32
import BaseN.Base64
