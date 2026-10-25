/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import BaseN
import Codec

/-!
# Axiom gate (`lake build`-enforced)

Every public law of this package must be provable from Lean's kernel plus
**only** `propext` and `Quot.sound` — never `Classical.choice`, never `sorryAx`,
never `native_decide`.  That discipline is a standing invariant of the whole
`codec` ecosystem, and it has already been violated once by accident (a
`Classical.choice` leak through `omega`/`simp` on a list-length contradiction —
see the task ledger's 4.3 note).

This file turns that invariant into a **build failure**: each `#guard_msgs`
below pins the *exact* diagnostic text of `#print axioms`, so any axiom that
appears or disappears changes the message and trips the guard.

A `Classical.choice` regression therefore cannot land silently.  If you add a
law, add it here too — an un-gated law is not protected.

Two laws are even cleaner than required and are pinned as such:
`BaseN.Base64.b64Split_blocks_tail` / `BaseN.Base32.b32Split_blocks_tail`
depend on `[propext]` alone.
-/

/-- info: 'Codec.roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.roundtrip

/-- info: 'Codec.bidir' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.bidir

/-- info: 'Codec.decode_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decode_spec

/-- info: 'BaseN.Base10.decode_encode_inverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.decode_encode_inverse

/-- info: 'BaseN.Base10.encode_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.encode_injective

/-- info: 'BaseN.Base10.roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.roundtrip

/-- info: 'BaseN.Base16.decode_encode_inverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.decode_encode_inverse

/-- info: 'BaseN.Base16.encode_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.encode_injective

/-- info: 'BaseN.Base16.roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.roundtrip

/-- info: 'BaseN.Base2.decode_encode_inverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.decode_encode_inverse

/-- info: 'BaseN.Base2.encodeBit_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.encodeBit_canonical

/-- info: 'BaseN.Base2.encode_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.encode_injective

/-- info: 'BaseN.Base2.roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.roundtrip

/-- info: 'BaseN.Base32.decodeFullB32_conv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_conv

/-- info: 'BaseN.Base32.decodeFullB32_reject_MYAAAA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_reject_MYAAAA

/-- info: 'BaseN.Base32.decodeFullB32_reject_bad_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_reject_bad_length

/-- info: 'BaseN.Base32.decodeFullB32_reject_first_invalid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_reject_first_invalid

/-- info: 'BaseN.Base32.decodeFullB32_reject_invalid_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_reject_invalid_char

/-- info: 'BaseN.Base32.decodeFullB32_reject_pad_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_reject_pad_first

/-- info: 'BaseN.Base32.decodeFullB32_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_roundtrip

/-- info: 'BaseN.Base32.encodeB32_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.encodeB32_canonical

/-- info: 'BaseN.Base32.encodeB32_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.encodeB32_injective

/-- info: 'BaseN.Base4.decode_encode_inverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.decode_encode_inverse

/-- info: 'BaseN.Base4.encode_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.encode_injective

/-- info: 'BaseN.Base4.roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.roundtrip

/-- info: 'BaseN.Base64.decodeFullB64_conv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_conv

/-- info: 'BaseN.Base64.decodeFullB64_reject_ZgAAAA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_reject_ZgAAAA

/-- info: 'BaseN.Base64.decodeFullB64_reject_bad_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_reject_bad_length

/-- info: 'BaseN.Base64.decodeFullB64_reject_first_invalid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_reject_first_invalid

/-- info: 'BaseN.Base64.decodeFullB64_reject_invalid_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_reject_invalid_char

/-- info: 'BaseN.Base64.decodeFullB64_reject_pad_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_reject_pad_first

/-- info: 'BaseN.Base64.decodeFullB64_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_roundtrip

/-- info: 'BaseN.Base64.encodeB64_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.encodeB64_canonical

/-- info: 'BaseN.Base64.encodeB64_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.encodeB64_injective

/-- info: 'BaseN.Base8.decode_encode_inverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.decode_encode_inverse

/-- info: 'BaseN.Base8.encode_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.encode_injective

/-- info: 'BaseN.Base8.roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.roundtrip

