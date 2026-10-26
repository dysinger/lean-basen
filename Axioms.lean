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

/-! ## Totality + spec-form injectivity (task 6.2)

`encode{X}_ne_none` is the encoder totality the spec's `Option`-equality
injectivity law rests on; `encode{X}_injective_eq` is that law itself
(`encode{X} v = encode{X} v' -> v = v'`), together with the totality bounds the
padded bases' proofs go through. All `[propext, Quot.sound]`-only. -/

/-- info: 'BaseN.Base2.encodeBit_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.encodeBit_ne_none

/-- info: 'BaseN.Base2.bitElem_encode_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.bitElem_encode_ne_none

/-- info: 'BaseN.Base2.encodeBit_injective_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.encodeBit_injective_eq

/-- info: 'BaseN.Base4.encodeQuartet_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.encodeQuartet_ne_none

/-- info: 'BaseN.Base4.encodeQuartet_injective_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.encodeQuartet_injective_eq

/-- info: 'BaseN.Base8.encodeOct_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.encodeOct_ne_none

/-- info: 'BaseN.Base8.encodeOct_injective_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.encodeOct_injective_eq

/-- info: 'BaseN.Base10.encodeDig_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.encodeDig_ne_none

/-- info: 'BaseN.Base10.encodeDig_injective_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.encodeDig_injective_eq

/-- info: 'BaseN.Base16.encodeHex_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.encodeHex_ne_none

/-- info: 'BaseN.Base16.encodeHex_injective_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.encodeHex_injective_eq

/-- info: 'BaseN.Base32.b32BlockUnapply_chars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockUnapply_chars

/-- info: 'BaseN.Base32.b32BlockUnapply_len5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockUnapply_len5

/-- info: 'BaseN.Base32.b32TailUnapply_len14' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32TailUnapply_len14

/-- info: 'BaseN.Base32.b32Split_ofBytes_shape_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32Split_ofBytes_shape_bounds

/-- info: 'BaseN.Base32.encodeB32_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.encodeB32_ne_none

/-- info: 'BaseN.Base32.encodeB32_injective_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.encodeB32_injective_eq

/-- info: 'BaseN.Base64.b64BlockUnapply_len3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64BlockUnapply_len3

/-- info: 'BaseN.Base64.b64TailUnapply_len12' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64TailUnapply_len12

/-- info: 'BaseN.Base64.b64Split_ofBytes_shape_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64Split_ofBytes_shape_bounds

/-- info: 'BaseN.Base64.encodeB64_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.encodeB64_ne_none

/-- info: 'BaseN.Base64.encodeB64_injective_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.encodeB64_injective_eq

/-- info: 'BaseN.Common.count_satisfy_encode_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.count_satisfy_encode_ne_none

/-! ## Unique canonical inverse (task 6.3)

`decodeFullB{64,32}_char` states the "decode is the unique canonical inverse"
requirement as one proposition: `decode s = some v ↔ ∃ v', encode v' = some ⟨n,s⟩
∧ v = v'`. Pure assembly over `decodeFullB*_conv` (→) and `decodeFullB*_roundtrip`
(←). `[propext, Quot.sound]`-only. -/

/-- info: 'BaseN.Base64.decodeFullB64_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_char

/-- info: 'BaseN.Base32.decodeFullB32_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_char

/-! ## Total characterization — the in-image converse for all seven bases (task 7.1)

Task 6.3 gave the iff for the two padded bases. Task 7.1 promotes it to all
seven: each fixed-width base's `decodeFull_B{x}_char` is the same proposition
assembled over its already-proved `decode_encode_inverse` (→) and `roundtrip`
(←). `[propext, Quot.sound]`-only. -/

/-- info: 'BaseN.Base2.decodeFull_B2_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.decodeFull_B2_char

/-- info: 'BaseN.Base4.decodeFull_B4_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.decodeFull_B4_char

/-- info: 'BaseN.Base8.decodeFull_B8_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.decodeFull_B8_char

/-- info: 'BaseN.Base10.decodeFull_B10_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.decodeFull_B10_char

/-- info: 'BaseN.Base16.decodeFull_B16_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.decodeFull_B16_char

/-! ## General rejection laws (task 6.4)

Task 6.4 replaced the finite rejection vector set with the *general* law for both
padded bases: an invalid alphabet byte at **any** index, a `=` at code-word slot
0 or 1 (i.e. non-terminal padding, the `Zg==Zg==` / `MY======MY======` class), and
a byte count not divisible by the code-word width. Plus the supporting lemmas
(`*_consumed_alphabet`, `Rel_b*TailElem_pad_pos`, `decodeFullB64_block_region`)
and the arity identity `decodeFullB*_arity`. All `[propext, Quot.sound]`-only. -/

/-- info: 'BaseN.Base64.decodeFullB64_consumed_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_consumed_alphabet

/-- info: 'BaseN.Base64.decodeFullB64_reject_invalid_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_reject_invalid_at

/-- info: 'BaseN.Base64.Rel_b64TailElem_pad_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.Rel_b64TailElem_pad_pos

/-- info: 'BaseN.Base64.decodeFullB64_block_region' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_block_region

/-- info: 'BaseN.Base64.decodeFullB64_reject_pad_at_low_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_reject_pad_at_low_slot

/-- info: 'BaseN.Base64.decodeFullB64_arity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_arity

/-- info: 'BaseN.Base64.decodeFullB64_reject_arity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_reject_arity

/-- info: 'BaseN.Base32.decodeFullB32_consumed_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_consumed_alphabet

/-- info: 'BaseN.Base32.decodeFullB32_reject_invalid_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_reject_invalid_at

/-- info: 'BaseN.Base32.Rel_b32TailElem_pad_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.Rel_b32TailElem_pad_pos

/-- info: 'BaseN.Base32.decodeFullB32_reject_pad_at_low_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_reject_pad_at_low_slot

/-- info: 'BaseN.Base32.decodeFullB32_arity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_arity

/-- info: 'BaseN.Base32.decodeFullB32_reject_arity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_reject_arity
