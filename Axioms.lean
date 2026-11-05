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

**Coverage is complete as of `codec-audit-round-two` §4:** all **440** public
`theorem`s of
`Base2`/`Base4`/`Base8`/`Base10`/`Base16`/`Base32`/`Base64`/`Common` are pinned
by a `#guard_msgs` below, so there is no un-gated law left.  (The audit that
prompted this found 91 of 404, i.e. 22.5% — the gap was real and took two
sessions to close.)  The distribution is 377 `[propext, Quot.sound]`, **48
`[propext]`-only**, and **15 axiom-free**; `Classical.choice` appears nowhere.

The 22 theorems added by §4 are the base32 §3.5 family: the 2/3/4-byte pad-bit
lemmas, their block-level rejections, and the three whole-input rejections plus
the general `decodeFullB32_reject_of_pad_and_tail` they are instances of.  **Gate
coverage is not §3.5 coverage** — the gate says a law's *logic* is clean; that the
*behaviour* is canonical is what §4's theorems now pin, and before §4 three of the
four non-canonical tail shapes had neither.

Adding a law therefore means adding its gate: the count above is checkable with
`grep -c '^#print axioms' Axioms.lean` against a `grep` of the modules'
`^theorem` lines, and a mismatch means a law landed un-gated. -/

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

/-! ## Total characterization **through the canonical type** (task 7.2)

`B64`/`B32` are the canonical block/tail spines — full blocks, then at most one
**terminal** tail, with no constructor continuing after a tail. That terminality
is the type-level content of "cannot represent trailing data".

An earlier revision withdrew the claim, saying the property is established "by
the rejection inequation, not by the type". That undersold the type: the decoder's
image is *provably* the image of `encode ∘ b*BytesOf`, so the type and the
inequation agree. `decode{B}*_char_via_type` states that agreement and
`decode{B}*_spine` records that every decoded value is a canonical flattening.

`b*BytesOf_tail1_eq` is `rfl`-true and depends on **no** axioms — the terminality
is definitional, not inherent.
-/

/-- info: 'BaseN.Base64.decodeFullB64_char_via_type' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_char_via_type

/-- info: 'BaseN.Base64.decodeFullB64_spine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_spine

/-- info: 'BaseN.Base32.decodeFullB32_char_via_type' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_char_via_type

/-- info: 'BaseN.Base32.decodeFullB32_spine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_spine

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

/-! ## RFC 4648 §8 — Base16 case-insensitivity (task 7.3)

The information-free variation is a length-preserving ASCII case fold over the
concrete syntax (`foldByte`/`foldList`), folded **up** so the canonical uppercase
encoding is a fixed point. The quotient lives in the **object**
(`Normal (List UInt8) foldList`), so the block `Iso` stays an ordinary `Iso` and
`Iso.law` is untouched. These four gates pin: the fold's idempotence, the
`Iso` law, the acceptance-preservation lemma the law needs, and the both-cases
decode law. -/

/-- info: 'BaseN.Base16.foldByte_idem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.foldByte_idem

/-- info: 'BaseN.Base16.foldList_idem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.foldList_idem

/-- info: 'BaseN.Base16.hexBlockIsoF_law' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexBlockIsoF_law

/-- info: 'BaseN.Base16.hexBlockApply_foldList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexBlockApply_foldList

/-- info: 'BaseN.Base16.decodeHexFold_lowercase_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.decodeHexFold_lowercase_eq

/-- info: 'BaseN.Base16.decodeHexFold_of_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.decodeHexFold_of_fixed

/-! ## Split-reassembly laws (pre-archive audit §6.6)

`b64Split_shape` / `b32Split_shape` state that splitting a byte list into full
blocks plus a terminal tail reassembles it. An audit found them referenced only
by their own declarations — dead by accident (nothing yet consumes them), not by
design. They are the natural load-bearing laws for any future split-level
argument, so they are gated here rather than deleted: gating is what makes them
count, and deleting a true theorem to satisfy a lint is the worse trade. -/

/-- info: 'BaseN.Base64.b64Split_shape' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base64.b64Split_shape

/-- info: 'BaseN.Base32.b32Split_shape' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base32.b32Split_shape

/-- info: 'BaseN.Base64.b64BlockUnapply_one' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base64.b64BlockUnapply_one

/-- info: 'BaseN.Base64.b64BlockUnapply_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base64.b64BlockUnapply_two

/-! ## RFC 4648 §3.5 non-canonical pad bits, at the block level (§6.2)

`b64BlockApply_b64Zh_chars` is the §3.5 check stated where the RFC puts it: on
the block decoder, whose whole definition is the re-encode equality. It is the
step that makes `Zh==` unrepresentable. `b64TailApply_b64Zh_chars` lifts it to
the tail element, and `not_rel_b64TailElem_of_apply_none` is the bridge from a
block-level `none` to the tail element's relation. -/

/-- info: 'BaseN.Base64.b64BlockApply_b64Zh_chars' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base64.b64BlockApply_b64Zh_chars

/-- info: 'BaseN.Base64.b64TailApply_b64Zh_chars' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base64.b64TailApply_b64Zh_chars

/-- info: 'BaseN.Base64.not_rel_b64TailElem_of_apply_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.not_rel_b64TailElem_of_apply_none

/-! ## RFC 4648 §3.5 non-canonical pad bits, the `MZ======` vector (§6.3b)

The base32 twin of the block above. `b32BlockApply_b32Mz_chars` rejects the
`MZ======` character block at the re-encode guard (`MZ` lenient-decodes to
`0x66`, whose canonical encoding is `MY======`), `b32TailApply_b32Mz_chars`
lifts that to the tail element, and `not_rel_b32TailElem_of_apply_none` is the
block-to-relation bridge. `decodeFullB32_reject_MZ` is the whole-input theorem:
the thing commit `3dfc249` claimed in a message with no theorem behind it. -/

/-- info: 'BaseN.Base32.b32BlockApply_b32Mz_chars' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockApply_b32Mz_chars

/-- info: 'BaseN.Base32.b32TailApply_b32Mz_chars' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base32.b32TailApply_b32Mz_chars

/-- info: 'BaseN.Base32.not_rel_b32TailElem_of_apply_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.not_rel_b32TailElem_of_apply_none

/-- info: 'BaseN.Base32.decodeFullB32_reject_MZ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_reject_MZ

/-! ## RFC 4648 §3.5 non-canonical pad bits, whole-input (§6.2)

The base64 half of the same family.  The block-level halves and the
block-to-relation bridge are gated above; these are the **whole-input lifts** —
that `decodeFullB64` itself says `none` for the two non-canonical pad-bit
vectors, which is what commit `9d5074e` claimed in a message while `b64Zh` and
`b64Zm9` were orphaned definitions with no theorem behind them (ledger §6.2 /
§6.3a). -/

/-- info: 'BaseN.Base64.b64Zm9_chars' does not depend on any axioms -/
#guard_msgs in
#print axioms BaseN.Base64.b64Zm9_chars

/-- info: 'BaseN.Base64.b64BlockApply_b64Zm9_chars' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base64.b64BlockApply_b64Zm9_chars

/-- info: 'BaseN.Base64.b64TailApply_b64Zm9_chars' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base64.b64TailApply_b64Zm9_chars

/-- info: 'BaseN.Base64.decodeFullB64_reject_b64Zh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_reject_b64Zh

/-- info: 'BaseN.Base64.decodeFullB64_reject_b64Zm9' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_reject_b64Zm9

/-! ## Complete coverage: every remaining public law (ledger §6.4)

The audit found this gate covered 91 of 404 theorems (22.5%), and the file's own
docstring says "an un-gated law is not protected" — so by its own standard 77.5%
were unprotected.  The blocks below close that gap: **every** public `theorem`
in every `BaseN` module is now pinned.

This was verified to be a *pure gating* task before writing any of it: all 315
trees were `#print axioms`'d in one probe first, and all came back clean —
272 `[propext, Quot.sound]`, 32 `[propext]`, 11 axiom-free, **zero**
`Classical.choice` and zero `sorryAx`.  So no proof needed repair; the gap was
coverage, not discipline.  That distinction is worth stating because it is the
opposite of what the same probe would have shown if a leak had landed un-gated —
which is exactly the failure mode this block exists to make impossible. -/

/- Every `Common` law not gated above (ledger §6.4 complete coverage). -/
/-- info: 'BaseN.Common.Productive_iso' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Common.Productive_iso
/-- info: 'BaseN.Common.Productive_seq_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.Productive_seq_left
/-- info: 'BaseN.Common.Productive_count_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.Productive_count_succ
/-- info: 'BaseN.Common.Productive_satisfy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.Productive_satisfy
/-- info: 'BaseN.Common.Productive_count_satisfy_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.Productive_count_satisfy_succ
/-- info: 'BaseN.Common.Unambiguous_satisfy' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Common.Unambiguous_satisfy
/-- info: 'BaseN.Common.Functional_satisfy' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Common.Functional_satisfy
/-- info: 'BaseN.Common.Functional_count_satisfy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.Functional_count_satisfy
/-- info: 'BaseN.Common.Functional_iso' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Common.Functional_iso
/-- info: 'BaseN.Common.Rel_count_satisfy_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.Rel_count_satisfy_len
/-- info: 'BaseN.Common.Rel_count_satisfy_forall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.Rel_count_satisfy_forall
/-- info: 'BaseN.Common.Rel_count_satisfy_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Common.Rel_count_satisfy_length
/-- info: 'BaseN.Common.Rel_count_satisfy_ofFn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.Rel_count_satisfy_ofFn
/-- info: 'BaseN.Common.relRepeat_forall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.relRepeat_forall
/-- info: 'BaseN.Common.relRepeat_functional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.relRepeat_functional
/-- info: 'BaseN.Common.encodeRepeat_of_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.encodeRepeat_of_rel
/-- info: 'BaseN.Common.count_satisfy_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.count_satisfy_unambiguous
/-- info: 'BaseN.Common.Unambiguous_iso' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Common.Unambiguous_iso
/-- info: 'BaseN.Common.consumesByte_count_satisfy_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.consumesByte_count_satisfy_succ
/-- info: 'BaseN.Common.bdrop_concat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.bdrop_concat
/-- info: 'BaseN.Common.concat_eq_drop_prepend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.concat_eq_drop_prepend
/-- info: 'BaseN.Common.decodeRepeat_prefix_concat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.decodeRepeat_prefix_concat
/-- info: 'BaseN.Common.head?_eq_some_of_mem_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Common.head?_eq_some_of_mem_eq
/-- info: 'BaseN.Common.nat_lt_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.nat_lt_four
/-- info: 'BaseN.Common.decodeRepeat_nil_mem_eq_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Common.decodeRepeat_nil_mem_eq_id
/-- info: 'BaseN.Common.relRepeat_block_len' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Common.relRepeat_block_len
/-- info: 'BaseN.Common.encode_satisfy_ne_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Common.encode_satisfy_ne_none
/-- info: 'BaseN.Common.encode_seq_ne_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Common.encode_seq_ne_none

/- Every `Base2` law not gated above (ledger §6.4 complete coverage). -/
/-- info: 'BaseN.Base2.bitVal_valToBit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.bitVal_valToBit
/-- info: 'BaseN.Base2.valToBit_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.valToBit_valid
/-- info: 'BaseN.Base2.valToBit_lt_256' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base2.valToBit_lt_256
/-- info: 'BaseN.Base2.bitValid_of_decide' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base2.bitValid_of_decide
/-- info: 'BaseN.Base2.valToBit_bitVal_of_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.valToBit_bitVal_of_valid
/-- info: 'BaseN.Base2.bitAt_le_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.bitAt_le_one
/-- info: 'BaseN.Base2.bitsVal_bitsOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.bitsVal_bitsOf
/-- info: 'BaseN.Base2.bits_decompose_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.bits_decompose_unique
/-- info: 'BaseN.Base2.bitVal_toByte_valToBit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.bitVal_toByte_valToBit
/-- info: 'BaseN.Base2.bitDigit_valid_of_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.bitDigit_valid_of_byte
/-- info: 'BaseN.Base2.bitBlockApply_unapply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.bitBlockApply_unapply
/-- info: 'BaseN.Base2.bitBlockIso_law' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.bitBlockIso_law
/-- info: 'BaseN.Base2.bitConsumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.bitConsumesByte
/-- info: 'BaseN.Base2.bitElem_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.bitElem_unambiguous
/-- info: 'BaseN.Base2.Rel_bitElem_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.Rel_bitElem_len
/-- info: 'BaseN.Base2.relBit_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.relBit_unambiguous
/-- info: 'BaseN.Base2.bitDecodeFull_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.bitDecodeFull_unambiguous
/-- info: 'BaseN.Base2.bitElem_functional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.bitElem_functional
/-- info: 'BaseN.Base2.Rel_bitElem_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.Rel_bitElem_canonical
/-- info: 'BaseN.Base2.bitBlockUnapply_digits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.bitBlockUnapply_digits
/-- info: 'BaseN.Base2.decodeFull_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.decodeFull_canonical
/-- info: 'BaseN.Base2.rejects_invalid_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.rejects_invalid_byte
/-- info: 'BaseN.Base2.rejects_bad_arity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.rejects_bad_arity

/- Every `Base4` law not gated above (ledger §6.4 complete coverage). -/
/-- info: 'BaseN.Base4.quartetVal_valToQuartet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.quartetVal_valToQuartet
/-- info: 'BaseN.Base4.valToQuartet_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.valToQuartet_valid
/-- info: 'BaseN.Base4.valToQuartet_lt_256' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.valToQuartet_lt_256
/-- info: 'BaseN.Base4.quartetValid_of_decide' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base4.quartetValid_of_decide
/-- info: 'BaseN.Base4.valToQuartet_quartetVal_of_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.valToQuartet_quartetVal_of_valid
/-- info: 'BaseN.Base4.quartetAt_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.quartetAt_le
/-- info: 'BaseN.Base4.quartetsVal_quartetsOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.quartetsVal_quartetsOf
/-- info: 'BaseN.Base4.quartets_decompose_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.quartets_decompose_unique
/-- info: 'BaseN.Base4.quartetVal_toByte_valToQuartet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.quartetVal_toByte_valToQuartet
/-- info: 'BaseN.Base4.quartetDigit_valid_of_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.quartetDigit_valid_of_byte
/-- info: 'BaseN.Base4.quartetBlockApply_unapply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.quartetBlockApply_unapply
/-- info: 'BaseN.Base4.quartetBlockIso_law' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.quartetBlockIso_law
/-- info: 'BaseN.Base4.quartetConsumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.quartetConsumesByte
/-- info: 'BaseN.Base4.quartetElem_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.quartetElem_unambiguous
/-- info: 'BaseN.Base4.Rel_quartetElem_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.Rel_quartetElem_len
/-- info: 'BaseN.Base4.relQuartet_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.relQuartet_unambiguous
/-- info: 'BaseN.Base4.quartetDecodeFull_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.quartetDecodeFull_unambiguous
/-- info: 'BaseN.Base4.quartetElem_functional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.quartetElem_functional
/-- info: 'BaseN.Base4.Rel_quartetElem_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.Rel_quartetElem_canonical
/-- info: 'BaseN.Base4.encodeQuartet_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.encodeQuartet_canonical
/-- info: 'BaseN.Base4.quartetBlockUnapply_digits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.quartetBlockUnapply_digits
/-- info: 'BaseN.Base4.quartetElem_encode_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.quartetElem_encode_ne_none
/-- info: 'BaseN.Base4.decodeFull_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.decodeFull_canonical
/-- info: 'BaseN.Base4.rejects_invalid_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.rejects_invalid_byte
/-- info: 'BaseN.Base4.rejects_bad_arity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.rejects_bad_arity

/- Every `Base8` law not gated above (ledger §6.4 complete coverage). -/
/-- info: 'BaseN.Base8.octToVal_valToOct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.octToVal_valToOct
/-- info: 'BaseN.Base8.valToOct_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.valToOct_valid
/-- info: 'BaseN.Base8.valToOct_lt_256' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.valToOct_lt_256
/-- info: 'BaseN.Base8.octValid_of_decide' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base8.octValid_of_decide
/-- info: 'BaseN.Base8.valToOct_octToVal_of_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.valToOct_octToVal_of_valid
/-- info: 'BaseN.Base8.oct_sum_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.oct_sum_eq
/-- info: 'BaseN.Base8.oct_decompose_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.oct_decompose_unique
/-- info: 'BaseN.Base8.octDigit_valid_of_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.octDigit_valid_of_byte
/-- info: 'BaseN.Base8.octToVal_ofNat_valToOct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.octToVal_ofNat_valToOct
/-- info: 'BaseN.Base8.octBlockApply_unapply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.octBlockApply_unapply
/-- info: 'BaseN.Base8.octBlockIso_law' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.octBlockIso_law
/-- info: 'BaseN.Base8.octConsumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.octConsumesByte
/-- info: 'BaseN.Base8.octElem_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.octElem_unambiguous
/-- info: 'BaseN.Base8.Rel_octElem_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.Rel_octElem_len
/-- info: 'BaseN.Base8.relOct_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.relOct_unambiguous
/-- info: 'BaseN.Base8.octDecodeFull_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.octDecodeFull_unambiguous
/-- info: 'BaseN.Base8.octElem_functional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.octElem_functional
/-- info: 'BaseN.Base8.Rel_octElem_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.Rel_octElem_canonical
/-- info: 'BaseN.Base8.encodeOct_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.encodeOct_canonical
/-- info: 'BaseN.Base8.octBlockUnapply_digits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.octBlockUnapply_digits
/-- info: 'BaseN.Base8.octElem_encode_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.octElem_encode_ne_none
/-- info: 'BaseN.Base8.decodeFull_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.decodeFull_canonical
/-- info: 'BaseN.Base8.rejects_invalid_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.rejects_invalid_byte
/-- info: 'BaseN.Base8.rejects_bad_arity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.rejects_bad_arity
/-- info: 'BaseN.Base8.rejects_overflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.rejects_overflow

/- Every `Base10` law not gated above (ledger §6.4 complete coverage). -/
/-- info: 'BaseN.Base10.digVal_valToDig' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.digVal_valToDig
/-- info: 'BaseN.Base10.valToDig_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.valToDig_valid
/-- info: 'BaseN.Base10.valToDig_lt_256' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.valToDig_lt_256
/-- info: 'BaseN.Base10.digValid_of_decide' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base10.digValid_of_decide
/-- info: 'BaseN.Base10.valToDig_digVal_of_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.valToDig_digVal_of_valid
/-- info: 'BaseN.Base10.dig_sum_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.dig_sum_eq
/-- info: 'BaseN.Base10.dig_decompose_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.dig_decompose_unique
/-- info: 'BaseN.Base10.digDigit_valid_of_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.digDigit_valid_of_byte
/-- info: 'BaseN.Base10.digVal_toByte_valToDig' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.digVal_toByte_valToDig
/-- info: 'BaseN.Base10.digBlockApply_unapply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.digBlockApply_unapply
/-- info: 'BaseN.Base10.digBlockIso_law' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.digBlockIso_law
/-- info: 'BaseN.Base10.digConsumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.digConsumesByte
/-- info: 'BaseN.Base10.digElem_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.digElem_unambiguous
/-- info: 'BaseN.Base10.Rel_digElem_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.Rel_digElem_len
/-- info: 'BaseN.Base10.relDig_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.relDig_unambiguous
/-- info: 'BaseN.Base10.digDecodeFull_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.digDecodeFull_unambiguous
/-- info: 'BaseN.Base10.digElem_functional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.digElem_functional
/-- info: 'BaseN.Base10.Rel_digElem_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.Rel_digElem_canonical
/-- info: 'BaseN.Base10.encodeDig_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.encodeDig_canonical
/-- info: 'BaseN.Base10.digBlockUnapply_digits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.digBlockUnapply_digits
/-- info: 'BaseN.Base10.digElem_encode_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.digElem_encode_ne_none
/-- info: 'BaseN.Base10.decodeFull_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.decodeFull_canonical
/-- info: 'BaseN.Base10.rejects_invalid_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.rejects_invalid_byte
/-- info: 'BaseN.Base10.rejects_bad_arity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.rejects_bad_arity
/-- info: 'BaseN.Base10.rejects_overflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.rejects_overflow

/- Every `Base16` law not gated above (ledger §6.4 complete coverage). -/
/-- info: 'BaseN.Base16.hexToNibble_digit' does not depend on any axioms -/
#guard_msgs in
#print axioms BaseN.Base16.hexToNibble_digit
/-- info: 'BaseN.Base16.hexToNibble_upper' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexToNibble_upper
/-- info: 'BaseN.Base16.hexToNibble_nibbleToHex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexToNibble_nibbleToHex
/-- info: 'BaseN.Base16.nibbleToHex_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.nibbleToHex_valid
/-- info: 'BaseN.Base16.nibbleToHex_lt_256' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.nibbleToHex_lt_256
/-- info: 'BaseN.Base16.hexNibbleValid_of_decide' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base16.hexNibbleValid_of_decide
/-- info: 'BaseN.Base16.nibbleToHex_hexToNibble_of_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.nibbleToHex_hexToNibble_of_valid
/-- info: 'BaseN.Base16.hexToNibble_toByte_nibbleToHex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexToNibble_toByte_nibbleToHex
/-- info: 'BaseN.Base16.hexDigit_valid_of_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexDigit_valid_of_byte
/-- info: 'BaseN.Base16.hexBlockApply_unapply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexBlockApply_unapply
/-- info: 'BaseN.Base16.hex_decompose_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hex_decompose_unique
/-- info: 'BaseN.Base16.hexBlockIso_law' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexBlockIso_law
/-- info: 'BaseN.Base16.hexConsumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexConsumesByte
/-- info: 'BaseN.Base16.hexElem_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexElem_unambiguous
/-- info: 'BaseN.Base16.Rel_hexElem_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.Rel_hexElem_len
/-- info: 'BaseN.Base16.relHex_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.relHex_unambiguous
/-- info: 'BaseN.Base16.hexDecodeFull_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexDecodeFull_unambiguous
/-- info: 'BaseN.Base16.hexElem_functional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexElem_functional
/-- info: 'BaseN.Base16.Rel_hexElem_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.Rel_hexElem_canonical
/-- info: 'BaseN.Base16.encodeHex_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.encodeHex_canonical
/-- info: 'BaseN.Base16.hexBlockUnapply_digits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexBlockUnapply_digits
/-- info: 'BaseN.Base16.hexElem_encode_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexElem_encode_ne_none
/-- info: 'BaseN.Base16.decodeFull_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.decodeFull_canonical
/-- info: 'BaseN.Base16.rejects_invalid_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.rejects_invalid_byte
/-- info: 'BaseN.Base16.rejects_lowercase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.rejects_lowercase
/-- info: 'BaseN.Base16.rejects_odd_arity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.rejects_odd_arity
/-- info: 'BaseN.Base16.foldByte_fixed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base16.foldByte_fixed
/-- info: 'BaseN.Base16.foldByte_folded' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base16.foldByte_folded
/-- info: 'BaseN.Base16.ofNat_sub32_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.ofNat_sub32_toNat
/-- info: 'BaseN.Base16.foldList_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms BaseN.Base16.foldList_nil
/-- info: 'BaseN.Base16.foldList_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms BaseN.Base16.foldList_cons
/-- info: 'BaseN.Base16.foldNormalizer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.foldNormalizer
/-- info: 'BaseN.Base16.hexToNibble_lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexToNibble_lower
/-- info: 'BaseN.Base16.hexNibbleValid_false_of_lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexNibbleValid_false_of_lower
/-- info: 'BaseN.Base16.hexNibbleValid_foldByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexNibbleValid_foldByte
/-- info: 'BaseN.Base16.hexToNibble_foldByte_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexToNibble_foldByte_true
/-- info: 'BaseN.Base16.hexToNibble_foldByte_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexToNibble_foldByte_false
/-- info: 'BaseN.Base16.hexToNibble_foldByte_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexToNibble_foldByte_value
/-- info: 'BaseN.Base16.hexBlockApply_none_of_not_len2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base16.hexBlockApply_none_of_not_len2
/-- info: 'BaseN.Base16.hexBlockApply_foldList_ne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base16.hexBlockApply_foldList_ne
/-- info: 'BaseN.Base16.fill_foldList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.fill_foldList
/-- info: 'BaseN.Base16.decodeHexBlockFold_both_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.decodeHexBlockFold_both_cases
/-- info: 'BaseN.Base16.foldList_hexBlockUnapply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.foldList_hexBlockUnapply
/-- info: 'BaseN.Base16.hexNibbleValid_of_hexFixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexNibbleValid_of_hexFixed
/-- info: 'BaseN.Base16.hexFixed_of_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.hexFixed_of_valid
/-- info: 'BaseN.Base16.decodeHexBlockFold_case_insensitive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.decodeHexBlockFold_case_insensitive
/-- info: 'BaseN.Base16.foldByteBytes_idem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.foldByteBytes_idem
/-- info: 'BaseN.Base16.decodeHexFold_both_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.decodeHexFold_both_cases

/- Every `Base32` law not gated above (ledger §6.4 complete coverage). -/
/-- info: 'BaseN.Base32.b32ToVal_valToB32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32ToVal_valToB32
/-- info: 'BaseN.Base32.valToB32_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.valToB32_valid
/-- info: 'BaseN.Base32.valToB32_not_pad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.valToB32_not_pad
/-- info: 'BaseN.Base32.valToB32_lt_256' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.valToB32_lt_256
/-- info: 'BaseN.Base32.byte0Of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.byte0Of
/-- info: 'BaseN.Base32.byte1Of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.byte1Of
/-- info: 'BaseN.Base32.byte2Of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.byte2Of
/-- info: 'BaseN.Base32.byte3Of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.byte3Of
/-- info: 'BaseN.Base32.byte4Of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.byte4Of
/-- info: 'BaseN.Base32.b32Valid_of_decide' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base32.b32Valid_of_decide
/-- info: 'BaseN.Base32.valToB32_b32ToVal_of_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.valToB32_b32ToVal_of_valid
/-- info: 'BaseN.Base32.b32OrPad_of_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base32.b32OrPad_of_valid
/-- info: 'BaseN.Base32.b32OrPad_pad' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base32.b32OrPad_pad
/-- info: 'BaseN.Base32.b32OrPad_toByte_valToB32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32OrPad_toByte_valToB32
/-- info: 'BaseN.Base32.b32BlockUnapply_total' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockUnapply_total
/-- info: 'BaseN.Base32.b32BlockUnapply_len8' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockUnapply_len8
/-- info: 'BaseN.Base32.b32BlockDecodeLenient_unapply_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockDecodeLenient_unapply_single
/-- info: 'BaseN.Base32.b32BlockDecodeLenient_unapply_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockDecodeLenient_unapply_pair
/-- info: 'BaseN.Base32.b32BlockDecodeLenient_unapply_triple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockDecodeLenient_unapply_triple
/-- info: 'BaseN.Base32.b32BlockDecodeLenient_unapply_quad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockDecodeLenient_unapply_quad
/-- info: 'BaseN.Base32.b32BlockDecodeLenient_unapply_quintet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockDecodeLenient_unapply_quintet
/-- info: 'BaseN.Base32.b32BlockIso_law' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockIso_law
/-- info: 'BaseN.Base32.b32BytesOf_ofBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BytesOf_ofBytes
/-- info: 'BaseN.Base32.b32OfBytes_bytesOf' does not depend on any axioms -/
#guard_msgs in
#print axioms BaseN.Base32.b32OfBytes_bytesOf
/-- info: 'BaseN.Base32.b32BlockConsumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockConsumesByte
/-- info: 'BaseN.Base32.b32BlockElem_functional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockElem_functional
/-- info: 'BaseN.Base32.Rel_b32BlockElem_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.Rel_b32BlockElem_canonical
/-- info: 'BaseN.Base32.b32BlockElem_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockElem_unambiguous
/-- info: 'BaseN.Base32.Rel_b32BlockElem_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.Rel_b32BlockElem_len
/-- info: 'BaseN.Base32.relB32Block_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.relB32Block_unambiguous
/-- info: 'BaseN.Base32.b32BlockDecodeFull_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockDecodeFull_unambiguous
/-- info: 'BaseN.Base32.b32BlockElem_encode_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockElem_encode_ne_none
/-- info: 'BaseN.Base32.b32TailIso_law' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32TailIso_law
/-- info: 'BaseN.Base32.b32TailElem_encode_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32TailElem_encode_ne_none
/-- info: 'BaseN.Base32.b32TailConsumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32TailConsumesByte
/-- info: 'BaseN.Base32.b32TailElem_functional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32TailElem_functional
/-- info: 'BaseN.Base32.b32TailElem_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32TailElem_unambiguous
/-- info: 'BaseN.Base32.Rel_b32TailElem_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.Rel_b32TailElem_len
/-- info: 'BaseN.Base32.relB32Tail_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.relB32Tail_unambiguous
/-- info: 'BaseN.Base32.b32Mz_chars' does not depend on any axioms -/
#guard_msgs in
#print axioms BaseN.Base32.b32Mz_chars
/-- info: 'BaseN.Base32.b32TailDecodeFull_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32TailDecodeFull_unambiguous
/-- info: 'BaseN.Base32.decodeFullB32TailOfEncode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32TailOfEncode
/-- info: 'BaseN.Base32.decodeFull_cast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFull_cast
/-- info: 'BaseN.Base32.b32Split_ofBytes_ofBytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base32.b32Split_ofBytes_ofBytes
/-- info: 'BaseN.Base32.decodeFull_b32Tail_suffix_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFull_b32Tail_suffix_nil
/-- info: 'BaseN.Base32.decodeFull_b32Tail_suffix_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFull_b32Tail_suffix_cons
/-- info: 'BaseN.Base32.b32Char_pad_false' does not depend on any axioms -/
#guard_msgs in
#print axioms BaseN.Base32.b32Char_pad_false
/-- info: 'BaseN.Base32.not_rel_b32BlockElem_of_pad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.not_rel_b32BlockElem_of_pad
/-- info: 'BaseN.Base32.Rel_b32BlockElem_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.Rel_b32BlockElem_size
/-- info: 'BaseN.Base32.Rel_b32TailElem_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.Rel_b32TailElem_size
/-- info: 'BaseN.Base32.Rel_b32BlockElem_not_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.Rel_b32BlockElem_not_tail
/-- info: 'BaseN.Base32.Rel_b32TailElem_has_pad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.Rel_b32TailElem_has_pad
/-- info: 'BaseN.Base32.relB32Block_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.relB32Block_len
/-- info: 'BaseN.Base32.relB32Tail_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.relB32Tail_len
/-- info: 'BaseN.Base32.encodeB32Block_nopad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.encodeB32Block_nopad
/-- info: 'BaseN.Base32.encodeB32Tail_has_pad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.encodeB32Tail_has_pad
/-- info: 'BaseN.Base32.encodeB32Tail_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.encodeB32Tail_len
/-- info: 'BaseN.Base32.prepend_concat_prefix_cast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.prepend_concat_prefix_cast
/-- info: 'BaseN.Base32.prepend_concat_suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.prepend_concat_suffix
/-- info: 'BaseN.Base32.b32BoundaryPin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BoundaryPin
/-- info: 'BaseN.Base32.b32BlockRunOfBoundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockRunOfBoundary
/-- info: 'BaseN.Base32.decodeFullB32_mem_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_mem_encode
/-- info: 'BaseN.Base32.decodeFullB32_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_some
/-- info: 'BaseN.Base32.Rel_b32TailElem_first_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.Rel_b32TailElem_first_char
/-- info: 'BaseN.Base32.b32Tail1_pad_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32Tail1_pad_bits
/-- info: 'BaseN.Base32.b32Tail1_pad_bits_mod4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32Tail1_pad_bits_mod4
/-- info: 'BaseN.Base32.b32TailBlock_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32TailBlock_canonical
/-- info: 'BaseN.Base32.relB32Block_len5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.relB32Block_len5
/-- info: 'BaseN.Base32.b32Split_blocks_tail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base32.b32Split_blocks_tail
/-- info: 'BaseN.Base32.encodeB32Tail_of_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.encodeB32Tail_of_rel
/-- info: 'BaseN.Base32.encodeB32Tail_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.encodeB32Tail_ne_none
/-- info: 'BaseN.Base32.encodeB32'_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.encodeB32'_ne_none
/-- info: 'BaseN.Base32.b32BytesOf_tail1_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms BaseN.Base32.b32BytesOf_tail1_eq

/- Every `Base64` law not gated above (ledger §6.4 complete coverage). -/
/-- info: 'BaseN.Base64.b64ToVal_valToB64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64ToVal_valToB64
/-- info: 'BaseN.Base64.valToB64_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.valToB64_valid
/-- info: 'BaseN.Base64.valToB64_not_pad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.valToB64_not_pad
/-- info: 'BaseN.Base64.valToB64_lt_256' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.valToB64_lt_256
/-- info: 'BaseN.Base64.byte0Of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.byte0Of
/-- info: 'BaseN.Base64.byte1Of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.byte1Of
/-- info: 'BaseN.Base64.byte2Of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.byte2Of
/-- info: 'BaseN.Base64.b64Valid_of_decide' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base64.b64Valid_of_decide
/-- info: 'BaseN.Base64.valToB64_b64ToVal_of_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.valToB64_b64ToVal_of_valid
/-- info: 'BaseN.Base64.b64BlockDecodeLenient_unapply_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64BlockDecodeLenient_unapply_single
/-- info: 'BaseN.Base64.b64BlockDecodeLenient_unapply_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64BlockDecodeLenient_unapply_pair
/-- info: 'BaseN.Base64.b64BlockDecodeLenient_unapply_triple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64BlockDecodeLenient_unapply_triple
/-- info: 'BaseN.Base64.b64BlockIso_law' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64BlockIso_law
/-- info: 'BaseN.Base64.b64BlockConsumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64BlockConsumesByte
/-- info: 'BaseN.Base64.b64BlockElem_functional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64BlockElem_functional
/-- info: 'BaseN.Base64.Rel_b64BlockElem_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.Rel_b64BlockElem_canonical
/-- info: 'BaseN.Base64.b64TailIso_law' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64TailIso_law
/-- info: 'BaseN.Base64.b64TailConsumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64TailConsumesByte
/-- info: 'BaseN.Base64.b64TailElem_functional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64TailElem_functional
/-- info: 'BaseN.Base64.b64BlockElem_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64BlockElem_unambiguous
/-- info: 'BaseN.Base64.Rel_b64BlockElem_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.Rel_b64BlockElem_len
/-- info: 'BaseN.Base64.Rel_b64BlockElem_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.Rel_b64BlockElem_size
/-- info: 'BaseN.Base64.relB64Block_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.relB64Block_unambiguous
/-- info: 'BaseN.Base64.b64BlockDecodeFull_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64BlockDecodeFull_unambiguous
/-- info: 'BaseN.Base64.b64TailElem_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64TailElem_unambiguous
/-- info: 'BaseN.Base64.Rel_b64TailElem_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.Rel_b64TailElem_len
/-- info: 'BaseN.Base64.relB64Tail_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.relB64Tail_unambiguous
/-- info: 'BaseN.Base64.b64TailDecodeFull_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64TailDecodeFull_unambiguous
/-- info: 'BaseN.Base64.b64BytesOf_ofBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64BytesOf_ofBytes
/-- info: 'BaseN.Base64.b64OfBytes_bytesOf' does not depend on any axioms -/
#guard_msgs in
#print axioms BaseN.Base64.b64OfBytes_bytesOf
/-- info: 'BaseN.Base64.decodeFullB64TailOfEncode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64TailOfEncode
/-- info: 'BaseN.Base64.decodeFull_cast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFull_cast
/-- info: 'BaseN.Base64.b64Split_ofBytes_ofBytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base64.b64Split_ofBytes_ofBytes
/-- info: 'BaseN.Base64.decodeFull_b64Tail_suffix_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFull_b64Tail_suffix_nil
/-- info: 'BaseN.Base64.decodeFull_b64Tail_suffix_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFull_b64Tail_suffix_cons
/-- info: 'BaseN.Base64.b64Char_pad_false' does not depend on any axioms -/
#guard_msgs in
#print axioms BaseN.Base64.b64Char_pad_false
/-- info: 'BaseN.Base64.not_rel_b64BlockElem_of_pad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.not_rel_b64BlockElem_of_pad
/-- info: 'BaseN.Base64.relB64Block_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.relB64Block_len
/-- info: 'BaseN.Base64.relB64Tail_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.relB64Tail_len
/-- info: 'BaseN.Base64.Rel_b64TailElem_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.Rel_b64TailElem_size
/-- info: 'BaseN.Base64.Rel_b64BlockElem_not_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.Rel_b64BlockElem_not_tail
/-- info: 'BaseN.Base64.Rel_b64TailElem_has_pad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.Rel_b64TailElem_has_pad
/-- info: 'BaseN.Base64.encodeB64Block_nopad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.encodeB64Block_nopad
/-- info: 'BaseN.Base64.encodeB64Tail_has_pad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.encodeB64Tail_has_pad
/-- info: 'BaseN.Base64.encodeB64Tail_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.encodeB64Tail_len
/-- info: 'BaseN.Base64.prepend_concat_prefix_cast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.prepend_concat_prefix_cast
/-- info: 'BaseN.Base64.prepend_concat_suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.prepend_concat_suffix
/-- info: 'BaseN.Base64.b64BoundaryPin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64BoundaryPin
/-- info: 'BaseN.Base64.b64BlockRunOfBoundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64BlockRunOfBoundary
/-- info: 'BaseN.Base64.decodeFullB64_mem_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_mem_encode
/-- info: 'BaseN.Base64.decodeFullB64_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.decodeFullB64_some
/-- info: 'BaseN.Base64.Rel_b64TailElem_first_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.Rel_b64TailElem_first_char
/-- info: 'BaseN.Base64.b64Tail1_pad_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64Tail1_pad_bits
/-- info: 'BaseN.Base64.b64Tail1_pad_bits_mod16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64Tail1_pad_bits_mod16
/-- info: 'BaseN.Base64.b64Tail2_pad_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64Tail2_pad_bits
/-- info: 'BaseN.Base64.b64Tail2_pad_bits_mod4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64Tail2_pad_bits_mod4
/-- info: 'BaseN.Base64.b64Zh_chars' does not depend on any axioms -/
#guard_msgs in
#print axioms BaseN.Base64.b64Zh_chars
/-- info: 'BaseN.Base64.b64TailBlock_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64TailBlock_canonical
/-- info: 'BaseN.Base64.relB64Block_len3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.relB64Block_len3
/-- info: 'BaseN.Base64.b64Split_blocks_tail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base64.b64Split_blocks_tail
/-- info: 'BaseN.Base64.encodeB64Tail_of_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.encodeB64Tail_of_rel
/-- info: 'BaseN.Base64.b64OrPad_of_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base64.b64OrPad_of_valid
/-- info: 'BaseN.Base64.b64OrPad_pad' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base64.b64OrPad_pad
/-- info: 'BaseN.Base64.b64TailElem_encode_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64TailElem_encode_ne_none
/-- info: 'BaseN.Base64.encodeB64Tail_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.encodeB64Tail_ne_none
/-- info: 'BaseN.Base64.b64BlockElem_encode_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.b64BlockElem_encode_ne_none
/-- info: 'BaseN.Base64.encodeB64'_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base64.encodeB64'_ne_none
/-- info: 'BaseN.Base64.b64BytesOf_tail1_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms BaseN.Base64.b64BytesOf_tail1_eq

/-- info: 'BaseN.Base32.b32Tail2_pad_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32Tail2_pad_bits
/-- info: 'BaseN.Base32.b32Tail2_pad_bits_mod16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32Tail2_pad_bits_mod16
/-- info: 'BaseN.Base32.b32Tail3_pad_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32Tail3_pad_bits
/-- info: 'BaseN.Base32.b32Tail3_pad_bits_mod2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32Tail3_pad_bits_mod2
/-- info: 'BaseN.Base32.b32Tail4_pad_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32Tail4_pad_bits
/-- info: 'BaseN.Base32.b32Tail4_pad_bits_mod8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.b32Tail4_pad_bits_mod8
/-- info: 'BaseN.Base32.b32MZTR_chars' does not depend on any axioms -/
#guard_msgs in
#print axioms BaseN.Base32.b32MZTR_chars
/-- info: 'BaseN.Base32.b32MZTGN_chars' does not depend on any axioms -/
#guard_msgs in
#print axioms BaseN.Base32.b32MZTGN_chars
/-- info: 'BaseN.Base32.b32MZTGMZR_chars' does not depend on any axioms -/
#guard_msgs in
#print axioms BaseN.Base32.b32MZTGMZR_chars
/-- info: 'BaseN.Base32.b32BlockApply_b32MZTR_chars' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockApply_b32MZTR_chars
/-- info: 'BaseN.Base32.b32BlockApply_b32MZTGN_chars' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockApply_b32MZTGN_chars
/-- info: 'BaseN.Base32.b32BlockApply_b32MZTGMZR_chars' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base32.b32BlockApply_b32MZTGMZR_chars
/-- info: 'BaseN.Base32.b32TailApply_b32MZTR_chars' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base32.b32TailApply_b32MZTR_chars
/-- info: 'BaseN.Base32.b32TailApply_b32MZTGN_chars' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base32.b32TailApply_b32MZTGN_chars
/-- info: 'BaseN.Base32.b32TailApply_b32MZTGMZR_chars' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BaseN.Base32.b32TailApply_b32MZTGMZR_chars
/-- info: 'BaseN.Base32.decodeFullB32_reject_of_pad_and_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_reject_of_pad_and_tail
/-- info: 'BaseN.Base32.decodeFullB32_reject_MZTR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_reject_MZTR
/-- info: 'BaseN.Base32.decodeFullB32_reject_MZTGN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_reject_MZTGN
/-- info: 'BaseN.Base32.decodeFullB32_reject_MZTGMZR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base32.decodeFullB32_reject_MZTGMZR
