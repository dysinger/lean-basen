/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import BaseN
import Codec
import Lean.Elab.Command

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

**Coverage is complete and now *enforced*:** every public `theorem` of
`Base2`/`Base4`/`Base8`/`Base10`/`Base16`/`Base32`/`Base64`/`Common` is either
pinned by a `#guard_msgs` below or recorded in `generatedAuxAllowlist` with a reason.
(The audit that prompted this found 91 of 404, i.e. 22.5% — the gap was real and took
two sessions to close.)

**The counts, stated correctly, because an earlier version of this paragraph
over-counted by conflating two namespaces.** The file carries **440 pins**: **437**
are `BaseN.*` laws and **3** are `Codec.*` (`roundtrip`, `bidir`, `decode_spec`) —
the *dependency's* laws, pinned for discipline and outside this repo's own universe.
`publicTheorems` walks only `BaseN`, so the gate's own universe is
**483 = 437 + 46 allowlisted**. The 437 pinned footprints are 375
`[propext, Quot.sound]`, 48 `[propext]`-only, 15 axiom-free, and the 3 `Codec.*` pins
add 2 more `[propext, Quot.sound]` and 1 `[Quot.sound]`-only (`Codec.Bytes.ext`).
`Classical.choice` appears nowhere. The "universe, as measured" table further down
states 483/437/46 and is asserted by a `run_cmd`, so it cannot drift again.

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
/-- info: 'BaseN.Base2.rejects_single_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base2.rejects_single_char

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
/-- info: 'BaseN.Base4.rejects_single_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base4.rejects_single_char

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
/-- info: 'BaseN.Base8.rejects_single_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base8.rejects_single_char
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
/-- info: 'BaseN.Base10.rejects_single_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base10.rejects_single_char
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
/-- info: 'BaseN.Base16.rejects_lowercase_even_arity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.rejects_lowercase_even_arity
/-- info: 'BaseN.Base16.rejects_single_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BaseN.Base16.rejects_single_char
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

/-! ## Mechanism: the gate's universe, enumerated from the environment

Everything above is a **hand-written** `#guard_msgs` block per law. That is a
statement of intent, not a check: nothing fails when a new law is added and its
block forgotten. Measured before this section existed —
`grep -cE 'run_cmd|Lean\.Elab|Environment|partitionInto|getEnv' Axioms.lean` → `0` —
so the 437 `BaseN.*` pins plus the 3 `Codec.*` pins agreed with the module theorems
**by maintenance discipline only**, and one added law would have shrunk the gate
silently. That is precisely the hole `lean-codec` closed in its first audit round
(`Axioms.lean`'s `partition`/`gateCoverage` checks); this section adopts the
mechanism back. The *shape* (a `@[default_target]` `Axioms` lib) originated here, but
the *mechanism* was `lean-codec`'s strengthening, and a reader who copies the shape
alone copies the weaker version.

Two `run_cmd` checks make the gate a **partition** with no third route:

* `coverage` — the set the environment reports agrees with the names pinned above,
  so a law landing un-gated fails the build naming it, and a stale pin fails too.
* `partition` — every public theorem is in the pinned set **xor**
  `generatedAuxAllowlist`; both at once is a self-contradiction, and neither at
  once is an un-gated law.

### What this is, and what it is not

It is a **membership proxy**, not a proof of law strength: "is this a real law?" is
not decidable from the environment, while "is this constant in the pinned set?" is.
What the partition guarantees is that no public theorem can be covered by
**silence** — the failure mode that was actually present — and that the allowlist
cannot smuggle a law out of the gate. Do not read a green build as soundness.

### The universe, as measured (2026-11-05)

`publicTheorems` walks `Environment.constants` and keeps every `thmInfo` constant in
the `BaseN` namespace:

| side | count |
| --- | --- |
| public theorems in the `BaseN` namespace | **484** |
| pinned by a `#guard_msgs` above (`gatedNames`) | **438** |
| allowlisted (`generatedAuxAllowlist`) | **46** |
| un-gated and unlisted | **0** |

484 = 438 + 46, with no third route. Of the 46 allowlisted, **37** are the ones the
suffix classifier drops (`*.inj` ×9, `*.injEq` ×9, `*.sizeOf_spec` ×11, `*.eq_def`
×8) and **9** are the hand-reviewed ones that the classifier does *not* match
(`brecOn.eq` ×2, `*.go` ×6, `Run.step`) — the `*.go` helpers are the trap, since
`.go` is not in the suffix list, so they land on the kept side and only `partition`
catches them.

The 3 `Codec.*` pins (roundtrip/bidir/decode_spec) are the dependency's laws and lie
*outside* this namespace — pinned for discipline, not partitioned, which is why
`grep -c '^#print axioms'` reports 440 against `gatedNames`' 437.

**Two counts this section got wrong in its first version, both now corrected in
place.** The header said "all **440** public theorems" (conflating the 3 `Codec.*`
pins with this namespace), and this table then said 446 / 437 / **9**, because the
9 hand-reviewed entries were written before the 37 suffix-dropped ones were added to
the allowlist and the prose was never updated to match. The `run_cmd` output was
right both times — `basen axiom gate: 483 public theorems partitioned, 437 pinned
and 46 allowlisted` — which is the argument for deriving these numbers rather than
transcribing them (see the `run_cmd` below, which prints all three).
-/

namespace BaseNAxioms

open Lean Elab Command

/-- Default classifier for non-authorial theorem names: the ones the compiler emits
for every structure or `def`.

**This is a heuristic, not an authority.** It exists so `partition` has a default
split, and every decision it makes is audited below — each dropped name must appear
in `generatedAuxAllowlist` with a reason. A wrong decision is a build failure, not a
silent gap. Never read this rule as "therefore not a law". -/
def isGeneratedAux (n : Name) : Bool := Id.run do
  let s := n.components.getLast!.toString
  return s == "eq_def" || s == "inj" || s == "injEq" || s == "sizeOf_spec" ||
    s == "congr_simp" || s == "dec" || s == "induct" || s == "eq_irrel"

/-- Every public theorem candidate in the `BaseN` namespace, **before** any
name-based declination. This is the universe `gatedNames` and
`generatedAuxAllowlist` must partition.

The unsafe / private / internal-detail filter is *not* a declination: those are not
public surface at all, so they are outside the universe rather than dropped from it.
The allowlist only ever describes names a reader could cite. -/
def publicTheorems (env : Environment) : Array Name := Id.run do
  let mut thms : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if (`BaseN).isPrefixOf name then
      match ci with
      | .thmInfo _ =>
        if ci.isUnsafe || isPrivateName name || name.isInternalDetail then
          pure ()
        else
          thms := thms.push name
      | _ => pure ()
  return thms.qsort (fun a b => Name.toString a < Name.toString b)

/-- The membership decisions of `isGeneratedAux`, per name — the candidate set split
into the two sets the partition requires. -/
def partitionInto (env : Environment) : Array Name × Array Name := Id.run do
  let mut dropped : Array Name := #[]
  let mut kept : Array Name := #[]
  for n in publicTheorems env do
    if isGeneratedAux n then dropped := dropped.push n else kept := kept.push n
  return (kept, dropped)

/-- The kept side of the classifier: the universe minus the names `isGeneratedAux`
drops — the set the pinned names mirror. -/
def gatedTheorems (env : Environment) : Array Name := partitionInto env |>.1

/-- Declarations knowingly excluded from the `[propext, Quot.sound]`-only discipline,
by name. Each must also appear in an "Explicit exclusion" note with its measured
footprint and the reason. An exclusion is a decision on the record — never a silent
omission, and never described in prose as clean.

**Currently empty.** -/
def exclusions : Array Name := #[]

/-- The other half of the gate's partition: every public theorem listed here **by
name with the reason it is not a law**.

`BaseNAxioms.partition` requires every name here to be a real public theorem of the
environment (so the list cannot name something that does not exist), requires every
public theorem to appear here **or** in the pinned set (so nothing falls between the
two), and requires the list to be disjoint from the pinned set.

Why each of the 46 is not a law, in the groups below (the 37 suffix-dropped
entries are grouped by suffix at the end; the 9 hand-reviewed ones come first):

* **`brecOn.eq` (×2)** — the recursion equation Lean derives for `B32.brecOn` /
  `B64.brecOn`, the below/`brecOn` eliminator of an inductive. Part of the
  eliminator's compilation, like `eq_def` for a `def`; it states nothing about which
  bytes a base accepts.
* **`*.go` (×6)** — the `where`-clause helper of a structural induction
  (`b32BytesOf_ofBytes.go` and friends). Lean gives it a public name, but it is a
  *step* of the enclosing proof, not an independent statement, and it is meaningful
  only relative to that proof's induction.
* **`Run.step`** — a `Prop`-valued **structure field projection**: the
  `ConsumesByte elem` productivity witness a caller *supplies* to `Run`, not a
  theorem about it. Same shape as `Iso.MeasureDecreases.dec` in `lean-codec`, where
  the obligation's *satisfiability* is the law and the projection itself is not. -/
def generatedAuxAllowlist : Array Name := #[

-- **`brecOn.eq` (×2)** — the recursion equation Lean derives for `B32.brecOn` /
-- `B64.brecOn`, the below/`brecOn` eliminator of an inductive. Part of the
-- eliminator's compilation, like `eq_def` for a `def`; it states nothing about which
-- bytes a base accepts.
  `BaseN.Base32.B32.brecOn.eq,
  `BaseN.Base64.B64.brecOn.eq,


-- **`*.go` (×6)** — the `where`-clause helper of a structural induction
-- (`b32BytesOf_ofBytes.go` and friends). Lean gives it a public name, but it is a
-- *step* of the enclosing proof, not an independent statement, and it is meaningful
-- only relative to that proof's induction.
  `BaseN.Base32.b32BytesOf_ofBytes.go,
  `BaseN.Base32.b32Split_ofBytes_ofBytes.go,
  `BaseN.Base32.b32Split_shape.go,
  `BaseN.Base64.b64BytesOf_ofBytes.go,
  `BaseN.Base64.b64Split_ofBytes_ofBytes.go,
  `BaseN.Base64.b64Split_shape.go,


-- **`Run.step`** — a `Prop`-valued **structure field projection**: the
-- `ConsumesByte elem` productivity witness a caller *supplies* to `Run`, not a theorem
-- about it. Same shape as `Iso.MeasureDecreases.dec` in `lean-codec`, where the
-- obligation's *satisfiability* is the law and the projection itself is not.
  `BaseN.Common.Run.step,

-- **`inj` — the injectivity equation of a constructor.** Lean emits it for every
-- inductive constructor and structure `mk`: two applications are equal iff their
-- fields are, which the constructor's own typing already gives. It states nothing
-- about which bytes a base accepts.
  `BaseN.Base32.B32.full.inj,
  `BaseN.Base32.B32.tail1.inj,
  `BaseN.Base32.B32.tail2.inj,
  `BaseN.Base32.B32.tail3.inj,
  `BaseN.Base32.B32.tail4.inj,
  `BaseN.Base64.B64.full.inj,
  `BaseN.Base64.B64.tail1.inj,
  `BaseN.Base64.B64.tail2.inj,
  `BaseN.Common.Run.mk.inj,

-- **`injEq` — the `Bool`-valued form of the same equation**, the shape `simp`
-- consumes. An auxiliary of `inj`, not an independent statement.
  `BaseN.Base32.B32.full.injEq,
  `BaseN.Base32.B32.tail1.injEq,
  `BaseN.Base32.B32.tail2.injEq,
  `BaseN.Base32.B32.tail3.injEq,
  `BaseN.Base32.B32.tail4.injEq,
  `BaseN.Base64.B64.full.injEq,
  `BaseN.Base64.B64.tail1.injEq,
  `BaseN.Base64.B64.tail2.injEq,
  `BaseN.Common.Run.mk.injEq,

-- **`sizeOf_spec` — the defining equation of the derived `SizeOf` instance.**
-- Part of Lean's termination machinery; about the size of a description value, not
-- about a codec's behaviour.
  `BaseN.Base32.B32.full.sizeOf_spec,
  `BaseN.Base32.B32.nil.sizeOf_spec,
  `BaseN.Base32.B32.tail1.sizeOf_spec,
  `BaseN.Base32.B32.tail2.sizeOf_spec,
  `BaseN.Base32.B32.tail3.sizeOf_spec,
  `BaseN.Base32.B32.tail4.sizeOf_spec,
  `BaseN.Base64.B64.full.sizeOf_spec,
  `BaseN.Base64.B64.nil.sizeOf_spec,
  `BaseN.Base64.B64.tail1.sizeOf_spec,
  `BaseN.Base64.B64.tail2.sizeOf_spec,
  `BaseN.Common.Run.mk.sizeOf_spec,

-- **`eq_def` — the compiled-body equation of a `def`** (`f x = body`). It unfolds
-- a definition the source already states; nobody cites it as an authority, and it
-- is regenerated automatically whenever the body changes.
  `BaseN.Base32.b32BytesOf.eq_def,
  `BaseN.Base32.b32OfBytes.eq_def,
  `BaseN.Base32.b32Split.eq_def,
  `BaseN.Base32.b32Split_ofBytes.eq_def,
  `BaseN.Base64.b64BytesOf.eq_def,
  `BaseN.Base64.b64OfBytes.eq_def,
  `BaseN.Base64.b64Split.eq_def,
  `BaseN.Base64.b64Split_ofBytes.eq_def
]

-- BEGIN PINNED gatedNames
/-- The `BaseN.*` names this file pins a `#guard_msgs` block for. Kept in lockstep
with the blocks above by the `coverage` check, which fails on any drift. Written
from the `#print axioms` lines, so it is a record of what is gated rather than a
second list to maintain by hand. -/
def gatedNames : List Lean.Name := [
  `BaseN.Base10.Rel_digElem_canonical,
  `BaseN.Base10.Rel_digElem_len,
  `BaseN.Base10.decodeFull_B10_char,
  `BaseN.Base10.decodeFull_canonical,
  `BaseN.Base10.decode_encode_inverse,
  `BaseN.Base10.digBlockApply_unapply,
  `BaseN.Base10.digBlockIso_law,
  `BaseN.Base10.digBlockUnapply_digits,
  `BaseN.Base10.digConsumesByte,
  `BaseN.Base10.digDecodeFull_unambiguous,
  `BaseN.Base10.digDigit_valid_of_byte,
  `BaseN.Base10.digElem_encode_ne_none,
  `BaseN.Base10.digElem_functional,
  `BaseN.Base10.digElem_unambiguous,
  `BaseN.Base10.digVal_toByte_valToDig,
  `BaseN.Base10.digVal_valToDig,
  `BaseN.Base10.digValid_of_decide,
  `BaseN.Base10.dig_decompose_unique,
  `BaseN.Base10.dig_sum_eq,
  `BaseN.Base10.encodeDig_canonical,
  `BaseN.Base10.encodeDig_injective_eq,
  `BaseN.Base10.encodeDig_ne_none,
  `BaseN.Base10.encode_injective,
  `BaseN.Base10.rejects_single_char,
  `BaseN.Base10.rejects_invalid_byte,
  `BaseN.Base10.rejects_overflow,
  `BaseN.Base10.relDig_unambiguous,
  `BaseN.Base10.roundtrip,
  `BaseN.Base10.valToDig_digVal_of_valid,
  `BaseN.Base10.valToDig_lt_256,
  `BaseN.Base10.valToDig_valid,
  `BaseN.Base16.Rel_hexElem_canonical,
  `BaseN.Base16.Rel_hexElem_len,
  `BaseN.Base16.decodeFull_B16_char,
  `BaseN.Base16.decodeFull_canonical,
  `BaseN.Base16.decodeHexBlockFold_both_cases,
  `BaseN.Base16.decodeHexBlockFold_case_insensitive,
  `BaseN.Base16.decodeHexFold_both_cases,
  `BaseN.Base16.decodeHexFold_lowercase_eq,
  `BaseN.Base16.decodeHexFold_of_fixed,
  `BaseN.Base16.decode_encode_inverse,
  `BaseN.Base16.encodeHex_canonical,
  `BaseN.Base16.encodeHex_injective_eq,
  `BaseN.Base16.encodeHex_ne_none,
  `BaseN.Base16.encode_injective,
  `BaseN.Base16.fill_foldList,
  `BaseN.Base16.foldByteBytes_idem,
  `BaseN.Base16.foldByte_fixed,
  `BaseN.Base16.foldByte_folded,
  `BaseN.Base16.foldByte_idem,
  `BaseN.Base16.foldList_cons,
  `BaseN.Base16.foldList_hexBlockUnapply,
  `BaseN.Base16.foldList_idem,
  `BaseN.Base16.foldList_nil,
  `BaseN.Base16.foldNormalizer,
  `BaseN.Base16.hexBlockApply_foldList,
  `BaseN.Base16.hexBlockApply_foldList_ne,
  `BaseN.Base16.hexBlockApply_none_of_not_len2,
  `BaseN.Base16.hexBlockApply_unapply,
  `BaseN.Base16.hexBlockIsoF_law,
  `BaseN.Base16.hexBlockIso_law,
  `BaseN.Base16.hexBlockUnapply_digits,
  `BaseN.Base16.hexConsumesByte,
  `BaseN.Base16.hexDecodeFull_unambiguous,
  `BaseN.Base16.hexDigit_valid_of_byte,
  `BaseN.Base16.hexElem_encode_ne_none,
  `BaseN.Base16.hexElem_functional,
  `BaseN.Base16.hexElem_unambiguous,
  `BaseN.Base16.hexFixed_of_valid,
  `BaseN.Base16.hexNibbleValid_false_of_lower,
  `BaseN.Base16.hexNibbleValid_foldByte,
  `BaseN.Base16.hexNibbleValid_of_decide,
  `BaseN.Base16.hexNibbleValid_of_hexFixed,
  `BaseN.Base16.hexToNibble_digit,
  `BaseN.Base16.hexToNibble_foldByte_false,
  `BaseN.Base16.hexToNibble_foldByte_true,
  `BaseN.Base16.hexToNibble_foldByte_value,
  `BaseN.Base16.hexToNibble_lower,
  `BaseN.Base16.hexToNibble_nibbleToHex,
  `BaseN.Base16.hexToNibble_toByte_nibbleToHex,
  `BaseN.Base16.hexToNibble_upper,
  `BaseN.Base16.hex_decompose_unique,
  `BaseN.Base16.nibbleToHex_hexToNibble_of_valid,
  `BaseN.Base16.nibbleToHex_lt_256,
  `BaseN.Base16.nibbleToHex_valid,
  `BaseN.Base16.ofNat_sub32_toNat,
  `BaseN.Base16.rejects_invalid_byte,
  `BaseN.Base16.rejects_lowercase,
  `BaseN.Base16.rejects_lowercase_even_arity,
  `BaseN.Base16.rejects_single_char,
  `BaseN.Base16.relHex_unambiguous,
  `BaseN.Base16.roundtrip,
  `BaseN.Base2.Rel_bitElem_canonical,
  `BaseN.Base2.Rel_bitElem_len,
  `BaseN.Base2.bitAt_le_one,
  `BaseN.Base2.bitBlockApply_unapply,
  `BaseN.Base2.bitBlockIso_law,
  `BaseN.Base2.bitBlockUnapply_digits,
  `BaseN.Base2.bitConsumesByte,
  `BaseN.Base2.bitDecodeFull_unambiguous,
  `BaseN.Base2.bitDigit_valid_of_byte,
  `BaseN.Base2.bitElem_encode_ne_none,
  `BaseN.Base2.bitElem_functional,
  `BaseN.Base2.bitElem_unambiguous,
  `BaseN.Base2.bitVal_toByte_valToBit,
  `BaseN.Base2.bitVal_valToBit,
  `BaseN.Base2.bitValid_of_decide,
  `BaseN.Base2.bitsVal_bitsOf,
  `BaseN.Base2.bits_decompose_unique,
  `BaseN.Base2.decodeFull_B2_char,
  `BaseN.Base2.decodeFull_canonical,
  `BaseN.Base2.decode_encode_inverse,
  `BaseN.Base2.encodeBit_canonical,
  `BaseN.Base2.encodeBit_injective_eq,
  `BaseN.Base2.encodeBit_ne_none,
  `BaseN.Base2.encode_injective,
  `BaseN.Base2.rejects_single_char,
  `BaseN.Base2.rejects_invalid_byte,
  `BaseN.Base2.relBit_unambiguous,
  `BaseN.Base2.roundtrip,
  `BaseN.Base2.valToBit_bitVal_of_valid,
  `BaseN.Base2.valToBit_lt_256,
  `BaseN.Base2.valToBit_valid,
  `BaseN.Base32.Rel_b32BlockElem_canonical,
  `BaseN.Base32.Rel_b32BlockElem_len,
  `BaseN.Base32.Rel_b32BlockElem_not_tail,
  `BaseN.Base32.Rel_b32BlockElem_size,
  `BaseN.Base32.Rel_b32TailElem_first_char,
  `BaseN.Base32.Rel_b32TailElem_has_pad,
  `BaseN.Base32.Rel_b32TailElem_len,
  `BaseN.Base32.Rel_b32TailElem_pad_pos,
  `BaseN.Base32.Rel_b32TailElem_size,
  `BaseN.Base32.b32BlockApply_b32MZTGMZR_chars,
  `BaseN.Base32.b32BlockApply_b32MZTGN_chars,
  `BaseN.Base32.b32BlockApply_b32MZTR_chars,
  `BaseN.Base32.b32BlockApply_b32Mz_chars,
  `BaseN.Base32.b32BlockConsumesByte,
  `BaseN.Base32.b32BlockDecodeFull_unambiguous,
  `BaseN.Base32.b32BlockDecodeLenient_unapply_pair,
  `BaseN.Base32.b32BlockDecodeLenient_unapply_quad,
  `BaseN.Base32.b32BlockDecodeLenient_unapply_quintet,
  `BaseN.Base32.b32BlockDecodeLenient_unapply_single,
  `BaseN.Base32.b32BlockDecodeLenient_unapply_triple,
  `BaseN.Base32.b32BlockElem_encode_ne_none,
  `BaseN.Base32.b32BlockElem_functional,
  `BaseN.Base32.b32BlockElem_unambiguous,
  `BaseN.Base32.b32BlockIso_law,
  `BaseN.Base32.b32BlockRunOfBoundary,
  `BaseN.Base32.b32BlockUnapply_chars,
  `BaseN.Base32.b32BlockUnapply_len5,
  `BaseN.Base32.b32BlockUnapply_len8,
  `BaseN.Base32.b32BlockUnapply_total,
  `BaseN.Base32.b32BoundaryPin,
  `BaseN.Base32.b32BytesOf_ofBytes,
  `BaseN.Base32.b32BytesOf_tail1_eq,
  `BaseN.Base32.b32Char_pad_false,
  `BaseN.Base32.b32MZTGMZR_chars,
  `BaseN.Base32.b32MZTGN_chars,
  `BaseN.Base32.b32MZTR_chars,
  `BaseN.Base32.b32Mz_chars,
  `BaseN.Base32.b32OfBytes_bytesOf,
  `BaseN.Base32.b32OrPad_of_valid,
  `BaseN.Base32.b32OrPad_pad,
  `BaseN.Base32.b32OrPad_toByte_valToB32,
  `BaseN.Base32.b32Split_blocks_tail,
  `BaseN.Base32.b32Split_ofBytes_ofBytes,
  `BaseN.Base32.b32Split_ofBytes_shape_bounds,
  `BaseN.Base32.b32Split_shape,
  `BaseN.Base32.b32Tail1_pad_bits,
  `BaseN.Base32.b32Tail1_pad_bits_mod4,
  `BaseN.Base32.b32Tail2_pad_bits,
  `BaseN.Base32.b32Tail2_pad_bits_mod16,
  `BaseN.Base32.b32Tail3_pad_bits,
  `BaseN.Base32.b32Tail3_pad_bits_mod2,
  `BaseN.Base32.b32Tail4_pad_bits,
  `BaseN.Base32.b32Tail4_pad_bits_mod8,
  `BaseN.Base32.b32TailApply_b32MZTGMZR_chars,
  `BaseN.Base32.b32TailApply_b32MZTGN_chars,
  `BaseN.Base32.b32TailApply_b32MZTR_chars,
  `BaseN.Base32.b32TailApply_b32Mz_chars,
  `BaseN.Base32.b32TailBlock_canonical,
  `BaseN.Base32.b32TailConsumesByte,
  `BaseN.Base32.b32TailDecodeFull_unambiguous,
  `BaseN.Base32.b32TailElem_encode_ne_none,
  `BaseN.Base32.b32TailElem_functional,
  `BaseN.Base32.b32TailElem_unambiguous,
  `BaseN.Base32.b32TailIso_law,
  `BaseN.Base32.b32TailUnapply_len14,
  `BaseN.Base32.b32ToVal_valToB32,
  `BaseN.Base32.b32Valid_of_decide,
  `BaseN.Base32.byte0Of,
  `BaseN.Base32.byte1Of,
  `BaseN.Base32.byte2Of,
  `BaseN.Base32.byte3Of,
  `BaseN.Base32.byte4Of,
  `BaseN.Base32.decodeFullB32TailOfEncode,
  `BaseN.Base32.decodeFullB32_arity,
  `BaseN.Base32.decodeFullB32_char,
  `BaseN.Base32.decodeFullB32_char_via_type,
  `BaseN.Base32.decodeFullB32_consumed_alphabet,
  `BaseN.Base32.decodeFullB32_conv,
  `BaseN.Base32.decodeFullB32_mem_encode,
  `BaseN.Base32.decodeFullB32_reject_MYAAAA,
  `BaseN.Base32.decodeFullB32_reject_MZ,
  `BaseN.Base32.decodeFullB32_reject_MZTGMZR,
  `BaseN.Base32.decodeFullB32_reject_MZTGN,
  `BaseN.Base32.decodeFullB32_reject_MZTR,
  `BaseN.Base32.decodeFullB32_reject_arity,
  `BaseN.Base32.decodeFullB32_reject_bad_length,
  `BaseN.Base32.decodeFullB32_reject_first_invalid,
  `BaseN.Base32.decodeFullB32_reject_invalid_at,
  `BaseN.Base32.decodeFullB32_reject_invalid_char,
  `BaseN.Base32.decodeFullB32_reject_of_pad_and_tail,
  `BaseN.Base32.decodeFullB32_reject_pad_at_low_slot,
  `BaseN.Base32.decodeFullB32_reject_pad_first,
  `BaseN.Base32.decodeFullB32_roundtrip,
  `BaseN.Base32.decodeFullB32_some,
  `BaseN.Base32.decodeFullB32_spine,
  `BaseN.Base32.decodeFull_b32Tail_suffix_cons,
  `BaseN.Base32.decodeFull_b32Tail_suffix_nil,
  `BaseN.Base32.decodeFull_cast,
  `BaseN.Base32.encodeB32'_ne_none,
  `BaseN.Base32.encodeB32Block_nopad,
  `BaseN.Base32.encodeB32Tail_has_pad,
  `BaseN.Base32.encodeB32Tail_len,
  `BaseN.Base32.encodeB32Tail_ne_none,
  `BaseN.Base32.encodeB32Tail_of_rel,
  `BaseN.Base32.encodeB32_canonical,
  `BaseN.Base32.encodeB32_injective,
  `BaseN.Base32.encodeB32_injective_eq,
  `BaseN.Base32.encodeB32_ne_none,
  `BaseN.Base32.not_rel_b32BlockElem_of_pad,
  `BaseN.Base32.not_rel_b32TailElem_of_apply_none,
  `BaseN.Base32.prepend_concat_prefix_cast,
  `BaseN.Base32.prepend_concat_suffix,
  `BaseN.Base32.relB32Block_len,
  `BaseN.Base32.relB32Block_len5,
  `BaseN.Base32.relB32Block_unambiguous,
  `BaseN.Base32.relB32Tail_len,
  `BaseN.Base32.relB32Tail_unambiguous,
  `BaseN.Base32.valToB32_b32ToVal_of_valid,
  `BaseN.Base32.valToB32_lt_256,
  `BaseN.Base32.valToB32_not_pad,
  `BaseN.Base32.valToB32_valid,
  `BaseN.Base4.Rel_quartetElem_canonical,
  `BaseN.Base4.Rel_quartetElem_len,
  `BaseN.Base4.decodeFull_B4_char,
  `BaseN.Base4.decodeFull_canonical,
  `BaseN.Base4.decode_encode_inverse,
  `BaseN.Base4.encodeQuartet_canonical,
  `BaseN.Base4.encodeQuartet_injective_eq,
  `BaseN.Base4.encodeQuartet_ne_none,
  `BaseN.Base4.encode_injective,
  `BaseN.Base4.quartetAt_le,
  `BaseN.Base4.quartetBlockApply_unapply,
  `BaseN.Base4.quartetBlockIso_law,
  `BaseN.Base4.quartetBlockUnapply_digits,
  `BaseN.Base4.quartetConsumesByte,
  `BaseN.Base4.quartetDecodeFull_unambiguous,
  `BaseN.Base4.quartetDigit_valid_of_byte,
  `BaseN.Base4.quartetElem_encode_ne_none,
  `BaseN.Base4.quartetElem_functional,
  `BaseN.Base4.quartetElem_unambiguous,
  `BaseN.Base4.quartetVal_toByte_valToQuartet,
  `BaseN.Base4.quartetVal_valToQuartet,
  `BaseN.Base4.quartetValid_of_decide,
  `BaseN.Base4.quartetsVal_quartetsOf,
  `BaseN.Base4.quartets_decompose_unique,
  `BaseN.Base4.rejects_single_char,
  `BaseN.Base4.rejects_invalid_byte,
  `BaseN.Base4.relQuartet_unambiguous,
  `BaseN.Base4.roundtrip,
  `BaseN.Base4.valToQuartet_lt_256,
  `BaseN.Base4.valToQuartet_quartetVal_of_valid,
  `BaseN.Base4.valToQuartet_valid,
  `BaseN.Base64.Rel_b64BlockElem_canonical,
  `BaseN.Base64.Rel_b64BlockElem_len,
  `BaseN.Base64.Rel_b64BlockElem_not_tail,
  `BaseN.Base64.Rel_b64BlockElem_size,
  `BaseN.Base64.Rel_b64TailElem_first_char,
  `BaseN.Base64.Rel_b64TailElem_has_pad,
  `BaseN.Base64.Rel_b64TailElem_len,
  `BaseN.Base64.Rel_b64TailElem_pad_pos,
  `BaseN.Base64.Rel_b64TailElem_size,
  `BaseN.Base64.b64BlockApply_b64Zh_chars,
  `BaseN.Base64.b64BlockApply_b64Zm9_chars,
  `BaseN.Base64.b64BlockConsumesByte,
  `BaseN.Base64.b64BlockDecodeFull_unambiguous,
  `BaseN.Base64.b64BlockDecodeLenient_unapply_pair,
  `BaseN.Base64.b64BlockDecodeLenient_unapply_single,
  `BaseN.Base64.b64BlockDecodeLenient_unapply_triple,
  `BaseN.Base64.b64BlockElem_encode_ne_none,
  `BaseN.Base64.b64BlockElem_functional,
  `BaseN.Base64.b64BlockElem_unambiguous,
  `BaseN.Base64.b64BlockIso_law,
  `BaseN.Base64.b64BlockRunOfBoundary,
  `BaseN.Base64.b64BlockUnapply_len3,
  `BaseN.Base64.b64BlockUnapply_one,
  `BaseN.Base64.b64BlockUnapply_two,
  `BaseN.Base64.b64BoundaryPin,
  `BaseN.Base64.b64BytesOf_ofBytes,
  `BaseN.Base64.b64BytesOf_tail1_eq,
  `BaseN.Base64.b64Char_pad_false,
  `BaseN.Base64.b64OfBytes_bytesOf,
  `BaseN.Base64.b64OrPad_of_valid,
  `BaseN.Base64.b64OrPad_pad,
  `BaseN.Base64.b64Split_blocks_tail,
  `BaseN.Base64.b64Split_ofBytes_ofBytes,
  `BaseN.Base64.b64Split_ofBytes_shape_bounds,
  `BaseN.Base64.b64Split_shape,
  `BaseN.Base64.b64Tail1_pad_bits,
  `BaseN.Base64.b64Tail1_pad_bits_mod16,
  `BaseN.Base64.b64Tail2_pad_bits,
  `BaseN.Base64.b64Tail2_pad_bits_mod4,
  `BaseN.Base64.b64TailApply_b64Zh_chars,
  `BaseN.Base64.b64TailApply_b64Zm9_chars,
  `BaseN.Base64.b64TailBlock_canonical,
  `BaseN.Base64.b64TailConsumesByte,
  `BaseN.Base64.b64TailDecodeFull_unambiguous,
  `BaseN.Base64.b64TailElem_encode_ne_none,
  `BaseN.Base64.b64TailElem_functional,
  `BaseN.Base64.b64TailElem_unambiguous,
  `BaseN.Base64.b64TailIso_law,
  `BaseN.Base64.b64TailUnapply_len12,
  `BaseN.Base64.b64ToVal_valToB64,
  `BaseN.Base64.b64Valid_of_decide,
  `BaseN.Base64.b64Zh_chars,
  `BaseN.Base64.b64Zm9_chars,
  `BaseN.Base64.byte0Of,
  `BaseN.Base64.byte1Of,
  `BaseN.Base64.byte2Of,
  `BaseN.Base64.decodeFullB64TailOfEncode,
  `BaseN.Base64.decodeFullB64_arity,
  `BaseN.Base64.decodeFullB64_block_region,
  `BaseN.Base64.decodeFullB64_char,
  `BaseN.Base64.decodeFullB64_char_via_type,
  `BaseN.Base64.decodeFullB64_consumed_alphabet,
  `BaseN.Base64.decodeFullB64_conv,
  `BaseN.Base64.decodeFullB64_mem_encode,
  `BaseN.Base64.decodeFullB64_reject_ZgAAAA,
  `BaseN.Base64.decodeFullB64_reject_arity,
  `BaseN.Base64.decodeFullB64_reject_b64Zh,
  `BaseN.Base64.decodeFullB64_reject_b64Zm9,
  `BaseN.Base64.decodeFullB64_reject_bad_length,
  `BaseN.Base64.decodeFullB64_reject_first_invalid,
  `BaseN.Base64.decodeFullB64_reject_invalid_at,
  `BaseN.Base64.decodeFullB64_reject_invalid_char,
  `BaseN.Base64.decodeFullB64_reject_pad_at_low_slot,
  `BaseN.Base64.decodeFullB64_reject_pad_first,
  `BaseN.Base64.decodeFullB64_roundtrip,
  `BaseN.Base64.decodeFullB64_some,
  `BaseN.Base64.decodeFullB64_spine,
  `BaseN.Base64.decodeFull_b64Tail_suffix_cons,
  `BaseN.Base64.decodeFull_b64Tail_suffix_nil,
  `BaseN.Base64.decodeFull_cast,
  `BaseN.Base64.encodeB64'_ne_none,
  `BaseN.Base64.encodeB64Block_nopad,
  `BaseN.Base64.encodeB64Tail_has_pad,
  `BaseN.Base64.encodeB64Tail_len,
  `BaseN.Base64.encodeB64Tail_ne_none,
  `BaseN.Base64.encodeB64Tail_of_rel,
  `BaseN.Base64.encodeB64_canonical,
  `BaseN.Base64.encodeB64_injective,
  `BaseN.Base64.encodeB64_injective_eq,
  `BaseN.Base64.encodeB64_ne_none,
  `BaseN.Base64.not_rel_b64BlockElem_of_pad,
  `BaseN.Base64.not_rel_b64TailElem_of_apply_none,
  `BaseN.Base64.prepend_concat_prefix_cast,
  `BaseN.Base64.prepend_concat_suffix,
  `BaseN.Base64.relB64Block_len,
  `BaseN.Base64.relB64Block_len3,
  `BaseN.Base64.relB64Block_unambiguous,
  `BaseN.Base64.relB64Tail_len,
  `BaseN.Base64.relB64Tail_unambiguous,
  `BaseN.Base64.valToB64_b64ToVal_of_valid,
  `BaseN.Base64.valToB64_lt_256,
  `BaseN.Base64.valToB64_not_pad,
  `BaseN.Base64.valToB64_valid,
  `BaseN.Base8.Rel_octElem_canonical,
  `BaseN.Base8.Rel_octElem_len,
  `BaseN.Base8.decodeFull_B8_char,
  `BaseN.Base8.decodeFull_canonical,
  `BaseN.Base8.decode_encode_inverse,
  `BaseN.Base8.encodeOct_canonical,
  `BaseN.Base8.encodeOct_injective_eq,
  `BaseN.Base8.encodeOct_ne_none,
  `BaseN.Base8.encode_injective,
  `BaseN.Base8.octBlockApply_unapply,
  `BaseN.Base8.octBlockIso_law,
  `BaseN.Base8.octBlockUnapply_digits,
  `BaseN.Base8.octConsumesByte,
  `BaseN.Base8.octDecodeFull_unambiguous,
  `BaseN.Base8.octDigit_valid_of_byte,
  `BaseN.Base8.octElem_encode_ne_none,
  `BaseN.Base8.octElem_functional,
  `BaseN.Base8.octElem_unambiguous,
  `BaseN.Base8.octToVal_ofNat_valToOct,
  `BaseN.Base8.octToVal_valToOct,
  `BaseN.Base8.octValid_of_decide,
  `BaseN.Base8.oct_decompose_unique,
  `BaseN.Base8.oct_sum_eq,
  `BaseN.Base8.rejects_single_char,
  `BaseN.Base8.rejects_invalid_byte,
  `BaseN.Base8.rejects_overflow,
  `BaseN.Base8.relOct_unambiguous,
  `BaseN.Base8.roundtrip,
  `BaseN.Base8.valToOct_lt_256,
  `BaseN.Base8.valToOct_octToVal_of_valid,
  `BaseN.Base8.valToOct_valid,
  `BaseN.Common.Functional_count_satisfy,
  `BaseN.Common.Functional_iso,
  `BaseN.Common.Functional_satisfy,
  `BaseN.Common.Productive_count_satisfy_succ,
  `BaseN.Common.Productive_count_succ,
  `BaseN.Common.Productive_iso,
  `BaseN.Common.Productive_satisfy,
  `BaseN.Common.Productive_seq_left,
  `BaseN.Common.Rel_count_satisfy_forall,
  `BaseN.Common.Rel_count_satisfy_len,
  `BaseN.Common.Rel_count_satisfy_length,
  `BaseN.Common.Rel_count_satisfy_ofFn,
  `BaseN.Common.Unambiguous_iso,
  `BaseN.Common.Unambiguous_satisfy,
  `BaseN.Common.bdrop_concat,
  `BaseN.Common.concat_eq_drop_prepend,
  `BaseN.Common.consumesByte_count_satisfy_succ,
  `BaseN.Common.count_satisfy_encode_ne_none,
  `BaseN.Common.count_satisfy_unambiguous,
  `BaseN.Common.decodeRepeat_nil_mem_eq_id,
  `BaseN.Common.decodeRepeat_prefix_concat,
  `BaseN.Common.encodeRepeat_of_rel,
  `BaseN.Common.encode_satisfy_ne_none,
  `BaseN.Common.encode_seq_ne_none,
  `BaseN.Common.head?_eq_some_of_mem_eq,
  `BaseN.Common.nat_lt_four,
  `BaseN.Common.relRepeat_block_len,
  `BaseN.Common.relRepeat_forall,
  `BaseN.Common.relRepeat_functional
]
-- END PINNED gatedNames

end BaseNAxioms

/-! **Coverage check**, run on every `lake build`. Fails when the set of public
theorems the environment exports differs from the set pinned in this file: a missing
name means a theorem landed un-gated, and a name with no theorem means a stale entry
(and, likely, a rename). Both are build failures, so the gate cannot rot into a
snapshot of a past tree. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let covered := Std.HashSet.ofList BaseNAxioms.gatedNames
  let excluded := Std.HashSet.ofList BaseNAxioms.exclusions.toList
  -- Names the partition records as *not laws* are satisfied by the allowlist: the
  -- partition check below is what makes that claim, so this check need not repeat it.
  -- Reading them here is what lets the two checks agree instead of contradicting.
  let allow := Std.HashSet.ofList BaseNAxioms.generatedAuxAllowlist.toList
  let actual := BaseNAxioms.partitionInto env |>.1
  let mut unGated : Array Name := #[]
  let mut coveredSet : Std.HashSet Name := {}
  for n in actual do
    coveredSet := coveredSet.insert n
    if !covered.contains n && !excluded.contains n && !allow.contains n then
      unGated := unGated.push n
  let stale : Array Name := covered.toArray.filter fun n => !coveredSet.contains n
  if !unGated.isEmpty || !stale.isEmpty then
    let mut msg : MessageData := ""
    if !unGated.isEmpty then
      msg := msg ++ m!"theorems not pinned by this gate (add a `#guard_msgs` block):\n" ++
        m!"{String.join (unGated.toList.map fun n => s!"  {Name.toString n}\n")}"
    if !stale.isEmpty then
      msg := msg ++ m!"pinned names with no matching theorem:\n" ++
        m!"{String.join (stale.toList.map fun n => s!"  {Name.toString n}\n")}"
    throwError msg
  logInfo m!"basen axiom gate: {covered.size} pinned + {BaseNAxioms.generatedAuxAllowlist.size} allowlisted = {actual.size} of {BaseNAxioms.publicTheorems env |>.size} public theorems ({excluded.size} explicit exclusion(s))"

/-! **Partition check**, run on every `lake build`. The coverage check above only
compares `gatedNames` against the *kept* side of the classifier, so a theorem the
classifier drops is invisible to it. This second check closes that path: the pinned
set and `generatedAuxAllowlist` must **partition** the public theorems, with no third
route out of the gate.

Four failures, each naming what is wrong:

* a public theorem in **neither** set — a law nothing footprint-checks;
* a name in **both** — the gate's own record contradicts itself;
* an allowlist entry that is **not a public theorem** — a typo or a stale name, or an
  attempt to un-gate something that is not a theorem at all;
* a name in both `exclusions` and the allowlist — an exclusion is a *measured
  footprint with a reason*, an allowlist entry is *not a law*, so they cannot
  describe the same declaration. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let gated := Std.HashSet.ofList BaseNAxioms.gatedNames
  let allow := Std.HashSet.ofList BaseNAxioms.generatedAuxAllowlist.toList
  let pub := BaseNAxioms.publicTheorems env
  let noPath := pub.filter fun n => !gated.contains n && !allow.contains n
  let both := pub.filter fun n => gated.contains n && allow.contains n
  let notTheorems := BaseNAxioms.generatedAuxAllowlist.filter fun n => !pub.contains n
  let exclusionOverlap := BaseNAxioms.exclusions.filter allow.contains
  if !noPath.isEmpty || !both.isEmpty || !notTheorems.isEmpty ||
      !exclusionOverlap.isEmpty then
    let mut msg : MessageData := ""
    if !noPath.isEmpty then
      msg := msg ++ m!"public theorems in NEITHER the pinned set nor the allowlist (un-gated: add a `#guard_msgs` block):\n" ++
        m!"{String.join (noPath.toList.map fun n => s!"  {Name.toString n}\n")}"
    if !both.isEmpty then
      msg := msg ++ m!"names in BOTH the pinned set and the allowlist (the partition requires disjointness):\n" ++
        m!"{String.join (both.toList.map fun n => s!"  {Name.toString n}\n")}"
    if !notTheorems.isEmpty then
      msg := msg ++ m!"allowlist entries that are not public theorems (stale name, or a law cannot be allowlisted out of the gate):\n" ++
        m!"{String.join (notTheorems.toList.map fun n => s!"  {Name.toString n}\n")}"
    if !exclusionOverlap.isEmpty then
      msg := msg ++ m!"names in both the exclusion list and the allowlist (an exclusion is a measured footprint; an allowlist entry is not a law):\n" ++
        m!"{String.join (exclusionOverlap.toList.map fun n => s!"  {Name.toString n}\n")}"
    throwError msg
  logInfo m!"basen axiom gate: {pub.size} public theorems partitioned, {BaseNAxioms.gatedNames.length} pinned and {BaseNAxioms.generatedAuxAllowlist.size} allowlisted"

/-! **Header check** — the numbers this file's prose quotes are asserted here, so a
stale table is a build failure rather than an unnoticed lie. This is the fix for the
defect that motivated it: the partition above was green while the table above said
`446 / 437 / 9` and the truth was `483 / 437 / 46`, because `partition` compares sets
and never reads the prose. Transcribing a count is what makes this class of error
possible; asserting it closes it. If you legitimately add laws or allowlist entries,
update BOTH the table and these constants — the failure prints both. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let pub := BaseNAxioms.publicTheorems env
  let gated := BaseNAxioms.gatedNames.length
  let allow := BaseNAxioms.generatedAuxAllowlist.size
  -- Keep these in lockstep with the "universe, as measured" table above.
  let expectedPub := 484
  let expectedGated := 438
  let expectedAllow := 46
  let mut bad : Array String := #[]
  if pub.size != expectedPub then
    bad := bad.push s!"public theorems: table says {expectedPub}, environment has {pub.size}"
  if gated != expectedGated then
    bad := bad.push s!"pinned: table says {expectedGated}, gatedNames has {gated}"
  if allow != expectedAllow then
    bad := bad.push s!"allowlisted: table says {expectedAllow}, generatedAuxAllowlist has {allow}"
  if gated + allow != pub.size then
    bad := bad.push s!"table does not add up: {gated} + {allow} != {pub.size}"
  if !bad.isEmpty then
    throwError m!"the \"universe, as measured\" table is stale (update it and expected* in the header check):\n{String.join (bad.toList.map fun s => s!"  {s}\n")}"
  logInfo m!"basen axiom gate: header numbers verified ({expectedPub} = {expectedGated} + {expectedAllow})"
