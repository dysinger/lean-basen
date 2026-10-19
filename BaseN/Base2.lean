/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# BaseN.Base2

Binary encoding: one bit per `0`/`1` character, **eight** characters per byte,
**MSB-first** (bit 7 first, bit 0 last).  Eight bits always span exactly one
byte, so decoding needs no overflow check (unlike base8, which rejects `>255`).

Not an RFC encoding (RFC 4648 covers 16/32/64 only); semantics are defined by
this package's spec: "one bit per `0`/`1` char, 8 chars per byte, MSB-first".
Alphabet is ASCII `0`/`1` (48-49), all `< 256`.

This module expresses the base as a `codec` `Codec (List UInt8)` value
(`bitElem`), composed from `satisfy` (one guarded bit digit), `count 8`
(eight bits per byte block), and an `iso` that folds the eight bit values
into their byte (MSB-first `b₀·128 + b₁·64 + … + b₇`, with no overflow check
since eight bits span `0..255` exactly).  The unbounded run is the productive
repetition triple `relBit`/`decodeBit`/`encodeBit` over `bitElem`, whose roundtrip
law is the *inherited* `decodeRepeat_spec`/`encodeRepeat_rel` — no bespoke
`encode`/`decode` and no fresh induction.
-/

import BaseN.Common

namespace BaseN.Base2

open Codec
open BaseN.Common

/-! ## Digit-level arithmetic (`Nat`) -/

/-- `bitVal e` — the bit value of a `0`/`1` character, or `2` if invalid. -/
def bitVal (e : Nat) : Nat :=
  if e = 48 then 0 else if e = 49 then 1 else 2

/-- `valToBit b` — the `0`/`1` character for bit `b` (`b ∈ {0,1}`, else `49`). -/
def valToBit (b : Nat) : Nat :=
  if b = 0 then 48 else 49

/-- `bitValid e` — `true` iff `e` is `0` or `1`. -/
def bitValid (e : Nat) : Bool := decide (bitVal e ≤ 1)

theorem bitVal_valToBit (b : Nat) (hb : b ≤ 1) : bitVal (valToBit b) = b := by
  unfold bitVal valToBit
  by_cases h : b = 0
  · simp [h]
  · have hb1 : b = 1 := by omega
    simp [hb1]

theorem valToBit_valid (b : Nat) (hb : b ≤ 1) : bitValid (valToBit b) = true := by
  unfold bitValid
  apply decide_eq_true
  rw [bitVal_valToBit b hb]
  exact hb

theorem valToBit_lt_256 (b : Nat) (_hb : b ≤ 1) : valToBit b < 256 := by
  unfold valToBit
  by_cases h : b = 0 <;> simp [h] <;> omega

/-- `bitValid e = true` implies `bitVal e ≤ 1`. -/
theorem bitValid_of_decide (e : Nat) (h : bitValid e = true) : bitVal e ≤ 1 :=
  of_decide_eq_true (by simpa [bitValid] using h)

/-- When `e` is a valid bit digit, `valToBit (bitVal e) = e`. -/
theorem valToBit_bitVal_of_valid (e : Nat) (h : bitValid e = true) :
    valToBit (bitVal e) = e := by
  have hv : bitVal e ≤ 1 := bitValid_of_decide e h
  unfold bitVal valToBit
  by_cases h48 : e = 48
  · simp [h48]
  · by_cases h49 : e = 49
    · simp [h49]
    · have : bitVal e = 2 := by simp [bitVal, h48, h49]
      omega

/-- The `i`-th bit (0-indexed from the MSB) of `v`: `(v / 2^(7-i)) % 2`. -/
def bitAt (v : Nat) (i : Nat) : Nat := (v / 2 ^ (7 - i)) % 2

/-- The 8 MSB-first bits of `v` (values `0`/`1`). -/
def bitsOf (v : Nat) : List Nat :=
  [bitAt v 0, bitAt v 1, bitAt v 2, bitAt v 3, bitAt v 4, bitAt v 5, bitAt v 6, bitAt v 7]

/-- The value of 8 MSB-first bits `b0..b7`. -/
def bitsVal (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) : Nat :=
  b0 * 128 + b1 * 64 + b2 * 32 + b3 * 16 + b4 * 8 + b5 * 4 + b6 * 2 + b7

/-- Each `bitAt` of a byte is `≤ 1` (a bit). -/
theorem bitAt_le_one (v : Nat) (i : Nat) : bitAt v i ≤ 1 := by
  unfold bitAt
  omega

/-- `bitsVal (bitsOf v) = v` for a byte `v < 256`: the MSB-first bit
roundtrip at Nat level. -/
theorem bitsVal_bitsOf (v : Nat) (hv : v < 256) :
    bitsVal (bitAt v 0) (bitAt v 1) (bitAt v 2) (bitAt v 3)
      (bitAt v 4) (bitAt v 5) (bitAt v 6) (bitAt v 7) = v := by
  unfold bitsVal bitAt
  simp only [Nat.reducePow, Nat.reduceSub]
  omega

/-- Uniqueness of the binary decomposition: equal sums of bit octuples (each bit
`≤ 1`) give equal octuples. -/
theorem bits_decompose_unique
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat)
    (_ha0 : a0 ≤ 1) (_ha1 : a1 ≤ 1) (_ha2 : a2 ≤ 1) (_ha3 : a3 ≤ 1)
    (_ha4 : a4 ≤ 1) (_ha5 : a5 ≤ 1) (_ha6 : a6 ≤ 1) (_ha7 : a7 ≤ 1)
    (_hb0 : b0 ≤ 1) (_hb1 : b1 ≤ 1) (_hb2 : b2 ≤ 1) (_hb3 : b3 ≤ 1)
    (_hb4 : b4 ≤ 1) (_hb5 : b5 ≤ 1) (_hb6 : b6 ≤ 1) (_hb7 : b7 ≤ 1)
    (h : bitsVal a0 a1 a2 a3 a4 a5 a6 a7 = bitsVal b0 b1 b2 b3 b4 b5 b6 b7) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6 ∧ a7 = b7 := by
  have ha0' : a0 = b0 := by
    have hm := congrArg (fun x => x / 128) h
    unfold bitsVal at hm
    omega
  have ha1' : a1 = b1 := by
    have hm := congrArg (fun x => (x % 128) / 64) h
    unfold bitsVal at hm
    omega
  have ha2' : a2 = b2 := by
    have hm := congrArg (fun x => (x % 64) / 32) h
    unfold bitsVal at hm
    omega
  have ha3' : a3 = b3 := by
    have hm := congrArg (fun x => (x % 32) / 16) h
    unfold bitsVal at hm
    omega
  have ha4' : a4 = b4 := by
    have hm := congrArg (fun x => (x % 16) / 8) h
    unfold bitsVal at hm
    omega
  have ha5' : a5 = b5 := by
    have hm := congrArg (fun x => (x % 8) / 4) h
    unfold bitsVal at hm
    omega
  have ha6' : a6 = b6 := by
    have hm := congrArg (fun x => (x % 4) / 2) h
    unfold bitsVal at hm
    omega
  have ha7' : a7 = b7 := by
    have hm := congrArg (fun x => x % 2) h
    unfold bitsVal at hm
    omega
  exact ⟨ha0', ha1', ha2', ha3', ha4', ha5', ha6', ha7'⟩

/-! ## The block isomorphism -/

/-- The bit digit predicate over `UInt8`: holds iff `b` is a bit digit byte. -/
def bitDigit (b : UInt8) : Bool := bitValid b.toNat

/-- `toByte n` — the `UInt8` embedding. -/
def toByte (n : Nat) : UInt8 := UInt8.ofNat n

/-- `apply`: read eight bit digits and fold them into their byte (MSB-first). -/
def bitBlockApply (cs : List UInt8) : Option UInt8 :=
  match cs with
  | [d0, d1, d2, d3, d4, d5, d6, d7] =>
      if bitValid d0.toNat && bitValid d1.toNat && bitValid d2.toNat && bitValid d3.toNat
         && bitValid d4.toNat && bitValid d5.toNat && bitValid d6.toNat && bitValid d7.toNat then
        let n := bitsVal (bitVal d0.toNat) (bitVal d1.toNat) (bitVal d2.toNat) (bitVal d3.toNat)
                  (bitVal d4.toNat) (bitVal d5.toNat) (bitVal d6.toNat) (bitVal d7.toNat)
        some (UInt8.ofNat n)
      else none
  | _ => none

/-- `unapply`: write a byte as its eight MSB-first bit digits (always valid). -/
def bitBlockUnapply (b : UInt8) : Option (List UInt8) :=
  some [toByte (valToBit (bitAt b.toNat 0)),
        toByte (valToBit (bitAt b.toNat 1)),
        toByte (valToBit (bitAt b.toNat 2)),
        toByte (valToBit (bitAt b.toNat 3)),
        toByte (valToBit (bitAt b.toNat 4)),
        toByte (valToBit (bitAt b.toNat 5)),
        toByte (valToBit (bitAt b.toNat 6)),
        toByte (valToBit (bitAt b.toNat 7))]

/-- `toByte (valToBit d)` — the byte embedding of a bit digit, for `d ≤ 1`. -/
private theorem toByte_valToBit (b : Nat) (hb : b ≤ 1) :
    (toByte (valToBit b)).toNat = valToBit b := by
  unfold toByte
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToBit_lt_256 b hb)]

/-- `bitVal ((toByte (valToBit d)).toNat) = d` for `d ≤ 1`. -/
theorem bitVal_toByte_valToBit (d : Nat) (hd : d ≤ 1) :
    bitVal (toByte (valToBit d)).toNat = d := by
  rw [toByte_valToBit d hd]
  exact bitVal_valToBit d hd

/-- Each digit byte of `bitBlockUnapply b` is valid. -/
theorem bitDigit_valid_of_byte (b : UInt8) :
    bitValid (toByte (valToBit (bitAt b.toNat 0))).toNat = true ∧
    bitValid (toByte (valToBit (bitAt b.toNat 1))).toNat = true ∧
    bitValid (toByte (valToBit (bitAt b.toNat 2))).toNat = true ∧
    bitValid (toByte (valToBit (bitAt b.toNat 3))).toNat = true ∧
    bitValid (toByte (valToBit (bitAt b.toNat 4))).toNat = true ∧
    bitValid (toByte (valToBit (bitAt b.toNat 5))).toNat = true ∧
    bitValid (toByte (valToBit (bitAt b.toNat 6))).toNat = true ∧
    bitValid (toByte (valToBit (bitAt b.toNat 7))).toNat = true := by
  have h0 := bitAt_le_one b.toNat 0
  have h1 := bitAt_le_one b.toNat 1
  have h2 := bitAt_le_one b.toNat 2
  have h3 := bitAt_le_one b.toNat 3
  have h4 := bitAt_le_one b.toNat 4
  have h5 := bitAt_le_one b.toNat 5
  have h6 := bitAt_le_one b.toNat 6
  have h7 := bitAt_le_one b.toNat 7
  constructor
  · rw [toByte_valToBit (bitAt b.toNat 0) h0]; exact valToBit_valid (bitAt b.toNat 0) h0
  constructor
  · rw [toByte_valToBit (bitAt b.toNat 1) h1]; exact valToBit_valid (bitAt b.toNat 1) h1
  constructor
  · rw [toByte_valToBit (bitAt b.toNat 2) h2]; exact valToBit_valid (bitAt b.toNat 2) h2
  constructor
  · rw [toByte_valToBit (bitAt b.toNat 3) h3]; exact valToBit_valid (bitAt b.toNat 3) h3
  constructor
  · rw [toByte_valToBit (bitAt b.toNat 4) h4]; exact valToBit_valid (bitAt b.toNat 4) h4
  constructor
  · rw [toByte_valToBit (bitAt b.toNat 5) h5]; exact valToBit_valid (bitAt b.toNat 5) h5
  constructor
  · rw [toByte_valToBit (bitAt b.toNat 6) h6]; exact valToBit_valid (bitAt b.toNat 6) h6
  · rw [toByte_valToBit (bitAt b.toNat 7) h7]; exact valToBit_valid (bitAt b.toNat 7) h7

/-- `apply` is a left inverse of `unapply` on the byte domain. -/
theorem bitBlockApply_unapply (b : UInt8) :
    bitBlockApply [toByte (valToBit (bitAt b.toNat 0)),
                   toByte (valToBit (bitAt b.toNat 1)),
                   toByte (valToBit (bitAt b.toNat 2)),
                   toByte (valToBit (bitAt b.toNat 3)),
                   toByte (valToBit (bitAt b.toNat 4)),
                   toByte (valToBit (bitAt b.toNat 5)),
                   toByte (valToBit (bitAt b.toNat 6)),
                   toByte (valToBit (bitAt b.toNat 7))] = some b := by
  have hbv : b.toNat < 256 := UInt8.toNat_lt b
  have h0 := bitAt_le_one b.toNat 0
  have h1 := bitAt_le_one b.toNat 1
  have h2 := bitAt_le_one b.toNat 2
  have h3 := bitAt_le_one b.toNat 3
  have h4 := bitAt_le_one b.toNat 4
  have h5 := bitAt_le_one b.toNat 5
  have h6 := bitAt_le_one b.toNat 6
  have h7 := bitAt_le_one b.toNat 7
  rw [bitBlockApply]
  rw [bitVal_toByte_valToBit (bitAt b.toNat 0) h0,
      bitVal_toByte_valToBit (bitAt b.toNat 1) h1,
      bitVal_toByte_valToBit (bitAt b.toNat 2) h2,
      bitVal_toByte_valToBit (bitAt b.toNat 3) h3,
      bitVal_toByte_valToBit (bitAt b.toNat 4) h4,
      bitVal_toByte_valToBit (bitAt b.toNat 5) h5,
      bitVal_toByte_valToBit (bitAt b.toNat 6) h6,
      bitVal_toByte_valToBit (bitAt b.toNat 7) h7]
  have hvd := bitDigit_valid_of_byte b
  rw [hvd.1, hvd.2.1, hvd.2.2.1, hvd.2.2.2.1, hvd.2.2.2.2.1, hvd.2.2.2.2.2.1, hvd.2.2.2.2.2.2.1, hvd.2.2.2.2.2.2.2]
  have hh : (true && true && true && true && true && true && true && true) = true := by decide
  rw [hh]
  have hsum : bitAt b.toNat 0 * 128 + bitAt b.toNat 1 * 64 + bitAt b.toNat 2 * 32 + bitAt b.toNat 3 * 16
            + bitAt b.toNat 4 * 8 + bitAt b.toNat 5 * 4 + bitAt b.toNat 6 * 2 + bitAt b.toNat 7 = b.toNat :=
    bitsVal_bitsOf b.toNat hbv
  rw [show bitsVal (bitAt b.toNat 0) (bitAt b.toNat 1) (bitAt b.toNat 2) (bitAt b.toNat 3)
      (bitAt b.toNat 4) (bitAt b.toNat 5) (bitAt b.toNat 6) (bitAt b.toNat 7) =
      bitAt b.toNat 0 * 128 + bitAt b.toNat 1 * 64 + bitAt b.toNat 2 * 32 + bitAt b.toNat 3 * 16
      + bitAt b.toNat 4 * 8 + bitAt b.toNat 5 * 4 + bitAt b.toNat 6 * 2 + bitAt b.toNat 7 by rfl]
  rw [hsum]
  simp

/-- The inverse law of the bit block: `apply` and `unapply` are mutual inverses. -/
theorem bitBlockIso_law (cs : List UInt8) (b : UInt8) :
    bitBlockApply cs = some b ↔ bitBlockUnapply b = some cs := by
  constructor
  · intro h
    cases cs with
    | nil => simp [bitBlockApply] at h
    | cons d0 rest =>
      cases rest with
      | nil => simp [bitBlockApply] at h
      | cons d1 rest2 =>
        cases rest2 with
        | nil => simp [bitBlockApply] at h
        | cons d2 rest3 =>
          cases rest3 with
          | nil => simp [bitBlockApply] at h
          | cons d3 rest4 =>
            cases rest4 with
            | nil => simp [bitBlockApply] at h
            | cons d4 rest5 =>
              cases rest5 with
              | nil => simp [bitBlockApply] at h
              | cons d5 rest6 =>
                cases rest6 with
                | nil => simp [bitBlockApply] at h
                | cons d6 rest7 =>
                  cases rest7 with
                  | nil => simp [bitBlockApply] at h
                  | cons d7 rest8 =>
                    cases rest8 with
                    | nil =>
                        rw [bitBlockApply] at h
                        by_cases hv : bitValid d0.toNat && bitValid d1.toNat && bitValid d2.toNat && bitValid d3.toNat
                            && bitValid d4.toNat && bitValid d5.toNat && bitValid d6.toNat && bitValid d7.toNat
                        · simp only [hv, ite_true] at h
                          have hb_eq : UInt8.ofNat (bitsVal (bitVal d0.toNat) (bitVal d1.toNat) (bitVal d2.toNat) (bitVal d3.toNat)
                              (bitVal d4.toNat) (bitVal d5.toNat) (bitVal d6.toNat) (bitVal d7.toNat)) = b := by
                            exact Option.some.inj h
                          -- decompose hv into per-digit validity
                          have hv' : ((((((bitValid d0.toNat = true ∧ bitValid d1.toNat = true) ∧
                              bitValid d2.toNat = true) ∧ bitValid d3.toNat = true) ∧
                              bitValid d4.toNat = true) ∧ bitValid d5.toNat = true) ∧
                              bitValid d6.toNat = true) ∧ bitValid d7.toNat = true := by
                            simpa only [Bool.and_eq_true_iff] using hv
                          have hvd0 : bitValid d0.toNat = true := hv'.1.1.1.1.1.1.1
                          have hvd1 : bitValid d1.toNat = true := hv'.1.1.1.1.1.1.2
                          have hvd2 : bitValid d2.toNat = true := hv'.1.1.1.1.1.2
                          have hvd3 : bitValid d3.toNat = true := hv'.1.1.1.1.2
                          have hvd4 : bitValid d4.toNat = true := hv'.1.1.1.2
                          have hvd5 : bitValid d5.toNat = true := hv'.1.1.2
                          have hvd6 : bitValid d6.toNat = true := hv'.1.2
                          have hvd7 : bitValid d7.toNat = true := hv'.2
                          have v0le := bitValid_of_decide d0.toNat hvd0
                          have v1le := bitValid_of_decide d1.toNat hvd1
                          have v2le := bitValid_of_decide d2.toNat hvd2
                          have v3le := bitValid_of_decide d3.toNat hvd3
                          have v4le := bitValid_of_decide d4.toNat hvd4
                          have v5le := bitValid_of_decide d5.toNat hvd5
                          have v6le := bitValid_of_decide d6.toNat hvd6
                          have v7le := bitValid_of_decide d7.toNat hvd7
                          have hb : b.toNat = bitsVal (bitVal d0.toNat) (bitVal d1.toNat) (bitVal d2.toNat) (bitVal d3.toNat)
                              (bitVal d4.toNat) (bitVal d5.toNat) (bitVal d6.toNat) (bitVal d7.toNat) := by
                            have hbt := congrArg UInt8.toNat hb_eq
                            rw [UInt8.toNat_ofNat'] at hbt
                            have hbnd : bitsVal (bitVal d0.toNat) (bitVal d1.toNat) (bitVal d2.toNat) (bitVal d3.toNat)
                                (bitVal d4.toNat) (bitVal d5.toNat) (bitVal d6.toNat) (bitVal d7.toNat) < 256 := by
                              unfold bitsVal
                              omega
                            rw [Nat.mod_eq_of_lt hbnd] at hbt
                            exact hbt.symm
                          have hdev : bitVal d0.toNat = bitAt b.toNat 0 ∧ bitVal d1.toNat = bitAt b.toNat 1 ∧
                                      bitVal d2.toNat = bitAt b.toNat 2 ∧ bitVal d3.toNat = bitAt b.toNat 3 ∧
                                      bitVal d4.toNat = bitAt b.toNat 4 ∧ bitVal d5.toNat = bitAt b.toNat 5 ∧
                                      bitVal d6.toNat = bitAt b.toNat 6 ∧ bitVal d7.toNat = bitAt b.toNat 7 := by
                            have hbit0 := bitAt_le_one b.toNat 0
                            have hbit1 := bitAt_le_one b.toNat 1
                            have hbit2 := bitAt_le_one b.toNat 2
                            have hbit3 := bitAt_le_one b.toNat 3
                            have hbit4 := bitAt_le_one b.toNat 4
                            have hbit5 := bitAt_le_one b.toNat 5
                            have hbit6 := bitAt_le_one b.toNat 6
                            have hbit7 := bitAt_le_one b.toNat 7
                            have hb' : bitsVal (bitVal d0.toNat) (bitVal d1.toNat) (bitVal d2.toNat) (bitVal d3.toNat)
                                (bitVal d4.toNat) (bitVal d5.toNat) (bitVal d6.toNat) (bitVal d7.toNat)
                              = bitsVal (bitAt b.toNat 0) (bitAt b.toNat 1) (bitAt b.toNat 2) (bitAt b.toNat 3)
                                (bitAt b.toNat 4) (bitAt b.toNat 5) (bitAt b.toNat 6) (bitAt b.toNat 7) := by
                              rw [bitsVal_bitsOf b.toNat (UInt8.toNat_lt b)]
                              exact hb.symm
                            exact bits_decompose_unique
                              (bitVal d0.toNat) (bitVal d1.toNat) (bitVal d2.toNat) (bitVal d3.toNat)
                              (bitVal d4.toNat) (bitVal d5.toNat) (bitVal d6.toNat) (bitVal d7.toNat)
                              (bitAt b.toNat 0) (bitAt b.toNat 1) (bitAt b.toNat 2) (bitAt b.toNat 3)
                              (bitAt b.toNat 4) (bitAt b.toNat 5) (bitAt b.toNat 6) (bitAt b.toNat 7)
                              v0le v1le v2le v3le v4le v5le v6le v7le
                              hbit0 hbit1 hbit2 hbit3 hbit4 hbit5 hbit6 hbit7
                              hb'
                          rw [bitBlockUnapply]
                          have hd0 : d0.toNat = valToBit (bitVal d0.toNat) :=
                            (valToBit_bitVal_of_valid d0.toNat hvd0).symm
                          have hd1 : d1.toNat = valToBit (bitVal d1.toNat) :=
                            (valToBit_bitVal_of_valid d1.toNat hvd1).symm
                          have hd2 : d2.toNat = valToBit (bitVal d2.toNat) :=
                            (valToBit_bitVal_of_valid d2.toNat hvd2).symm
                          have hd3 : d3.toNat = valToBit (bitVal d3.toNat) :=
                            (valToBit_bitVal_of_valid d3.toNat hvd3).symm
                          have hd4 : d4.toNat = valToBit (bitVal d4.toNat) :=
                            (valToBit_bitVal_of_valid d4.toNat hvd4).symm
                          have hd5 : d5.toNat = valToBit (bitVal d5.toNat) :=
                            (valToBit_bitVal_of_valid d5.toNat hvd5).symm
                          have hd6 : d6.toNat = valToBit (bitVal d6.toNat) :=
                            (valToBit_bitVal_of_valid d6.toNat hvd6).symm
                          have hd7 : d7.toNat = valToBit (bitVal d7.toNat) :=
                            (valToBit_bitVal_of_valid d7.toNat hvd7).symm
                          rw [← hdev.1, ← hdev.2.1, ← hdev.2.2.1, ← hdev.2.2.2.1,
                              ← hdev.2.2.2.2.1, ← hdev.2.2.2.2.2.1, ← hdev.2.2.2.2.2.2.1, ← hdev.2.2.2.2.2.2.2]
                          rw [← hd0, ← hd1, ← hd2, ← hd3, ← hd4, ← hd5, ← hd6, ← hd7]
                          simp [toByte]
                        · simp [hv] at h
                    | cons _ _ => simp [bitBlockApply] at h
  · intro h
    rw [bitBlockUnapply] at h
    cases h
    exact bitBlockApply_unapply b

/-- The eight-bit block ↔ one byte partial isomorphism. -/
def bitBlockIso : Iso (List UInt8) UInt8 :=
  { apply := bitBlockApply, unapply := bitBlockUnapply, law := bitBlockIso_law }

/-- The base2 element: eight bit digit bytes grouped into one byte. -/
def bitElem : Codec UInt8 := Codec.iso bitBlockIso (count 8 (Codec.satisfy bitDigit))

/-- `bitElem` is productive, hence a `ConsumesByte` witness. -/
theorem bitConsumesByte : ConsumesByte bitElem := by
  unfold bitElem
  rw [← productive_iff_consumesByte (Codec.iso bitBlockIso (count 8 (Codec.satisfy bitDigit)))]
  apply Productive_iso bitBlockIso (count 8 (Codec.satisfy bitDigit))
  rw [show 8 = 7 + 1 by rfl]
  exact Productive_count_satisfy_succ bitDigit 7

/-- The base2 decoder: productive repetition over `bitElem`. -/
def decodeBit {n : Nat} (s : Bytes n) : List (List UInt8 × Suffix n) :=
  decodeRepeat bitElem bitConsumesByte n s

/-- The base2 encoder: repeat `bitElem` over the byte list. -/
def encodeBit (bs : List UInt8) : Option (Sigma fun n => Bytes n) :=
  encodeRepeat bitElem bs

/-- The base2 relation: `relRepeat` over `Rel bitElem`. -/
def relBit : List UInt8 → (n : Nat) → Bytes n → Prop :=
  relRepeat (Rel bitElem)

/-! ## Unambiguity and the inherited roundtrip law -/

/-- `bitElem` is unambiguous: the decoded byte is uniquely determined. -/
theorem bitElem_unambiguous : Unambiguous bitElem := by
  unfold bitElem
  apply Unambiguous_iso bitBlockIso (count 8 (Codec.satisfy bitDigit))
  exact count_satisfy_unambiguous bitDigit 8

/-- `Rel bitElem x s` pins the byte length: `n = 8`. -/
theorem Rel_bitElem_len (x : UInt8) {n : Nat} (s : Bytes n) :
    Rel bitElem x s → n = 8 := by
  intro h
  unfold bitElem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, _, hc⟩
  exact Rel_count_satisfy_len bitDigit 8 a s hc

/-- The base2 relation is unambiguous. -/
theorem relBit_unambiguous : relUnambiguous relBit := by
  intro a b n s ha hb
  dsimp [relBit] at ha hb
  induction a generalizing b n s with
  | nil =>
      rw [relRepeat_nil] at ha
      subst n
      cases b with
      | nil => rfl
      | cons y ys =>
          rw [relRepeat_cons] at hb
          rcases hb with ⟨m, hm, s₁, s₂, hs, hy, _⟩
          have hlen : m = 8 := Rel_bitElem_len y s₁ hy
          have hm0 : m = 0 := by omega
          omega
  | cons x xs ih =>
      cases b with
      | nil =>
          rw [relRepeat_nil] at hb
          rw [relRepeat_cons] at ha
          rcases ha with ⟨mx, hmx, s₁x, s₂x, hsx, hx, hxs⟩
          have hlen : mx = 8 := Rel_bitElem_len x s₁x hx
          subst n
          have hm0 : mx = 0 := by omega
          omega
      | cons y ys =>
          rw [relRepeat_cons] at ha hb
          rcases ha with ⟨mx, hmx, s₁x, s₂x, hsx, hx, hxs⟩
          rcases hb with ⟨my, hmy, s₁y, s₂y, hsy, hy, hys⟩
          have hlx : mx = 8 := Rel_bitElem_len x s₁x hx
          have hly : my = 8 := Rel_bitElem_len y s₁y hy
          subst mx
          subst my
          have hpre : s₁x = s₁y := by
            apply Bytes.ext
            intro i
            have hin : i.val < n := Nat.lt_of_lt_of_le i.isLt hmx
            have hx' : s ⟨i.val, hin⟩ = s₁x i := by
              rw [hsx]
              exact splice_prefix_read hmx s₁x s₂x ⟨i.val, hin⟩ i.isLt
            have hy' : s ⟨i.val, hin⟩ = s₁y i := by
              rw [hsy]
              exact splice_prefix_read hmy s₁y s₂y ⟨i.val, hin⟩ i.isLt
            exact hx'.symm.trans hy'
          have htaily : s₂x = s₂y := by
            rw [← bdrop_splice hmx s₁x s₂x, ← bdrop_splice hmy s₁y s₂y]
            congr 1
            rw [← hsx]
            rw [hsy]
          have hhead : x = y := by
            exact bitElem_unambiguous s₁x hx (by rw [hpre]; exact hy)
          have htail : xs = ys := by
            exact ih s₂x hxs (by simpa [htaily] using hys)
          rw [hhead, htail]

/-- Full-consumption decode is unambiguous for `bitElem`. -/
theorem bitDecodeFull_unambiguous {x y : List UInt8} {n : Nat} (s : Bytes n) :
    (x, Suffix.empty n) ∈ decodeRepeat bitElem bitConsumesByte n s →
    (y, Suffix.empty n) ∈ decodeRepeat bitElem bitConsumesByte n s → x = y := by
  intro hx hy
  rcases (decodeRepeat_spec bitElem bitConsumesByte x n s (Suffix.empty n)).1 hx with ⟨s₀x, hsx, hrx⟩
  rcases (decodeRepeat_spec bitElem bitConsumesByte y n s (Suffix.empty n)).1 hy with ⟨s₀y, hsy, hry⟩
  have hs₀ : s₀x = s₀y := by
    have hpre : (Suffix.empty n).prepend s₀x = (Suffix.empty n).prepend s₀y := by
      exact hsx.symm.trans hsy
    exact prepend_prefix_eq (Suffix.empty n) s₀x s₀y hpre
  exact relBit_unambiguous s₀x hrx (by rw [hs₀]; exact hry)

/-- The base2 roundtrip law. `[propext, Quot.sound]`-only. -/
theorem roundtrip (bs : List UInt8) {n : Nat} {s : Bytes n} :
    encodeBit bs = some ⟨n, s⟩ → decodeFull bitElem bitConsumesByte n s = some bs := by
  intro he
  have hrel : relRepeat (Rel bitElem) bs n s := encodeRepeat_rel bitElem bs he
  have hmem : (bs, Suffix.empty n) ∈ decodeRepeat bitElem bitConsumesByte n s := by
    refine (decodeRepeat_spec bitElem bitConsumesByte bs n s (Suffix.empty n)).2 ⟨
      cast (congrArg Bytes (Nat.sub_zero n).symm) s, ?_, ?_⟩
    · exact (prepend_empty_eq s).symm
    · exact (relRepeat_cast (Rel bitElem) bs (Nat.sub_zero n).symm s).2 hrel
  exact (decodeFull_spec bitElem bitConsumesByte (fun {x y} {m} (t : Bytes m) =>
    bitDecodeFull_unambiguous (s := t)) s bs).2 hmem

end BaseN.Base2
