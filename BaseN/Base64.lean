/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# BaseN.Base64

RFC 4648 §4 base64 encoding.  `valToB64` maps a 6-bit value to the RFC 4648
alphabet (`A-Z` 65-90, `a-z` 97-122, `0-9` 48-57, `+` 43, `/` 47); `b64ToVal`
inverts it (returns `64` on an invalid byte, mirroring the "`invalid > max`"
convention of the other bases).  Padding is `=` (61).  Each 3-byte block encodes
to 4 characters; a 1-byte tail encodes to 2 chars + `==`, a 2-byte tail to 3
chars + `=`.

All digit math is `Nat`-level; the alphabet is ASCII, every produced byte is
`< 256`.  `[propext, Quot.sound]`-only, zero `sorry`.
-/

import BaseN.Common

namespace BaseN.Base64

set_option linter.unnecessarySimpa false

open Codec
open BaseN.Common

/-- `valToB64 i` — the base64 alphabet character for `i ∈ {0..63}`. -/
def valToB64 (i : Nat) : Nat :=
  if i ≤ 25 then 65 + i
  else if i ≤ 51 then 97 + i - 26
  else if i ≤ 61 then 48 + i - 52
  else if i = 62 then 43
  else 47

/-- `b64ToVal e` — the 6-bit value of a base64 character, or `64` if invalid. -/
def b64ToVal (e : Nat) : Nat :=
  if e ≤ 90 then
    if 65 ≤ e then e - 65
    else
      if e ≤ 57 then
        if 48 ≤ e then e - 48 + 52
        else if e = 43 then 62 else if e = 47 then 63 else 64
      else 64
  else
    if 97 ≤ e then
      if e ≤ 122 then e - 97 + 26 else 64
    else 64

/-- `b64Valid e` — `true` iff `e` is a base64 alphabet character. -/
def b64Valid (e : Nat) : Bool := decide (b64ToVal e ≤ 63)

/-- `toByte n` — the `UInt8` embedding. -/
def toByte (n : Nat) : UInt8 := UInt8.ofNat n

/-- `b64ToVal (valToB64 i) = i` — the 6-bit ↔ char bijection. -/
theorem b64ToVal_valToB64 (i : Nat) (hi : i ≤ 63) :
    b64ToVal (valToB64 i) = i := by
  unfold b64ToVal valToB64
  by_cases h25 : i ≤ 25
  · simp only [h25, ite_true]
    have h1 : 65 + i ≤ 90 := by omega
    have h2 : 65 ≤ 65 + i := by omega
    simp only [h1, ite_true, h2, ite_true]
    omega
  · simp only [h25, ite_false]
    by_cases h51 : i ≤ 51
    · simp only [h51, ite_true]
      have hle90 : ¬ 97 + i - 26 ≤ 90 := by omega
      simp only [hle90, ite_false]
      have h97 : 97 ≤ 97 + i - 26 := by omega
      have h122 : 97 + i - 26 ≤ 122 := by omega
      simp only [h97, ite_true, h122, ite_true]
      omega
    · simp only [h51, ite_false]
      by_cases h61 : i ≤ 61
      · simp only [h61, ite_true]
        have hle90 : 48 + i - 52 ≤ 90 := by omega
        simp only [hle90, ite_true]
        have hn65 : ¬ 65 ≤ 48 + i - 52 := by omega
        simp only [hn65, ite_false]
        have hle57 : 48 + i - 52 ≤ 57 := by omega
        simp only [hle57, ite_true]
        have h48 : 48 ≤ 48 + i - 52 := by omega
        simp only [h48, ite_true]
        omega
      · simp only [h61, ite_false]
        rcases (show i = 62 ∨ i = 63 by omega) with rfl | rfl <;> decide

/-- `valToB64 i` produces a valid base64 character. -/
theorem valToB64_valid (i : Nat) (hi : i ≤ 63) : b64Valid (valToB64 i) = true := by
  unfold b64Valid
  apply decide_eq_true
  rw [b64ToVal_valToB64 i hi]
  exact hi

/-- `valToB64 i ≠ 61` — never the padding byte `=`. -/
theorem valToB64_not_pad (i : Nat) (hi : i ≤ 63) : valToB64 i ≠ 61 := by
  unfold valToB64
  by_cases h25 : i ≤ 25
  · simp only [h25, ite_true]; omega
  · by_cases h51 : i ≤ 51
    · simp only [h25, ite_false, h51, ite_true]; omega
    · by_cases h61 : i ≤ 61
      · simp only [h25, ite_false, h51, ite_false, h61, ite_true]; omega
      · simp only [h25, ite_false, h51, ite_false, h61, ite_false]
        rcases (show i = 62 ∨ i = 63 by omega) with rfl | rfl <;> decide

/-- `valToB64 i < 256` — every base64 character is a single byte. -/
theorem valToB64_lt_256 (i : Nat) (_hi : i ≤ 63) : valToB64 i < 256 := by
  unfold valToB64
  by_cases h25 : i ≤ 25
  · simp only [h25, ite_true]; omega
  · by_cases h51 : i ≤ 51
    · simp only [h25, ite_false, h51, ite_true]; omega
    · by_cases h61 : i ≤ 61
      · simp only [h25, ite_false, h51, ite_false, h61, ite_true]; omega
      · simp only [h25, ite_false, h51, ite_false, h61, ite_false]
        rcases (show i = 62 ∨ i = 63 by omega) with rfl | rfl <;> decide

-- Byte extraction identities (the structural inverses)

/-- `byte0 v0 v1` — first byte reconstruction from the two leading chars. -/
theorem byte0 (v0 v1 : Nat) (_hv0 : v0 < 256) (hv1 : v1 < 256) :
    (v0 / 4) * 4 + ((v0 % 4) * 16 + v1 / 16) / 16 = v0 := by
  have hd : v1 / 16 < 16 := by omega
  have hm : v0 % 4 < 16 := by omega
  have hdiv := Nat.add_mul_div_left (v1 / 16) (v0 % 4) (by decide : 0 < 16)
  -- hdiv : (v1/16 + 16*(v0%4)) / 16 = (v1/16)/16 + v0%4
  have hz : v1 / 16 / 16 = 0 := Nat.div_eq_of_lt hd
  have hsum : 4 * (v0 / 4) + v0 % 4 = v0 := by
    have h := Nat.div_add_mod v0 4
    simpa [Nat.mul_comm] using h
  omega

/-- `byte1 v0 v1` — second byte reconstruction from the 2-byte tail chars. -/
theorem byte1 (v0 v1 : Nat) (_hv0 : v0 < 256) (hv1 : v1 < 256) :
    ((v0 % 4) * 16 + v1 / 16) % 16 * 16 + ((v1 % 16) * 4) / 4 = v1 := by
  have hmod : ((v0 % 4) * 16 + v1 / 16) % 16 = v1 / 16 := by
    have h := Nat.add_mul_mod_self_right (v0 % 4) (v1 / 16) 16
    -- h : ((v0%4) + 16 * (v1/16)) % 16 = (v0%4) % 16
    omega
  have hdiv4 : ((v1 % 16) * 4) / 4 = v1 % 16 := Nat.mul_div_left (v1 % 16) (by decide : 0 < 4)
  have hsum : 16 * (v1 / 16) + v1 % 16 = v1 := by
    have h := Nat.div_add_mod v1 16
    simpa [Nat.mul_comm] using h
  omega

/-- `byte2 v1 v2` — third byte reconstruction from the 3-byte block chars. -/
theorem byte2 (v1 v2 : Nat) (_hv1 : v1 < 256) (hv2 : v2 < 256) :
    ((v1 % 16) * 4 + v2 / 64) % 4 * 64 + (v2 % 64) = v2 := by
  have hmod : ((v1 % 16) * 4 + v2 / 64) % 4 = v2 / 64 := by
    have h := Nat.add_mul_mod_self_left (v1 % 16) (v2 / 64) 4
    -- h : ((v1%16) + 4 * (v2/64)) % 4 = (v1%16) % 4
    omega
  have hsum : 64 * (v2 / 64) + v2 % 64 = v2 := by
    have h := Nat.div_add_mod v2 64
    simpa [Nat.mul_comm] using h
  omega
-- character reconstruction

/-- `b64Valid e = true` implies `b64ToVal e ≤ 63`. -/
theorem b64Valid_of_decide (e : Nat) (h : b64Valid e = true) : b64ToVal e ≤ 63 :=
  of_decide_eq_true (by simpa [b64Valid] using h)

/-- `(toByte (valToB64 i)).toNat = valToB64 i`. -/
private theorem toByte_valToB64 (i : Nat) (hi : i ≤ 63) :
    (toByte (valToB64 i)).toNat = valToB64 i := by
  unfold toByte
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToB64_lt_256 i hi)]

/-- `valToB64 (b64ToVal e) = e` when `e` is a valid base64 character. -/
theorem valToB64_b64ToVal_of_valid (e : Nat) (h : b64Valid e = true) :
    valToB64 (b64ToVal e) = e := by
  have hv : b64ToVal e ≤ 63 := b64Valid_of_decide e h
  by_cases hle90 : e ≤ 90
  · by_cases hge65 : 65 ≤ e
    · have hb : b64ToVal e = e - 65 := by simp [b64ToVal, hle90, hge65]
      rw [hb]
      have hle25 : e - 65 ≤ 25 := by omega
      simp [valToB64, hle25]
      omega
    · by_cases hle57 : e ≤ 57
      · by_cases hge48 : 48 ≤ e
        · have hb : b64ToVal e = e - 48 + 52 := by simp [b64ToVal, hle90, hge65, hle57, hge48]
          rw [hb]
          have hnle25 : ¬ e - 48 + 52 ≤ 25 := by omega
          have hnle51 : ¬ e - 48 + 52 ≤ 51 := by omega
          have hle61 : e - 48 + 52 ≤ 61 := by omega
          simp [valToB64, hnle25, hnle51, hle61]
          omega
        · by_cases he43 : e = 43
          · have hb : b64ToVal e = 62 := by simp [b64ToVal, he43]
            rw [hb]
            rw [show valToB64 62 = 43 by decide]
            exact he43.symm
          · by_cases he47 : e = 47
            · have hb : b64ToVal e = 63 := by simp [b64ToVal, he47]
              rw [hb]
              rw [show valToB64 63 = 47 by decide]
              exact he47.symm
            · have hb : b64ToVal e = 64 := by simp [b64ToVal, hle90, hge65, hle57, hge48, he43, he47]
              rw [hb] at hv
              omega
      · have hb : b64ToVal e = 64 := by simp [b64ToVal, hle90, hge65, hle57]
        rw [hb] at hv
        omega
  · by_cases hge97 : 97 ≤ e
    · by_cases hle122 : e ≤ 122
      · have hb : b64ToVal e = e - 97 + 26 := by simp [b64ToVal, hle90, hge97, hle122]
        rw [hb]
        have hnle25 : ¬ e - 97 + 26 ≤ 25 := by omega
        have hle51 : e - 97 + 26 ≤ 51 := by omega
        simp [valToB64, hnle25, hle51]
        omega
      · have hb : b64ToVal e = 64 := by simp [b64ToVal, hle90, hge97, hle122]
        rw [hb] at hv
        omega
    · have hb : b64ToVal e = 64 := by simp [b64ToVal, hle90, hge97]
      rw [hb] at hv
      omega

-- pad predicate

/-- Base64 alphabet character (no `=` pad). -/
def b64Char (b : UInt8) : Bool := b64Valid b.toNat

/-- Base64 alphabet character or the `=` pad. -/
def b64OrPad (b : UInt8) : Bool := b64Valid b.toNat || (b.toNat = 61)

-- block unapply (encode) / lenient decode / apply (re-encode-check)

/-- `b64BlockUnapply bs` — encode 1–3 bytes as exactly 4 base64 chars (with `=` pad). -/
def b64BlockUnapply (bs : List UInt8) : Option (List UInt8) :=
  match bs with
  | [v0] => some [toByte (valToB64 (v0.toNat / 4)), toByte (valToB64 ((v0.toNat % 4) * 16)), 61, 61]
  | [v0, v1] => some [toByte (valToB64 (v0.toNat / 4)), toByte (valToB64 ((v0.toNat % 4) * 16 + v1.toNat / 16)),
                      toByte (valToB64 ((v1.toNat % 16) * 4)), 61]
  | [v0, v1, v2] => some [toByte (valToB64 (v0.toNat / 4)), toByte (valToB64 ((v0.toNat % 4) * 16 + v1.toNat / 16)),
                          toByte (valToB64 ((v1.toNat % 16) * 4 + v2.toNat / 64)), toByte (valToB64 (v2.toNat % 64))]
  | _ => none

/-- `b64BlockDecodeLenient cs` — decode exactly 4 base64 chars into 1–3 bytes,
accepting any pad shape (no dropped-bit strictness). -/
def b64BlockDecodeLenient (cs : List UInt8) : Option (List UInt8) :=
  match cs with
  | [c0, c1, c2, c3] =>
      if c0.toNat = 61 || c1.toNat = 61 then none
      else if ¬ b64Valid c0.toNat || ¬ b64Valid c1.toNat then none
      else
        let v0 := b64ToVal c0.toNat
        let v1 := b64ToVal c1.toNat
        let b0 := v0 * 4 + v1 / 16
        if c2.toNat = 61 && c3.toNat = 61 then some [toByte b0]
        else if c2.toNat = 61 then none
        else if ¬ b64Valid c2.toNat then none
        else
          let v2 := b64ToVal c2.toNat
          let b1 := (v1 % 16) * 16 + v2 / 4
          if c3.toNat = 61 then some [toByte b0, toByte b1]
          else if ¬ b64Valid c3.toNat then none
          else
            let v3 := b64ToVal c3.toNat
            let b2 := (v2 % 4) * 64 + v3
            some [toByte b0, toByte b1, toByte b2]
  | _ => none

/-- `b64BlockApply cs` — decode 4 chars and verify the result re-encodes to `cs`
(canonical input only). Makes `apply`/`unapply` a genuine bijection. -/
def b64BlockApply (cs : List UInt8) : Option (List UInt8) :=
  (b64BlockDecodeLenient cs).bind fun bs =>
    if b64BlockUnapply bs = some cs then some bs else none

-- forward: lenient decode∘encode = id for a single block

/-- 1-byte tail. -/
theorem b64BlockDecodeLenient_unapply_single (b0 : UInt8) :
    b64BlockDecodeLenient [toByte (valToB64 (b0.toNat / 4)), toByte (valToB64 ((b0.toNat % 4) * 16)), 61, 61] = some [b0] := by
  have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
  have h0 : b0.toNat / 4 ≤ 63 := by omega
  have h1 : (b0.toNat % 4) * 16 ≤ 63 := by omega
  rw [b64BlockDecodeLenient]
  rw [toByte_valToB64 (b0.toNat / 4) h0, toByte_valToB64 ((b0.toNat % 4) * 16) h1]
  have hnp0 : valToB64 (b0.toNat / 4) ≠ 61 := valToB64_not_pad (b0.toNat / 4) h0
  have hnp1 : valToB64 ((b0.toNat % 4) * 16) ≠ 61 := valToB64_not_pad ((b0.toNat % 4) * 16) h1
  have hvd0 : b64Valid (valToB64 (b0.toNat / 4)) = true := valToB64_valid (b0.toNat / 4) h0
  have hvd1 : b64Valid (valToB64 ((b0.toNat % 4) * 16)) = true := valToB64_valid ((b0.toNat % 4) * 16) h1
  rw [hvd0, hvd1]
  rw [b64ToVal_valToB64 (b0.toNat / 4) h0, b64ToVal_valToB64 ((b0.toNat % 4) * 16) h1]
  simp only [hnp0, hnp1]
  have hb0v : (b0.toNat / 4) * 4 + (((b0.toNat % 4) * 16) / 16) = b0.toNat :=
    byte0 b0.toNat 0 hb0 (by decide)
  rw [hb0v]
  simp [toByte, UInt8.ofNat_toNat]

/-- 2-byte tail. -/
theorem b64BlockDecodeLenient_unapply_pair (b0 b1 : UInt8) :
    b64BlockDecodeLenient [toByte (valToB64 (b0.toNat / 4)), toByte (valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16)),
                           toByte (valToB64 ((b1.toNat % 16) * 4)), 61] = some [b0, b1] := by
  have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
  have hb1 : b1.toNat < 256 := UInt8.toNat_lt b1
  have h0 : b0.toNat / 4 ≤ 63 := by omega
  have h1 : (b0.toNat % 4) * 16 + b1.toNat / 16 ≤ 63 := by omega
  have h2 : (b1.toNat % 16) * 4 ≤ 63 := by omega
  rw [b64BlockDecodeLenient]
  rw [toByte_valToB64 (b0.toNat / 4) h0, toByte_valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16) h1,
      toByte_valToB64 ((b1.toNat % 16) * 4) h2]
  have hnp0 : valToB64 (b0.toNat / 4) ≠ 61 := valToB64_not_pad _ h0
  have hnp1 : valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16) ≠ 61 := valToB64_not_pad _ h1
  have hnp2 : valToB64 ((b1.toNat % 16) * 4) ≠ 61 := valToB64_not_pad _ h2
  have hvd0 : b64Valid (valToB64 (b0.toNat / 4)) = true := valToB64_valid _ h0
  have hvd1 : b64Valid (valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16)) = true := valToB64_valid _ h1
  have hvd2 : b64Valid (valToB64 ((b1.toNat % 16) * 4)) = true := valToB64_valid _ h2
  rw [hvd0, hvd1]
  rw [b64ToVal_valToB64 (b0.toNat / 4) h0, b64ToVal_valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16) h1]
  simp only [hnp0, hnp1]
  have hb0v : (b0.toNat / 4) * 4 + (((b0.toNat % 4) * 16 + b1.toNat / 16) / 16) = b0.toNat := byte0 b0.toNat b1.toNat hb0 hb1
  rw [hb0v]
  rw [hvd2]
  rw [b64ToVal_valToB64 ((b1.toNat % 16) * 4) h2]
  simp only [hnp2]
  have hb1v : (((b0.toNat % 4) * 16 + b1.toNat / 16) % 16) * 16 + (((b1.toNat % 16) * 4) / 4) = b1.toNat := byte1 b0.toNat b1.toNat hb0 hb1
  rw [hb1v]
  simp [toByte, UInt8.ofNat_toNat]

/-- 3-byte block. -/
theorem b64BlockDecodeLenient_unapply_triple (b0 b1 b2 : UInt8) :
    b64BlockDecodeLenient [toByte (valToB64 (b0.toNat / 4)), toByte (valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16)),
                           toByte (valToB64 ((b1.toNat % 16) * 4 + b2.toNat / 64)), toByte (valToB64 (b2.toNat % 64))] = some [b0, b1, b2] := by
  have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
  have hb1 : b1.toNat < 256 := UInt8.toNat_lt b1
  have hb2 : b2.toNat < 256 := UInt8.toNat_lt b2
  have h0 : b0.toNat / 4 ≤ 63 := by omega
  have h1 : (b0.toNat % 4) * 16 + b1.toNat / 16 ≤ 63 := by omega
  have h2 : (b1.toNat % 16) * 4 + b2.toNat / 64 ≤ 63 := by omega
  have h3 : b2.toNat % 64 ≤ 63 := by omega
  rw [b64BlockDecodeLenient]
  rw [toByte_valToB64 (b0.toNat / 4) h0, toByte_valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16) h1,
      toByte_valToB64 ((b1.toNat % 16) * 4 + b2.toNat / 64) h2, toByte_valToB64 (b2.toNat % 64) h3]
  have hnp0 : valToB64 (b0.toNat / 4) ≠ 61 := valToB64_not_pad _ h0
  have hnp1 : valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16) ≠ 61 := valToB64_not_pad _ h1
  have hnp2 : valToB64 ((b1.toNat % 16) * 4 + b2.toNat / 64) ≠ 61 := valToB64_not_pad _ h2
  have hnp3 : valToB64 (b2.toNat % 64) ≠ 61 := valToB64_not_pad _ h3
  have hvd0 : b64Valid (valToB64 (b0.toNat / 4)) = true := valToB64_valid _ h0
  have hvd1 : b64Valid (valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16)) = true := valToB64_valid _ h1
  have hvd2 : b64Valid (valToB64 ((b1.toNat % 16) * 4 + b2.toNat / 64)) = true := valToB64_valid _ h2
  have hvd3 : b64Valid (valToB64 (b2.toNat % 64)) = true := valToB64_valid _ h3
  rw [hvd0, hvd1]
  rw [b64ToVal_valToB64 (b0.toNat / 4) h0, b64ToVal_valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16) h1]
  simp only [hnp0, hnp1]
  have hb0v : (b0.toNat / 4) * 4 + (((b0.toNat % 4) * 16 + b1.toNat / 16) / 16) = b0.toNat := byte0 b0.toNat b1.toNat hb0 hb1
  rw [hb0v]
  rw [hvd2]
  rw [b64ToVal_valToB64 ((b1.toNat % 16) * 4 + b2.toNat / 64) h2]
  simp only [hnp2]
  have hb1v : (((b0.toNat % 4) * 16 + b1.toNat / 16) % 16) * 16 + (((b1.toNat % 16) * 4 + b2.toNat / 64) / 4) = b1.toNat := by
    have hmod : ((b0.toNat % 4) * 16 + b1.toNat / 16) % 16 = b1.toNat / 16 := by
      have h := Nat.add_mul_mod_self_right (b0.toNat % 4) (b1.toNat / 16) 16
      omega
    have hdiv : ((b1.toNat % 16) * 4 + b2.toNat / 64) / 4 = b1.toNat % 16 := by
      have h := Nat.add_mul_div_left (b2.toNat / 64) (b1.toNat % 16) (by decide : 0 < 4)
      have hz : b2.toNat / 64 / 4 = 0 := Nat.div_eq_of_lt (by omega)
      omega
    have hsum := Nat.div_add_mod b1.toNat 16
    omega
  rw [hb1v]
  rw [hvd3]
  rw [b64ToVal_valToB64 (b2.toNat % 64) h3]
  simp only [hnp3]
  have hb2v : (((b1.toNat % 16) * 4 + b2.toNat / 64) % 4) * 64 + (b2.toNat % 64) = b2.toNat := byte2 b1.toNat b2.toNat hb1 hb2
  rw [hb2v]
  simp [toByte, UInt8.ofNat_toNat]
/-- The inverse law: `apply` and `unapply` are mutual inverses. -/
theorem b64BlockIso_law (cs bs : List UInt8) :
    b64BlockApply cs = some bs ↔ b64BlockUnapply bs = some cs := by
  constructor
  · -- backward: apply cs = some bs → unapply bs = some cs
    intro h
    rw [b64BlockApply] at h
    rcases (Iso.bind_eq_some (b64BlockDecodeLenient cs) (fun bs' => if b64BlockUnapply bs' = some cs then some bs' else none) bs).1 h with
      ⟨bs', hdec, hcheck⟩
    have hun : b64BlockUnapply bs' = some cs := by
      by_cases hbs : b64BlockUnapply bs' = some cs
      · exact hbs
      · simp [hbs] at hcheck
    have hbs' : bs' = bs := by
      by_cases hbs : b64BlockUnapply bs' = some cs
      · simpa [hbs] using hcheck
      · simp [hbs] at hcheck
    rw [← hbs']
    exact hun
  · -- forward: unapply bs = some cs → apply cs = some bs
    intro h
    cases bs with
    | nil => simp [b64BlockUnapply] at h
    | cons b0 t0 =>
      cases t0 with
      | nil =>
          have h' : cs = [toByte (valToB64 (b0.toNat / 4)), toByte (valToB64 ((b0.toNat % 4) * 16)), 61, 61] := by
            simpa [b64BlockUnapply] using h.symm
          subst h'
          rw [b64BlockApply, b64BlockDecodeLenient_unapply_single b0]
          simp [b64BlockUnapply]
      | cons b1 t1 =>
        cases t1 with
        | nil =>
            have h' : cs = [toByte (valToB64 (b0.toNat / 4)), toByte (valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16)),
                            toByte (valToB64 ((b1.toNat % 16) * 4)), 61] := by
              simpa [b64BlockUnapply] using h.symm
            subst h'
            rw [b64BlockApply, b64BlockDecodeLenient_unapply_pair b0 b1]
            simp [b64BlockUnapply]
        | cons b2 t2 =>
          cases t2 with
          | nil =>
              have h' : cs = [toByte (valToB64 (b0.toNat / 4)), toByte (valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16)),
                              toByte (valToB64 ((b1.toNat % 16) * 4 + b2.toNat / 64)), toByte (valToB64 (b2.toNat % 64))] := by
                simpa [b64BlockUnapply] using h.symm
              subst h'
              rw [b64BlockApply, b64BlockDecodeLenient_unapply_triple b0 b1 b2]
              simp [b64BlockUnapply]
          | cons _ _ => simp [b64BlockUnapply] at h

def b64BlockIso : Iso (List UInt8) (List UInt8) :=
  { apply := b64BlockApply, unapply := b64BlockUnapply, law := b64BlockIso_law }

/-! ## The `Codec`-value full-block element

The full block is the `Run`'s repetition step: `count 4 (satisfy b64Char)` reads
four alphabet characters (no `=`; a pad-block is the terminal tail and is handled
separately), and `b64BlockIso` maps them to the three recovered bytes.  The
productivity witness is the inherited `Productive_iso`/`Productive_count_satisfy_succ`
chain (a block consumes 4 ≥ 1 bytes, so `decodeRepeat` is total). -/

/-- The full-block element: 4 alphabet chars → 3 bytes (no padding). -/
def b64BlockElem : Codec (List UInt8) :=
  iso b64BlockIso (count 4 (Codec.satisfy b64Char))

/-- `b64BlockElem` consumes 4 bytes per block. -/
theorem b64BlockConsumesByte : ConsumesByte b64BlockElem := by
  rw [← productive_iff_consumesByte, b64BlockElem]
  exact Productive_iso b64BlockIso (count 4 (Codec.satisfy b64Char))
    (Productive_count_satisfy_succ b64Char 3)

/-- `b64BlockElem` is functional (a block relates to a unique byte string). -/
theorem b64BlockElem_functional : Functional b64BlockElem := by
  unfold b64BlockElem
  exact Functional_iso b64BlockIso (count 4 (Codec.satisfy b64Char))
    (Functional_count_satisfy b64Char 4)

/-- Every byte of a `b64BlockElem`-related string is a base64 alphabet character. -/
theorem Rel_b64BlockElem_canonical {x : List UInt8} {m : Nat} {t : Bytes m} :
    Rel b64BlockElem x t → ∀ i : Fin m, b64Char (t i) = true := by
  intro ht
  unfold b64BlockElem at ht
  rw [Rel_iso] at ht
  rcases ht with ⟨a, _, hc⟩
  exact Rel_count_satisfy_forall b64Char 4 a t hc

/-! ## The terminal-tail element

The terminal tail is a single *padded* block (2 or 3 chars + `=`), or the empty
string.  It is decoded *after* the full-block run, so "data after `=`" has no
shape: a full block (3 bytes, no `=`) is rejected by `b64TailIso` (only 1–2-byte
outputs), and the recursive full-block repetition never produces a pad. -/

/-- `b64TailApply cs` — decode 4 chars to 1 or 2 bytes only (padded blocks). -/
def b64TailApply (cs : List UInt8) : Option (List UInt8) :=
  match b64BlockApply cs with
  | some [b0] => some [b0]
  | some [b0, b1] => some [b0, b1]
  | _ => none

/-- `b64TailUnapply bs` — encode 1 or 2 bytes as a padded 4-char block. -/
def b64TailUnapply (bs : List UInt8) : Option (List UInt8) :=
  match bs with
  | [b0] => b64BlockUnapply [b0]
  | [b0, b1] => b64BlockUnapply [b0, b1]
  | _ => none

/-- `b64TailApply` and `b64TailUnapply` are mutual inverses. -/
theorem b64TailIso_law (cs bs : List UInt8) :
    b64TailApply cs = some bs ↔ b64TailUnapply bs = some cs := by
  constructor
  · intro h
    cases hc : b64BlockApply cs with
    | none => simp [b64TailApply, hc] at h
    | some b =>
        cases b with
        | nil => simp [b64TailApply, hc] at h
        | cons b0 t =>
          cases t with
          | nil =>
              simp [b64TailApply, hc] at h
              subst bs
              simp [b64TailUnapply]
              exact (b64BlockIso_law cs [b0]).1 (by simp [hc])
          | cons b1 t2 =>
            cases t2 with
            | nil =>
                simp [b64TailApply, hc] at h
                subst bs
                simp [b64TailUnapply]
                exact (b64BlockIso_law cs [b0, b1]).1 (by simp [hc])
            | cons _ _ => simp [b64TailApply, hc] at h
  · intro h
    cases bs with
    | nil => simp [b64TailUnapply] at h
    | cons b0 t =>
      cases t with
      | nil =>
          simp [b64TailUnapply] at h
          have hb : b64BlockUnapply [b0] = some cs := by simpa using h
          have ha : b64BlockApply cs = some [b0] := (b64BlockIso_law cs [b0]).2 hb
          simp [b64TailApply, ha]
      | cons b1 t2 =>
        cases t2 with
        | nil =>
            simp [b64TailUnapply] at h
            have hb : b64BlockUnapply [b0, b1] = some cs := by simpa using h
            have ha : b64BlockApply cs = some [b0, b1] := (b64BlockIso_law cs [b0, b1]).2 hb
            simp [b64TailApply, ha]
        | cons _ _ => simp [b64TailUnapply] at h

/-- The terminal-tail block isomorphism (1–2 bytes ↔ padded 4-char block). -/
def b64TailIso : Iso (List UInt8) (List UInt8) :=
  { apply := b64TailApply, unapply := b64TailUnapply, law := b64TailIso_law }

/-- The terminal-tail element (padded block → 1/2 bytes). -/
def b64TailElem : Codec (List UInt8) :=
  iso b64TailIso (count 4 (Codec.satisfy b64OrPad))

/-- `b64TailElem` consumes 4 bytes per (padded) block; the empty input decodes to
`[]` via `decodeFull_zero`, so the whole-input tail decoder needs no `pure` branch. -/
theorem b64TailConsumesByte : ConsumesByte b64TailElem := by
  rw [← productive_iff_consumesByte, b64TailElem]
  exact Productive_iso b64TailIso (count 4 (Codec.satisfy b64OrPad))
    (Productive_count_satisfy_succ b64OrPad 3)

/-- `b64TailElem` is functional. -/
theorem b64TailElem_functional : Functional b64TailElem := by
  unfold b64TailElem
  exact Functional_iso b64TailIso (count 4 (Codec.satisfy b64OrPad))
    (Functional_count_satisfy b64OrPad 4)

/-! ## Unambiguity (the gate to the inherited roundtrip)

Each element must be `Unambiguous` at both the element level and the full
`decodeRepeat` level, mirroring `Base16`'s `hexElem_unambiguous`/
`hexDecodeFull_unambiguous` chain. -/

/-- `b64BlockElem` is unambiguous. -/
theorem b64BlockElem_unambiguous : Unambiguous b64BlockElem := by
  unfold b64BlockElem
  exact Unambiguous_iso b64BlockIso (count 4 (Codec.satisfy b64Char))
    (count_satisfy_unambiguous b64Char 4)

/-- `Rel b64BlockElem b bl` pins the byte length: `n = 4`. -/
theorem Rel_b64BlockElem_len (bl : List UInt8) {n : Nat} (s : Bytes n) :
    Rel b64BlockElem bl s → n = 4 := by
  intro h
  unfold b64BlockElem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, _, hc⟩
  exact Rel_count_satisfy_len b64Char 4 a s hc

/-- A `b64BlockElem`-related value is a 3-byte list: the full block's four
characters are all alphabet (no `=`), so `b64BlockUnapply x = some a` (via
`b64BlockIso_law`) cannot be a 1- or 2-byte encoding (those put a `61` pad at a
tail position), leaving only the 3-byte shape.  This is the block side of the
pad dichotomy the block/tail split-uniqueness lemma needs. -/
theorem Rel_b64BlockElem_size (x : List UInt8) {n : Nat} (s : Bytes n) :
    Rel b64BlockElem x s → x.length = 3 := by
  intro h
  unfold b64BlockElem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, ha, hr⟩
  have hofn : List.ofFn s = a := Rel_count_satisfy_ofFn b64Char 4 a s hr
  -- The decoded chars `a` contain no `=` pad: each is a `b64Char` byte of `s`.
  have hnopad : ∀ c ∈ a, c.toNat ≠ 61 := by
    intro c hc
    have hmem : c ∈ List.ofFn s := by rwa [hofn]
    rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, hi'⟩
    have hc_eq : c = s ⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩ := hi'.symm.trans (List.getElem_ofFn hi)
    have hbc : b64Char c = true := by
      rw [hc_eq]
      exact Rel_count_satisfy_forall b64Char 4 a s hr ⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩
    unfold b64Char at hbc
    intro heq
    rw [heq] at hbc
    have hpf : b64Valid 61 = false := by decide
    rw [hpf] at hbc
    exact Bool.false_ne_true hbc
  -- `b64BlockApply a = some x` gives the backward `b64BlockUnapply x = some a`.
  have hun : b64BlockUnapply x = some a := (b64BlockIso_law a x).1 ha
  -- Size case split: 1- and 2-byte shapes embed a `61` pad, violating `hnopad`.
  cases x with
  | nil => simp [b64BlockUnapply] at hun
  | cons x0 xs =>
      cases xs with
      | nil =>
          simp [b64BlockUnapply] at hun
          have hmem : (UInt8.ofNat 61) ∈ a := by
            rw [← hun]; simp
          exact False.elim (hnopad (UInt8.ofNat 61) hmem rfl)
      | cons x1 xs1 =>
          cases xs1 with
          | nil =>
              simp [b64BlockUnapply] at hun
              have hmem : (UInt8.ofNat 61) ∈ a := by
                rw [← hun]; simp
              exact False.elim (hnopad (UInt8.ofNat 61) hmem rfl)
          | cons x2 xs2 =>
              cases xs2 with
              | nil => rfl
              | cons _ _ => simp [b64BlockUnapply] at hun

/-- The full-block relation is unambiguous (element-level lifts to `relRepeat`). -/
theorem relB64Block_unambiguous : relUnambiguous (relRepeat (Rel b64BlockElem)) := by
  intro a b n s ha hb
  induction a generalizing b n s with
  | nil =>
      rw [relRepeat_nil] at ha
      subst n
      cases b with
      | nil => rfl
      | cons y ys =>
          rw [relRepeat_cons] at hb
          rcases hb with ⟨m, hm, s₁, s₂, _, hy, _⟩
          have hlen : m = 4 := Rel_b64BlockElem_len y s₁ hy
          have hm0 : m = 0 := by omega
          omega
  | cons x xs ih =>
      cases b with
      | nil =>
          rw [relRepeat_nil] at hb
          rw [relRepeat_cons] at ha
          rcases ha with ⟨mx, hmx, s₁x, s₂x, _, hx, _⟩
          have hlen : mx = 4 := Rel_b64BlockElem_len x s₁x hx
          subst n
          have hm0 : mx = 0 := by omega
          omega
      | cons y ys =>
          rw [relRepeat_cons] at ha hb
          rcases ha with ⟨mx, hmx, s₁x, s₂x, hsx, hx, hxs⟩
          rcases hb with ⟨my, hmy, s₁y, s₂y, hsy, hy, hys⟩
          have hlx : mx = 4 := Rel_b64BlockElem_len x s₁x hx
          have hly : my = 4 := Rel_b64BlockElem_len y s₁y hy
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
            exact b64BlockElem_unambiguous s₁x hx (by rw [hpre]; exact hy)
          have htail : xs = ys := by
            exact ih s₂x hxs (by simpa [htaily] using hys)
          rw [hhead, htail]

/-- Full-consumption decode is unambiguous for `b64BlockElem`. -/
theorem b64BlockDecodeFull_unambiguous {x y : List (List UInt8)} {n : Nat} (s : Bytes n) :
    (x, Suffix.empty n) ∈ decodeRepeat b64BlockElem b64BlockConsumesByte n s →
    (y, Suffix.empty n) ∈ decodeRepeat b64BlockElem b64BlockConsumesByte n s → x = y := by
  intro hx hy
  rcases (decodeRepeat_spec b64BlockElem b64BlockConsumesByte x n s (Suffix.empty n)).1 hx with ⟨s₀x, hsx, hrx⟩
  rcases (decodeRepeat_spec b64BlockElem b64BlockConsumesByte y n s (Suffix.empty n)).1 hy with ⟨s₀y, hsy, hry⟩
  have hs₀ : s₀x = s₀y := by
    have hpre : (Suffix.empty n).prepend s₀x = (Suffix.empty n).prepend s₀y := by
      exact hsx.symm.trans hsy
    exact prepend_prefix_eq (Suffix.empty n) s₀x s₀y hpre
  exact relB64Block_unambiguous s₀x hrx (by rw [hs₀]; exact hry)

/-- `b64TailElem` is unambiguous. -/
theorem b64TailElem_unambiguous : Unambiguous b64TailElem := by
  unfold b64TailElem
  exact Unambiguous_iso b64TailIso (count 4 (Codec.satisfy b64OrPad))
    (count_satisfy_unambiguous b64OrPad 4)

/-- `Rel b64TailElem t s` pins the byte length: `n = 4`. -/
theorem Rel_b64TailElem_len (t : List UInt8) {n : Nat} (s : Bytes n) :
    Rel b64TailElem t s → n = 4 := by
  intro h
  unfold b64TailElem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, _, hc⟩
  exact Rel_count_satisfy_len b64OrPad 4 a s hc

/-- The tail relation is unambiguous. -/
theorem relB64Tail_unambiguous : relUnambiguous (relRepeat (Rel b64TailElem)) := by
  intro a b n s ha hb
  induction a generalizing b n s with
  | nil =>
      rw [relRepeat_nil] at ha
      subst n
      cases b with
      | nil => rfl
      | cons y ys =>
          rw [relRepeat_cons] at hb
          rcases hb with ⟨m, hm, s₁, s₂, _, hy, _⟩
          have hlen : m = 4 := Rel_b64TailElem_len y s₁ hy
          have hm0 : m = 0 := by omega
          omega
  | cons x xs ih =>
      cases b with
      | nil =>
          rw [relRepeat_nil] at hb
          rw [relRepeat_cons] at ha
          rcases ha with ⟨mx, hmx, s₁x, s₂x, _, hx, _⟩
          have hlen : mx = 4 := Rel_b64TailElem_len x s₁x hx
          subst n
          have hm0 : mx = 0 := by omega
          omega
      | cons y ys =>
          rw [relRepeat_cons] at ha hb
          rcases ha with ⟨mx, hmx, s₁x, s₂x, hsx, hx, hxs⟩
          rcases hb with ⟨my, hmy, s₁y, s₂y, hsy, hy, hys⟩
          have hlx : mx = 4 := Rel_b64TailElem_len x s₁x hx
          have hly : my = 4 := Rel_b64TailElem_len y s₁y hy
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
            exact b64TailElem_unambiguous s₁x hx (by rw [hpre]; exact hy)
          have htail : xs = ys := by
            exact ih s₂x hxs (by simpa [htaily] using hys)
          rw [hhead, htail]

/-- Full-consumption decode is unambiguous for `b64TailElem`. -/
theorem b64TailDecodeFull_unambiguous {x y : List (List UInt8)} {n : Nat} (s : Bytes n) :
    (x, Suffix.empty n) ∈ decodeRepeat b64TailElem b64TailConsumesByte n s →
    (y, Suffix.empty n) ∈ decodeRepeat b64TailElem b64TailConsumesByte n s → x = y := by
  intro hx hy
  rcases (decodeRepeat_spec b64TailElem b64TailConsumesByte x n s (Suffix.empty n)).1 hx with ⟨s₀x, hsx, hrx⟩
  rcases (decodeRepeat_spec b64TailElem b64TailConsumesByte y n s (Suffix.empty n)).1 hy with ⟨s₀y, hsy, hry⟩
  have hs₀ : s₀x = s₀y := by
    have hpre : (Suffix.empty n).prepend s₀x = (Suffix.empty n).prepend s₀y := by
      exact hsx.symm.trans hsy
    exact prepend_prefix_eq (Suffix.empty n) s₀x s₀y hpre
  exact relB64Tail_unambiguous s₀x hrx (by rw [hs₀]; exact hry)

/-! ## The canonical value type and its flatten

`B64` is the canonical base64 block/tail spine: full 3-byte blocks, then at most
one terminal tail of 1 or 2 bytes.  Its tail constructors are terminal (no
continuation), so the split is well-scoped; the *rejection* of data after a pad
is the `decodeFullB64 = none` inequation over the composition, not a type-level fact.
-/

/-- The canonical base64 value. -/
inductive B64 where
  | nil
  | full (b0 b1 b2 : UInt8) (rest : B64)
  | tail1 (b0 : UInt8)
  | tail2 (b0 b1 : UInt8)

/-! ## The `B64` ↔ `List UInt8` canonical block/tail spine

The base64 value is the whole `List UInt8`; `B64` is the canonical block/tail
spine (a proved total bijective relabeling) used to specify the full-block +
terminal-tail split. This section is that relabeling. -/

/-- The decoded byte list of a `B64` value (full blocks 3 bytes each, then at
most one 1/2-byte terminal tail). -/
def b64BytesOf : B64 → List UInt8
  | B64.nil => []
  | B64.full b0 b1 b2 rest => [b0, b1, b2] ++ b64BytesOf rest
  | B64.tail1 b0 => [b0]
  | B64.tail2 b0 b1 => [b0, b1]

/-- Total split of a byte list into full 3-byte blocks plus a terminal 1/2-byte
tail.  Every byte list maps to a unique `B64` (the reverse of `b64BytesOf`); the
empty tail is `nil`, a 1-byte tail is `tail1`, a 2-byte tail is `tail2`. -/
def b64OfBytes : List UInt8 → B64
  | [] => B64.nil
  | [b0] => B64.tail1 b0
  | [b0, b1] => B64.tail2 b0 b1
  | b0 :: b1 :: b2 :: rest => B64.full b0 b1 b2 (b64OfBytes rest)

/-- `b64BytesOf` is a left inverse of `b64OfBytes`: splitting then flattening is
identity.  Proved by structural induction on the byte list (the 0/1/2-element
cases are tails, the 3+-element case recurses three elements deeper). -/
theorem b64BytesOf_ofBytes (bs : List UInt8) : b64BytesOf (b64OfBytes bs) = bs := by
  exact go bs
where
  go : (l : List UInt8) → b64BytesOf (b64OfBytes l) = l
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | b0 :: b1 :: b2 :: t2 => by
      unfold b64OfBytes b64BytesOf
      rw [go t2]
      rfl
  termination_by l => l.length
  decreasing_by simp +arith

/-- `b64OfBytes` is a left inverse of `b64BytesOf`: encoding then splitting a
`B64` value is identity.  The terminal-tail constructors are disjoint, so the
length class (0/1/2/3+) uniquely recovers the constructor. -/
theorem b64OfBytes_bytesOf (v : B64) : b64OfBytes (b64BytesOf v) = v := by
  induction v with
  | nil => rfl
  | full b0 b1 b2 rest ih =>
      change b64OfBytes ([b0, b1, b2] ++ b64BytesOf rest) = B64.full b0 b1 b2 rest
      have hcons : [b0, b1, b2] ++ b64BytesOf rest = b0 :: b1 :: b2 :: b64BytesOf rest := rfl
      rw [hcons]
      unfold b64OfBytes
      rw [ih]
  | tail1 b0 => rfl
  | tail2 b0 b1 => rfl

/-! ## The `Run` for base64 (full-block repetition)

Base64 is surfaced as a first-class run value: the full 3-byte block element is
the repetition step (`Run.elem`), and the terminal tail is a separate bounded
`Codec`.  The whole-input decoder/encoder are `Codec.decodeFull`/`decodeRepeat`/
`encodeRepeat` over these elements (never a bespoke `parseB64`). -/

/-- The base64 full-block run: value `List (List UInt8)`, one 3-byte block per step. -/
def b64Run : Run (List UInt8) :=
  { elem := b64BlockElem, step := b64BlockConsumesByte }

/-- The terminal-tail run's element is `b64TailElem` (bounded, one padded block). -/
def b64TailRun : Run (List UInt8) :=
  { elem := b64TailElem, step := b64TailConsumesByte }

/-! ## The uniform whole-input decoder/encoder

The whole base64 decoder is the *backtracking composition* of the full-block
run (`decodeRepeat b64BlockElem`) with the terminal tail (`decodeFull b64TailElem`)
— never a bespoke `parseB64`.  The encoder splits the byte list into full blocks +
a terminal tail and encodes each via the element encoders. -/

/-- The whole-input base64 decoder over a length-indexed byte string: the
full-block run followed by a single terminal tail (D8).  The committed tail is
at most one padded block — a *multi-block* tail (data after a terminal `=` that
is itself a valid padded block, e.g. `"Zg==Zg=="`) is rejected by the `≤ 1`
guard. -/
def decodeFullB64 {n : Nat} (s : Bytes n) : Option (List UInt8) :=
  List.head? ((decodeRepeat b64BlockElem b64BlockConsumesByte n s).filterMap fun ⟨blocks, t⟩ =>
    match decodeFull b64TailElem b64TailConsumesByte t.remaining t.bytes with
    | some tail =>
        if tail.length ≤ 1 then some (blocks.flatten ++ tail.flatten) else none
    | none => none)

/-- Split a byte list into full 3-byte blocks plus a terminal 0/1/2-byte tail. -/
def b64Split : List UInt8 → (List (List UInt8) × List UInt8)
  | [] => ([], [])
  | [b] => ([], [b])
  | [a, b] => ([], [a, b])
  | a :: b :: c :: rest =>
      let (blocks, tail) := b64Split rest
      ([a, b, c] :: blocks, tail)

/-- `b64Split` relabels the `B64` structure as a full-block list + terminal tail. -/
def b64Split_ofBytes (v : B64) : (List (List UInt8) × List UInt8) :=
  match v with
  | B64.nil => ([], [])
  | B64.tail1 b => ([], [b])
  | B64.tail2 a b => ([], [a, b])
  | B64.full a b c rest =>
      let (blocks, tail) := b64Split_ofBytes rest
      ([a, b, c] :: blocks, tail)

/-- Encode a terminal tail (0/1/2 bytes); empty tail → empty bytes. -/
def encodeB64Tail (tail : List UInt8) : Option (Sigma fun m => Bytes m) :=
  match tail with
  | [] => some ⟨0, Codec.emptyBytes⟩
  | [b] => Codec.encode b64TailElem [b]
  | [a, b] => Codec.encode b64TailElem [a, b]
  | _ => none

/-- `b64Split_ofBytes` of a value gives blocks whose flatten, plus the tail, is
exactly the byte list. -/
private theorem b64Split_ofBytes_shape (v : B64) :
    (b64Split_ofBytes v).1.flatten ++ (b64Split_ofBytes v).2 = b64BytesOf v := by
  induction v with
  | nil => rfl
  | tail1 b => rfl
  | tail2 a b => rfl
  | full a b c rest ih =>
      simp [b64Split_ofBytes, b64BytesOf]
      rw [ih]

/-- Encode the full blocks + terminal tail: `encodeRepeat` over the block element
and the bounded tail element, concatenated into one byte string. -/
def encodeB64' (blocks : List (List UInt8)) (tail : List UInt8) : Option (Sigma fun n => Bytes n) :=
  match encodeRepeat b64BlockElem blocks, encodeB64Tail tail with
  | some b, some t => some ⟨b.1 + t.1, Codec.concat b.2 t.2⟩
  | _, _ => none

/-- The whole-input base64 encoder (over the byte list). -/
def encodeB64 (bs : List UInt8) : Option (Sigma fun n => Bytes n) :=
  let p := b64Split_ofBytes (b64OfBytes bs)
  encodeB64' p.1 p.2

/-- `concat s emptyBytes` is `s` up to the `n + 0 = n` length cast. -/
private theorem concat_empty_eq {n : Nat} (s : Bytes n) :
    Codec.concat s (Codec.emptyBytes : Bytes 0) = cast (congrArg Bytes (Nat.add_zero n)) s := by
  apply Bytes.ext
  intro i
  unfold Codec.concat
  have hi : i.val < n := i.isLt
  simp [hi]

/-- Decoding an encoded tail with `decodeFull b64TailElem` recovers exactly one
tail block (or none, for the empty tail). -/
theorem decodeFull_b64Tail_of_encode (tail : List UInt8) {q : Nat} {st : Bytes q}
    (ht : encodeB64Tail tail = some ⟨q, st⟩) :
    decodeFull b64TailElem b64TailConsumesByte q st = (match tail with | [] => some [] | _ => some [tail]) := by
  cases tail with
  | nil =>
      have hs : (⟨0, (Codec.emptyBytes : Bytes 0)⟩ : Sigma fun k => Bytes k) = ⟨q, st⟩ := by
        simpa [encodeB64Tail] using ht
      cases hs
      exact decodeFull_zero b64TailElem b64TailConsumesByte Codec.emptyBytes
  | cons b t =>
    cases t with
    | nil =>
        have he : Codec.encode b64TailElem [b] = some ⟨q, st⟩ := by
          simpa [encodeB64Tail] using ht
        have hrep : encodeRepeat b64TailElem [[b]] = some ⟨q + 0, Codec.concat st (Codec.emptyBytes : Bytes 0)⟩ := by
          simp [encodeRepeat, he]
        have hrel2 : relRepeat (Rel b64TailElem) [[b]] (q + 0) (Codec.concat st (Codec.emptyBytes : Bytes 0)) :=
          encodeRepeat_rel b64TailElem [[b]] hrep
        have hc : Codec.concat st (Codec.emptyBytes : Bytes 0) = cast (congrArg Bytes (Nat.add_zero q)) st :=
          concat_empty_eq st
        have hrel : relRepeat (Rel b64TailElem) [[b]] q st := by
          rw [hc] at hrel2
          exact (relRepeat_cast (Rel b64TailElem) [[b]] (Nat.add_zero q) st).1 hrel2
        have hmem : ([[b]], Suffix.empty q) ∈ decodeRepeat b64TailElem b64TailConsumesByte q st := by
          refine (decodeRepeat_spec b64TailElem b64TailConsumesByte [[b]] q st (Suffix.empty q)).2 ⟨
            cast (congrArg Bytes (Nat.sub_zero q).symm) st, ?_, ?_⟩
          · exact (prepend_empty_eq st).symm
          · exact (relRepeat_cast (Rel b64TailElem) [[b]] (Nat.sub_zero q).symm st).2 hrel
        exact (decodeFull_spec b64TailElem b64TailConsumesByte
          (fun {x y} {m} (tx : Bytes m) => b64TailDecodeFull_unambiguous (s := tx)) st [[b]]).2 hmem
    | cons a t2 =>
      cases t2 with
      | nil =>
          have he : Codec.encode b64TailElem [b, a] = some ⟨q, st⟩ := by
            simpa [encodeB64Tail] using ht
          have hrep : encodeRepeat b64TailElem [[b, a]] = some ⟨q + 0, Codec.concat st (Codec.emptyBytes : Bytes 0)⟩ := by
            simp [encodeRepeat, he]
          have hrel2 : relRepeat (Rel b64TailElem) [[b, a]] (q + 0) (Codec.concat st (Codec.emptyBytes : Bytes 0)) :=
            encodeRepeat_rel b64TailElem [[b, a]] hrep
          have hc : Codec.concat st (Codec.emptyBytes : Bytes 0) = cast (congrArg Bytes (Nat.add_zero q)) st :=
            concat_empty_eq st
          have hrel : relRepeat (Rel b64TailElem) [[b, a]] q st := by
            rw [hc] at hrel2
            exact (relRepeat_cast (Rel b64TailElem) [[b, a]] (Nat.add_zero q) st).1 hrel2
          have hmem : ([[b, a]], Suffix.empty q) ∈ decodeRepeat b64TailElem b64TailConsumesByte q st := by
            refine (decodeRepeat_spec b64TailElem b64TailConsumesByte [[b, a]] q st (Suffix.empty q)).2 ⟨
              cast (congrArg Bytes (Nat.sub_zero q).symm) st, ?_, ?_⟩
            · exact (prepend_empty_eq st).symm
            · exact (relRepeat_cast (Rel b64TailElem) [[b, a]] (Nat.sub_zero q).symm st).2 hrel
          exact (decodeFull_spec b64TailElem b64TailConsumesByte
            (fun {x y} {m} (tx : Bytes m) => b64TailDecodeFull_unambiguous (s := tx)) st [[b, a]]).2 hmem
      | cons _ _ => simp [encodeB64Tail] at ht

/-! ## Whole-input roundtrip transport lemmas (base64)

The whole-input roundtrip composes the full-block run with the terminal tail; the
lemmas here are the `concat`/`Suffix.drop`/cast transport facts it needs
(`[propext, Quot.sound]`-only). -/

/-- `decodeFull` is insensitive to a length cast of its byte argument. -/
theorem decodeFull_cast {α : Type} (p : Codec α) (h : ConsumesByte p) :
    ∀ {n m : Nat} (e : n = m) (s : Bytes n),
      decodeFull p h m (cast (congrArg Bytes e) s) = decodeFull p h n s := by
  intro n m e s
  subst e
  rfl

/-- Splitting a byte list into full blocks + a terminal tail reassembles it. -/
theorem b64Split_shape (bs : List UInt8) :
    (b64Split bs).1.flatten ++ (b64Split bs).2 = bs := by
  exact go bs
where
  go : (l : List UInt8) → (b64Split l).1.flatten ++ (b64Split l).2 = l
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | b0 :: b1 :: b2 :: rest => by
      simp [b64Split, go rest]

/-- `b64Split_ofBytes (b64OfBytes bs)` re-labels as the direct `b64Split bs`. -/
theorem b64Split_ofBytes_ofBytes (bs : List UInt8) :
    b64Split_ofBytes (b64OfBytes bs) = b64Split bs := by
  exact go bs
where
  go : (l : List UInt8) → b64Split_ofBytes (b64OfBytes l) = b64Split l
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | b0 :: b1 :: b2 :: rest => by
      simp [b64OfBytes, b64Split_ofBytes, b64Split, go rest]

/-- Decoding an encoded *empty* tail over a dropped suffix is `some []`. -/
theorem decodeFull_b64Tail_suffix_nil {q m : Nat} {st : Bytes q} (sb : Bytes m)
    (ht : encodeB64Tail [] = some ⟨q, st⟩) :
    decodeFull b64TailElem b64TailConsumesByte (Suffix.drop m (concat sb st)).remaining (Suffix.drop m (concat sb st)).bytes
      = some [] := by
  unfold Suffix.drop
  simp only []
  rw [bdrop_concat sb st]
  change decodeFull b64TailElem b64TailConsumesByte (m + q - m)
      (cast (congrArg Bytes (Nat.add_sub_cancel_left m q).symm) st) = some []
  rw [decodeFull_cast b64TailElem b64TailConsumesByte (Nat.add_sub_cancel_left m q).symm st]
  simpa using decodeFull_b64Tail_of_encode [] ht

/-- Decoding an encoded *non-empty* tail over a dropped suffix is `some [tail]`. -/
theorem decodeFull_b64Tail_suffix_cons (tail : List UInt8) {q m : Nat} {st : Bytes q} (sb : Bytes m)
    (ht : encodeB64Tail tail = some ⟨q, st⟩) (hne : tail ≠ []) :
    decodeFull b64TailElem b64TailConsumesByte (Suffix.drop m (concat sb st)).remaining (Suffix.drop m (concat sb st)).bytes
      = some [tail] := by
  unfold Suffix.drop
  simp only []
  rw [bdrop_concat sb st]
  change decodeFull b64TailElem b64TailConsumesByte (m + q - m)
      (cast (congrArg Bytes (Nat.add_sub_cancel_left m q).symm) st) = some [tail]
  rw [decodeFull_cast b64TailElem b64TailConsumesByte (Nat.add_sub_cancel_left m q).symm st]
  have h := decodeFull_b64Tail_of_encode tail ht
  cases tail with
  | nil => exact False.elim (hne rfl)
  | cons x t =>
      cases t with
      | nil => simpa using h
      | cons y t2 =>
          cases t2 with
          | nil => simpa using h
          | cons _ _ => simp [encodeB64Tail] at ht

/-- A pad byte is not a base64 alphabet character. -/
theorem b64Char_pad_false : b64Char (UInt8.ofNat 61) = false := by
  unfold b64Char b64Valid b64ToVal
  decide

/-- A block element never relates to a byte string containing a pad byte. -/
theorem not_rel_b64BlockElem_of_pad (x : List UInt8) {m : Nat} (s : Bytes m) :
    (∃ i : Fin m, (s i).toNat = 61) → ¬ Rel b64BlockElem x s := by
  intro hpad hrel
  rcases hpad with ⟨i, hi⟩
  have hcanon : b64Char (s i) = true := Rel_b64BlockElem_canonical hrel i
  unfold b64Char at hcanon
  rw [hi] at hcanon
  -- hcanon : b64Valid 61 = true; but b64Valid 61 = false
  have hfalse : b64Valid 61 = false := by decide
  rw [hfalse] at hcanon
  exact Bool.false_ne_true hcanon

/-! ## Whole-input roundtrip (base64)

`decodeFullB64 (encodeB64 bs) = some bs`.  `[propext, Quot.sound]`-only. -/

/-- A `relRepeat (Rel b64BlockElem)` consumes `4 · length` bytes (each block is a
4-char element). -/
theorem relB64Block_len {xs : List (List UInt8)} {n : Nat} (s : Bytes n) :
    relRepeat (Rel b64BlockElem) xs n s → n = 4 * xs.length := by
  intro h
  induction xs generalizing n with
  | nil =>
      rw [relRepeat_nil] at h
      subst n
      rfl
  | cons x rest ih =>
      rw [relRepeat_cons] at h
      rcases h with ⟨m, _hm, s₁, s₂, _hs, hrel₁, hrelRest⟩
      have h4 : m = 4 := Rel_b64BlockElem_len x s₁ hrel₁
      subst m
      have hrest : n - 4 = 4 * rest.length := ih s₂ hrelRest
      rw [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- A `relRepeat (Rel b64TailElem)` consumes `4 · length` bytes. -/
theorem relB64Tail_len {xs : List (List UInt8)} {n : Nat} (s : Bytes n) :
    relRepeat (Rel b64TailElem) xs n s → n = 4 * xs.length := by
  intro h
  induction xs generalizing n with
  | nil =>
      rw [relRepeat_nil] at h
      subst n
      rfl
  | cons x rest ih =>
      rw [relRepeat_cons] at h
      rcases h with ⟨m, _hm, s₁, s₂, _hs, hrel₁, hrelRest⟩
      have h4 : m = 4 := Rel_b64TailElem_len x s₁ hrel₁
      subst m
      have hrest : n - 4 = 4 * rest.length := ih s₂ hrelRest
      rw [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- A `Rel b64TailElem` value is a 1- or 2-byte list (a padded block). -/
theorem Rel_b64TailElem_size (x : List UInt8) {n : Nat} (s : Bytes n) :
    Rel b64TailElem x s → x.length = 1 ∨ x.length = 2 := by
  intro h
  unfold b64TailElem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, ha, _⟩
  have hsz : x.length = 1 ∨ x.length = 2 := by
    unfold b64TailIso at ha
    change b64TailApply a = some x at ha
    unfold b64TailApply at ha
    cases hb : b64BlockApply a with
    | none => simp [hb] at ha
    | some bl =>
        cases bl with
        | nil => simp [hb] at ha
        | cons b0 t =>
            cases t with
            | nil => simp [hb] at ha; cases ha; left; rfl
            | cons b1 t2 =>
                cases t2 with
                | nil => simp [hb] at ha; cases ha; right; rfl
                | cons _ _ => simp [hb] at ha
  exact hsz

/-- The pad-dichotomy rejection: a value cannot be both a full block (3 bytes,
no pad) and a terminal tail (1–2 bytes, padded).  `Rel_b64BlockElem_size` pins
the former to `x.length = 3`, `Rel_b64TailElem_size` the latter to a 1- or
2-byte list — disjoint length classes, so exactly one boundary class holds.  This
is the "no-pad 4-char block vs. padded tail" disjunction the block/tail
split-uniqueness lemma depends on. -/
theorem Rel_b64BlockElem_not_tail (x : List UInt8) {n m : Nat} (s : Bytes n) (t : Bytes m) :
    Rel b64BlockElem x s → Rel b64TailElem x t → False := by
  intro hb ht
  have h3 : x.length = 3 := Rel_b64BlockElem_size x s hb
  have h12 := Rel_b64TailElem_size x t ht
  rcases h12 with h1 | h2 <;> omega

/-- A `Rel b64TailElem`-related string contains a `=` pad byte: the tail value
`x` is 1–2 bytes, so `b64TailApply`/`b64BlockApply` recover it from a block whose
`b64BlockUnapply` puts a `61` at a terminal position, and the content-extraction
lemma pins those chars to actual bytes of `s`.  This is the tail side of the pad
dichotomy: a padded block must contain `=`, so it cannot be confused with a
full (no-pad) block. -/
theorem Rel_b64TailElem_has_pad (x : List UInt8) {n : Nat} (s : Bytes n) :
    Rel b64TailElem x s → (∃ i : Fin n, (s i).toNat = 61) := by
  intro h
  unfold b64TailElem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, ha, hr⟩
  have hofn : List.ofFn s = a := Rel_count_satisfy_ofFn b64OrPad 4 a s hr
  -- `b64TailApply a = some x` forces `b64BlockUnapply` of a 1- or 2-byte list,
  -- whose char list has a `61` at a terminal position.
  unfold b64TailIso at ha
  change b64TailApply a = some x at ha
  unfold b64TailApply at ha
  cases hb : b64BlockApply a with
  | none => simp [hb] at ha
  | some bl =>
      cases bl with
      | nil => simp [hb] at ha
      | cons b0 bl1 =>
        cases bl1 with
        | nil =>
            -- 1-byte tail: bl = [b0]
            have hun : b64BlockUnapply [b0] = some a := (b64BlockIso_law a [b0]).1 (by simpa using hb)
            simp [b64BlockUnapply] at hun
            have hmem : (UInt8.ofNat 61) ∈ a := by rw [← hun]; simp
            rw [← hofn] at hmem
            rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, hi'⟩
            refine ⟨⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩, ?_⟩
            have hbyte : s ⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩ = (UInt8.ofNat 61) := by
              exact (List.getElem_ofFn hi).symm.trans hi'
            have hval : (s ⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩).toNat = 61 := by
              simpa using congrArg UInt8.toNat hbyte
            exact hval
        | cons b1 bl2 =>
          cases bl2 with
          | nil =>
            -- 2-byte tail: bl = [b0, b1]
            have hun : b64BlockUnapply [b0, b1] = some a := (b64BlockIso_law a [b0, b1]).1 (by simpa using hb)
            simp [b64BlockUnapply] at hun
            have hmem : (UInt8.ofNat 61) ∈ a := by rw [← hun]; simp
            rw [← hofn] at hmem
            rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, hi'⟩
            refine ⟨⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩, ?_⟩
            have hbyte : s ⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩ = (UInt8.ofNat 61) := by
              exact (List.getElem_ofFn hi).symm.trans hi'
            have hval : (s ⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩).toNat = 61 := by
              simpa using congrArg UInt8.toNat hbyte
            exact hval
          | cons _ _ =>
            -- 3 bytes: b64TailApply rejects (returns none)
            simp [hb] at ha

/-! ## Encoded-output structure (inputs to the boundary-pin)

`encodeRepeat b64BlockElem blocks` produces alphabet-only (no-pad) bytes, and a
non-empty `encodeB64Tail` produces a padded block containing `=`.  Together with
the pad-dichotomy primitives these pin the block/tail boundary at `m₁`. -/

/-- The full-block encoding is alphabet-only: every byte of `encodeRepeat
b64BlockElem blocks = some ⟨n, s⟩` is a `b64Char` (never `=`). -/
theorem encodeB64Block_nopad (blocks : List (List UInt8)) {n : Nat} {s : Bytes n}
    (he : encodeRepeat b64BlockElem blocks = some ⟨n, s⟩) :
    ∀ i : Fin n, b64Char (s i) = true := by
  have hrel : relRepeat (Rel b64BlockElem) blocks n s := encodeRepeat_rel b64BlockElem blocks he
  exact relRepeat_forall b64Char (fun x {m} t ht => Rel_b64BlockElem_canonical (t := t) ht) blocks n s hrel

/-- A non-empty terminal-tail encoding contains a `=` pad byte. -/
theorem encodeB64Tail_has_pad (tail : List UInt8) {n : Nat} {s : Bytes n}
    (hne : tail ≠ []) (he : encodeB64Tail tail = some ⟨n, s⟩) :
    ∃ i : Fin n, (s i).toNat = 61 := by
  cases tail with
  | nil => exact False.elim (hne rfl)
  | cons b t =>
      cases t with
      | nil =>
          have henc : Codec.encode b64TailElem [b] = some ⟨n, s⟩ := by simpa [encodeB64Tail] using he
          have hrel : Rel b64TailElem [b] s := encode_rel b64TailElem [b] henc
          exact Rel_b64TailElem_has_pad [b] s hrel
      | cons b1 t1 =>
          cases t1 with
          | nil =>
              have henc : Codec.encode b64TailElem [b, b1] = some ⟨n, s⟩ := by simpa [encodeB64Tail] using he
              have hrel : Rel b64TailElem [b, b1] s := encode_rel b64TailElem [b, b1] henc
              exact Rel_b64TailElem_has_pad [b, b1] s hrel
          | cons _ _ => simp [encodeB64Tail] at he

/-- `encodeB64Tail tail = some ⟨n, s⟩` pins the encoded length to `0` (empty
tail) or `4` (one padded block). This is the input to the boundary-pin's
`m₂ ∈ {0, 4}` fact. -/
theorem encodeB64Tail_len (tail : List UInt8) {n : Nat} {s : Bytes n}
    (he : encodeB64Tail tail = some ⟨n, s⟩) :
    n = 0 ∨ n = 4 := by
  cases tail with
  | nil =>
      have hs : (⟨0, (Codec.emptyBytes : Bytes 0)⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by
        simpa [encodeB64Tail] using he
      cases hs
      left; rfl
  | cons b t =>
      cases t with
      | nil =>
          have henc : Codec.encode b64TailElem [b] = some ⟨n, s⟩ := by simpa [encodeB64Tail] using he
          have hrel : Rel b64TailElem [b] s := encode_rel b64TailElem [b] henc
          have hlen : n = 4 := Rel_b64TailElem_len [b] s hrel
          right; exact hlen
      | cons b1 t1 =>
          cases t1 with
          | nil =>
              have henc : Codec.encode b64TailElem [b, b1] = some ⟨n, s⟩ := by simpa [encodeB64Tail] using he
              have hrel : Rel b64TailElem [b, b1] s := encode_rel b64TailElem [b, b1] henc
              have hlen : n = 4 := Rel_b64TailElem_len [b, b1] s hrel
              right; exact hlen
          | cons _ _ => simp [encodeB64Tail] at he

/-! ## Whole-input roundtrip transport: prefix/suffix extraction

The whole-input roundtrip `decodeFullB64 (encodeB64 bs) = some bs` composes the
full-block run with the terminal tail.  Its one new step is the *block/tail
split-uniqueness* lemma, whose boundary pin rests on extracting the decoded
consumed-prefix / remaining bytes back to the committed `blkBytes`/`tailBytes`.
`[propext, Quot.sound]`-only. -/

/-- From `t'.prepend s₀ = concat a b` and `m₁ + m₂ - t'.remaining = m₁` (so the
consumed prefix has length `m₁`), the consumed prefix `s₀` is exactly `a`. -/
theorem prepend_concat_prefix_cast {m₁ m₂ : Nat} (a : Bytes m₁) (b : Bytes m₂)
    (t' : Suffix (m₁ + m₂)) (s₀ : Bytes (m₁ + m₂ - t'.remaining))
    (e : m₁ + m₂ - t'.remaining = m₁)
    (h : t'.prepend s₀ = concat a b) :
    cast (congrArg Bytes e) s₀ = a := by
  apply Bytes.ext
  intro i
  have hi' : i.val < m₁ + m₂ - t'.remaining := by
    rw [e]
    exact i.isLt
  rw [cast_bytes_val' (e := e)]
  have hs₀ : s₀ ⟨i.val, hi'⟩ = (t'.prepend s₀) ⟨i.val, (by omega : i.val < m₁ + m₂)⟩ := by
    rw [prepend_apply]
    unfold concat
    rw [cast_fin_symm]
    · simp [hi']
    · omega
  have hpre : (t'.prepend s₀) ⟨i.val, (by omega : i.val < m₁ + m₂)⟩ = a ⟨i.val, by omega⟩ := by
    rw [h]
    unfold concat
    simp [show i.val < m₁ by omega]
  rw [hs₀, hpre]

/-- From `t'.prepend s₀ = concat a b` and `t'.remaining = m₂` (so the consumed
prefix has length `m₁`), the remaining suffix `t'.bytes` is exactly `b` (up to the
length cast).  Dropping the consumed prefix `s₀` from `t'.prepend s₀` recovers
`t'.bytes` (via `bdrop_prepend`), and from `concat a b` recovers `b` (via
`bdrop_concat`), so the two agree.  This is the suffix half of the block/tail
boundary-pin. -/
theorem prepend_concat_suffix {m₁ m₂ : Nat} (a : Bytes m₁) (b : Bytes m₂)
    (t' : Suffix (m₁ + m₂)) (s₀ : Bytes (m₁ + m₂ - t'.remaining))
    (hrem : t'.remaining = m₂)
    (h : t'.prepend s₀ = concat a b) :
    cast (congrArg Bytes (Nat.sub_sub_self t'.hle).symm) t'.bytes =
      cast (congrArg Bytes (by omega : m₂ = (m₁ + m₂) - ((m₁ + m₂) - t'.remaining))) b := by
  have hdrop := congrArg (bdrop (m₁ + m₂ - t'.remaining)) h
  rw [bdrop_prepend t' s₀] at hdrop
  have hrhs : bdrop (m₁ + m₂ - t'.remaining) (concat a b) =
      cast (congrArg Bytes (by omega : m₂ = (m₁ + m₂) - ((m₁ + m₂) - t'.remaining))) b := by
    apply Bytes.ext
    intro i
    rw [cast_bytes_val' (e := (by omega : m₂ = (m₁ + m₂) - ((m₁ + m₂) - t'.remaining)))]
    dsimp [bdrop, concat]
    have hk : m₁ + m₂ - t'.remaining = m₁ := by omega
    have hnot : ¬ i.val + m₁ < m₁ := by omega
    simp [hk, hnot]
  rw [hdrop, hrhs]

/-! ## The block/tail boundary pin

The one genuinely new step of the padded-base roundtrip: pin the split between
the full-block run and the terminal tail.  Given the committed `concat blkBytes
tailBytes` (with `blkBytes` alphabet-only and `tailBytes` empty or one padded
block) and the decoded block prefix `s₀` / remaining suffix `t'.bytes`, the
block run cannot stop before (`t'.remaining > m₂`) or after (`t'.remaining < m₂`)
the `m₁`-boundary — the `=` pad byte would have to be read as an alphabet byte
by `s₀` or by the first decoded tail block, contradicting the pad dichotomy.
`[propext, Quot.sound]`-only. -/

/-- Reading the consumed prefix of a `prepend`-reassembly: `s₀` is the prefix of
`t'.prepend s₀`. -/
private theorem prepend_prefix_read {m₁ m₂ : Nat} (t' : Suffix (m₁ + m₂))
    (s₀ : Bytes (m₁ + m₂ - t'.remaining)) (i : Fin (m₁ + m₂ - t'.remaining)) :
    s₀ i = (t'.prepend s₀) ⟨i.val, (by omega : i.val < m₁ + m₂)⟩ := by
  rw [prepend_apply]
  unfold concat
  rw [cast_fin_symm]
  · simp [i.isLt]
  · omega

/-- Reading the remaining suffix of a `prepend`-reassembly against the committed
`concat`: `t'.bytes` is the suffix of `concat blkBytes tailBytes` at offset
`m₁ + m₂ - t'.remaining`. -/
private theorem prepend_suffix_read {m₁ m₂ : Nat} (blkBytes : Bytes m₁) (tailBytes : Bytes m₂)
    (t' : Suffix (m₁ + m₂)) (s₀ : Bytes (m₁ + m₂ - t'.remaining))
    (h : t'.prepend s₀ = concat blkBytes tailBytes)
    (i : Fin t'.remaining) :
    t'.bytes i =
      (concat blkBytes tailBytes) ⟨i.val + (m₁ + m₂ - t'.remaining), (by
        have hi : i.val < t'.remaining := i.isLt
        have hle : t'.remaining ≤ m₁ + m₂ := t'.hle
        omega)⟩ := by
  have hdrop := congrArg (bdrop (m₁ + m₂ - t'.remaining)) h
  rw [bdrop_prepend t' s₀] at hdrop
  have hread := congrArg (fun (s : Bytes ((m₁ + m₂) - (m₁ + m₂ - t'.remaining))) =>
    s ⟨i.val, (by
      have hi : i.val < t'.remaining := i.isLt
      have hsub : (m₁ + m₂) - (m₁ + m₂ - t'.remaining) = t'.remaining := Nat.sub_sub_self t'.hle
      omega)⟩) hdrop
  rw [cast_bytes_val' (e := (Nat.sub_sub_self t'.hle).symm)] at hread
  dsimp [bdrop] at hread
  simpa using hread

/-- Reading a committed `concat` at a tail index: position `m₁ + i.val` is the
tail byte `tailBytes i`. -/
private theorem concat_tail_read {m₁ m₂ : Nat} (blkBytes : Bytes m₁) (tailBytes : Bytes m₂)
    (i : Fin m₂) :
    (concat blkBytes tailBytes) ⟨m₁ + i.val, (by omega : m₁ + i.val < m₁ + m₂)⟩ = tailBytes i := by
  unfold concat
  have hnot : ¬ (m₁ + i.val) < m₁ := by omega
  simp [hnot, Nat.add_sub_cancel_left]

/-- The first decoded tail block cannot sit inside the alphabet-only block
region: its first 4 bytes are `blkBytes`-region bytes (no `=`), but a tail block
always contains a `=` pad byte. -/
private theorem b64_first_tail_block_not_alphabet
    {m₁ m₂ : Nat} (blkBytes : Bytes m₁) (tailBytes : Bytes m₂)
    (t : List UInt8) (rest : List (List UInt8))
    (t' : Suffix (m₁ + m₂)) (s₀ : Bytes (m₁ + m₂ - t'.remaining))
    (htail : relRepeat (Rel b64TailElem) (t :: rest) t'.remaining t'.bytes)
    (h : t'.prepend s₀ = concat blkBytes tailBytes)
    (hblk : ∀ i : Fin m₁, b64Char (blkBytes i) = true)
    (hL4 : (m₁ + m₂ - t'.remaining) + 4 ≤ m₁) :
    False := by
  rw [relRepeat_cons] at htail
  rcases htail with ⟨m, hm, s₁, s₂, hs, ht₁, _⟩
  have hm4 : m = 4 := Rel_b64TailElem_len t s₁ ht₁
  have hpad₁ : ∃ i : Fin m, (s₁ i).toNat = 61 := Rel_b64TailElem_has_pad t s₁ ht₁
  rcases hpad₁ with ⟨i, hi⟩
  have hi_lt_m : i.val < m := i.isLt
  have hi_lt_t' : i.val < t'.remaining := by omega
  -- the first tail block is a prefix of `t'.bytes`
  have hs₁read : s₁ i = t'.bytes ⟨i.val, hi_lt_t'⟩ := by
    rw [hs]
    simpa using (splice_prefix_read hm s₁ s₂ ⟨i.val, hi_lt_t'⟩ hi_lt_m).symm
  have ht'pad : (t'.bytes ⟨i.val, hi_lt_t'⟩).toNat = 61 := by
    rw [← hs₁read]
    exact hi
  -- the remaining suffix reads back through the committed `concat` into `blkBytes`
  have htsuffix : t'.bytes ⟨i.val, hi_lt_t'⟩ =
      (concat blkBytes tailBytes) ⟨i.val + (m₁ + m₂ - t'.remaining), (by
        have hle : t'.remaining ≤ m₁ + m₂ := t'.hle
        omega : i.val + (m₁ + m₂ - t'.remaining) < m₁ + m₂)⟩ :=
    prepend_suffix_read blkBytes tailBytes t' s₀ h ⟨i.val, hi_lt_t'⟩
  have hconcatpad : ((concat blkBytes tailBytes) ⟨i.val + (m₁ + m₂ - t'.remaining), (by
        have hle : t'.remaining ≤ m₁ + m₂ := t'.hle
        omega : i.val + (m₁ + m₂ - t'.remaining) < m₁ + m₂)⟩).toNat = 61 := by
    rw [← htsuffix]
    exact ht'pad
  have hconcat_read : (concat blkBytes tailBytes) ⟨i.val + (m₁ + m₂ - t'.remaining), (by
        have hle : t'.remaining ≤ m₁ + m₂ := t'.hle
        omega : i.val + (m₁ + m₂ - t'.remaining) < m₁ + m₂)⟩ =
      blkBytes ⟨i.val + (m₁ + m₂ - t'.remaining), (by omega : i.val + (m₁ + m₂ - t'.remaining) < m₁)⟩ := by
    unfold concat
    have hi4 : i.val < 4 := by omega
    have hlt : i.val + (m₁ + m₂ - t'.remaining) < m₁ := by omega
    simp [hlt]
  have hblkpad : (blkBytes ⟨i.val + (m₁ + m₂ - t'.remaining), (by omega : i.val + (m₁ + m₂ - t'.remaining) < m₁)⟩).toNat = 61 := by
    rw [← hconcat_read]
    exact hconcatpad
  have hcanon := hblk ⟨i.val + (m₁ + m₂ - t'.remaining), (by omega : i.val + (m₁ + m₂ - t'.remaining) < m₁)⟩
  unfold b64Char at hcanon
  rw [hblkpad] at hcanon
  have hfalse : b64Valid 61 = false := by decide
  rw [hfalse] at hcanon
  exact Bool.false_ne_true hcanon

/-- `4 * a < 4 * b → a < b` — the constructive (`omega`) spelling of the
multiplication-cancellation the boundary-pin needs (the stdlib
`Nat.lt_of_mul_lt_mul_left` is `Classical.choice`-dependent). -/
private theorem four_mul_lt_of_lt {a b : Nat} (h : 4 * a < 4 * b) : a < b := by
  omega

/-- The block/tail boundary pin: the full-block run of a padded base consumes
exactly `m₁` bytes, leaving exactly the terminal tail `m₂`.  Inputs are the
committed block encode (`henc`), the decoded block prefix (`hblock`), the
decoded tail (`htail`), the reassembly `t'.prepend s₀ = concat blkBytes tailBytes`,
and the tail's `m₂ ∈ {0,4}`-plus-pad structure (`hm₂`, `hpad`). -/
theorem b64_boundary_pin
    {m₁ m₂ : Nat} (blkBytes : Bytes m₁) (tailBytes : Bytes m₂)
    (blocks blocks' : List (List UInt8)) (tail'' : List (List UInt8))
    (t' : Suffix (m₁ + m₂)) (s₀ : Bytes (m₁ + m₂ - t'.remaining))
    (henc : relRepeat (Rel b64BlockElem) blocks m₁ blkBytes)
    (hblock : relRepeat (Rel b64BlockElem) blocks' (m₁ + m₂ - t'.remaining) s₀)
    (htail : relRepeat (Rel b64TailElem) tail'' t'.remaining t'.bytes)
    (h : t'.prepend s₀ = concat blkBytes tailBytes)
    (hm₂ : m₂ = 0 ∨ m₂ = 4)
    (hpad : m₂ ≠ 0 → ∃ i : Fin m₂, (tailBytes i).toNat = 61) :
    t'.remaining = m₂ := by
  have hs₀ : ∀ i : Fin (m₁ + m₂ - t'.remaining), b64Char (s₀ i) = true :=
    relRepeat_forall b64Char (fun x {m} t ht => Rel_b64BlockElem_canonical (t := t) ht) blocks' (m₁ + m₂ - t'.remaining) s₀ hblock
  have hblk : ∀ i : Fin m₁, b64Char (blkBytes i) = true :=
    relRepeat_forall b64Char (fun x {m} t ht => Rel_b64BlockElem_canonical (t := t) ht) blocks m₁ blkBytes henc
  have hL : m₁ + m₂ - t'.remaining = 4 * blocks'.length := relB64Block_len s₀ hblock
  have hm₁len : m₁ = 4 * blocks.length := relB64Block_len blkBytes henc
  have ht' : t'.remaining = 4 * tail''.length := relB64Tail_len t'.bytes htail
  rcases hm₂ with hm₂0 | hm₂4
  · -- m₂ = 0 (empty tail): the block run must consume everything
    cases tail'' with
    | nil =>
        have ht'0 : t'.remaining = 0 := by simpa using ht'
        omega
    | cons t rest =>
        have ht'pos : 4 ≤ t'.remaining := by
          rw [ht']
          simp only [List.length_cons]
          omega
        have hL4 : (m₁ + m₂ - t'.remaining) + 4 ≤ m₁ := by
          have ht'le : t'.remaining ≤ m₁ := by simpa [hm₂0] using t'.hle
          omega
        exact False.elim (b64_first_tail_block_not_alphabet blkBytes tailBytes t rest t' s₀ htail h hblk hL4)
  · -- m₂ = 4 (padded tail): the block run must stop exactly at m₁
    have hpad' : ∃ i : Fin m₂, (tailBytes i).toNat = 61 := hpad (by omega : m₂ ≠ 0)
    rcases hpad' with ⟨ip, hip⟩
    have hconcat_tail : (concat blkBytes tailBytes) ⟨m₁ + ip.val, (by omega : m₁ + ip.val < m₁ + m₂)⟩ = tailBytes ip :=
      concat_tail_read blkBytes tailBytes ip
    have hnot : ¬ (m₁ + ip.val) < (m₁ + m₂ - t'.remaining) := by
      intro hjlt
      have hs₀read : s₀ ⟨m₁ + ip.val, hjlt⟩ = (concat blkBytes tailBytes) ⟨m₁ + ip.val, (by omega : m₁ + ip.val < m₁ + m₂)⟩ := by
        rw [prepend_prefix_read t' s₀ ⟨m₁ + ip.val, hjlt⟩]
        rw [h]
      have hs₀pad : (s₀ ⟨m₁ + ip.val, hjlt⟩).toNat = 61 := by
        rw [hs₀read, hconcat_tail]
        exact hip
      have hcanon := hs₀ ⟨m₁ + ip.val, hjlt⟩
      unfold b64Char at hcanon
      rw [hs₀pad] at hcanon
      have hfalse : b64Valid 61 = false := by decide
      rw [hfalse] at hcanon
      exact Bool.false_ne_true hcanon
    have hL_le_j : m₁ + m₂ - t'.remaining ≤ m₁ + ip.val := Nat.le_of_not_gt hnot
    have hL_le_m₁3 : m₁ + m₂ - t'.remaining ≤ m₁ + 3 := by omega
    have hlen_le : blocks'.length ≤ blocks.length := by omega
    have hL_le_m₁ : m₁ + m₂ - t'.remaining ≤ m₁ := by omega
    cases tail'' with
    | nil =>
        have ht'0 : t'.remaining = 0 := by simpa using ht'
        have hcontra : m₁ + m₂ ≤ m₁ := by
          rw [ht'0] at hL_le_m₁
          simpa using hL_le_m₁
        omega
    | cons t rest =>
        by_cases hL_eq : m₁ + m₂ - t'.remaining = m₁
        · have hsub : (m₁ + m₂ - t'.remaining) + t'.remaining = m₁ + m₂ := Nat.sub_add_cancel t'.hle
          have hsub' : m₁ + t'.remaining = m₁ + m₂ := by
            rw [hL_eq] at hsub
            exact hsub
          exact Nat.add_left_cancel hsub'
        · have hL_lt : m₁ + m₂ - t'.remaining < m₁ := Nat.lt_of_le_of_ne hL_le_m₁ hL_eq
          have hlen_lt : blocks'.length < blocks.length := by
            have h1 : 4 * blocks'.length < 4 * blocks.length := by
              rw [← hL, ← hm₁len]
              exact hL_lt
            exact four_mul_lt_of_lt h1
          have hL4 : (m₁ + m₂ - t'.remaining) + 4 ≤ m₁ := by
            have hlen_succ : blocks'.length + 1 ≤ blocks.length := Nat.succ_le_of_lt hlen_lt
            have h4 : 4 * blocks'.length + 4 ≤ 4 * blocks.length := by
              have h := Nat.mul_le_mul_left 4 hlen_succ
              simpa [Nat.mul_add] using h
            omega
          exact False.elim (b64_first_tail_block_not_alphabet blkBytes tailBytes t rest t' s₀ htail h hblk hL4)

/-- The block run extracted by the whole-input decoder is the committed block
run: once the boundary pin fixes `t'.remaining = m₂` (so the block prefix
consumes exactly `m₁` bytes), the decoded block prefix `s₀` is exactly `blkBytes`
(via `prepend_concat_prefix_cast`), and `relB64Block_unambiguous` pins
`blocks' = blocks`.  This is substep (3) of the whole-input roundtrip: the
block-run/tail split is unique, so the decoded full blocks are the committed
full blocks.  `[propext, Quot.sound]`-only. -/
theorem b64_block_run_of_boundary
    {m₁ m₂ : Nat} (blkBytes : Bytes m₁) (tailBytes : Bytes m₂)
    (blocks blocks' : List (List UInt8))
    (t' : Suffix (m₁ + m₂)) (s₀ : Bytes (m₁ + m₂ - t'.remaining))
    (henc : relRepeat (Rel b64BlockElem) blocks m₁ blkBytes)
    (hblock : relRepeat (Rel b64BlockElem) blocks' (m₁ + m₂ - t'.remaining) s₀)
    (h : t'.prepend s₀ = concat blkBytes tailBytes)
    (hrem : t'.remaining = m₂) :
    blocks' = blocks := by
  have he : m₁ + m₂ - t'.remaining = m₁ := by omega
  have hblock' : relRepeat (Rel b64BlockElem) blocks' m₁ (cast (congrArg Bytes he) s₀) :=
    (relRepeat_cast (Rel b64BlockElem) blocks' he s₀).2 hblock
  have hs₀ : cast (congrArg Bytes he) s₀ = blkBytes :=
    prepend_concat_prefix_cast blkBytes tailBytes t' s₀ he h
  rw [hs₀] at hblock'
  exact relB64Block_unambiguous blkBytes hblock' henc

/-! ## Whole-input roundtrip assembly (base64)

The roundtrip `decodeFullB64 (encodeB64 bs) = some bs`: the committed encode
splits `bs` into full blocks `blocks` + a terminal `tail`; the decoder's
`head?`-of-`filterMap` returns that committed result, and every other candidate
is equal to it (the block run is unique by `b64_block_run_of_boundary`, the
tail by `b64TailDecodeFull_unambiguous`).  `[propext, Quot.sound]`-only. -/

/-- The committed encode of `bs` produces a `decodeFullB64`-candidate: the block
run `blocks` decodes over the concatenation at the `m₁` boundary, and its
tail decodes to the committed terminal tail. -/
theorem decodeFullB64_mem_encode (bs : List UInt8) {n : Nat} {s : Bytes n}
    (he : encodeB64 bs = some ⟨n, s⟩) :
    bs ∈ (decodeRepeat b64BlockElem b64BlockConsumesByte n s).filterMap
      (fun ⟨blocks, t⟩ =>
        match decodeFull b64TailElem b64TailConsumesByte t.remaining t.bytes with
        | some tail => if tail.length ≤ 1 then some (blocks.flatten ++ tail.flatten) else none
        | none => none) := by
  let blocks := (b64Split_ofBytes (b64OfBytes bs)).1
  let tail := (b64Split_ofBytes (b64OfBytes bs)).2
  cases heb : encodeRepeat b64BlockElem blocks with
  | none =>
      unfold encodeB64 encodeB64' at he
      simp [blocks, heb] at he
  | some b =>
      cases het : encodeB64Tail tail with
      | none =>
          unfold encodeB64 encodeB64' at he
          simp [blocks, tail, heb, het] at he
      | some t =>
          rcases b with ⟨m₁, blkBytes⟩
          rcases t with ⟨m₂, tailBytes⟩
          have hpair : (⟨m₁ + m₂, Codec.concat blkBytes tailBytes⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by
            have he' : some (⟨m₁ + m₂, Codec.concat blkBytes tailBytes⟩ : Sigma fun k => Bytes k) = some ⟨n, s⟩ := by
              unfold encodeB64 encodeB64' at he
              simpa [blocks, tail, heb, het] using he
            exact Option.some.inj he'
          cases hpair
          have hblkmem : (blocks, Suffix.empty m₁) ∈ decodeRepeat b64BlockElem b64BlockConsumesByte m₁ blkBytes :=
            (decodeRepeat_spec b64BlockElem b64BlockConsumesByte blocks m₁ blkBytes (Suffix.empty m₁)).2
              ⟨cast (congrArg Bytes (Nat.sub_zero m₁).symm) blkBytes, (prepend_empty_eq blkBytes).symm,
                (relRepeat_cast (Rel b64BlockElem) blocks (Nat.sub_zero m₁).symm blkBytes).2
                  (encodeRepeat_rel b64BlockElem blocks heb)⟩
          have hblkpre : (blocks, Suffix.drop m₁ (Codec.concat blkBytes tailBytes)) ∈
              decodeRepeat b64BlockElem b64BlockConsumesByte (m₁ + m₂) (Codec.concat blkBytes tailBytes) :=
            decodeRepeat_prefix_concat b64BlockElem b64BlockConsumesByte blocks blkBytes tailBytes hblkmem
          have hflat : blocks.flatten ++ tail = bs := by
            dsimp [blocks, tail]
            rw [b64Split_ofBytes_shape (b64OfBytes bs), b64BytesOf_ofBytes bs]
          rw [List.mem_filterMap]
          refine ⟨(blocks, Suffix.drop m₁ (Codec.concat blkBytes tailBytes)), hblkpre, ?_⟩
          by_cases hne : tail = []
          · -- empty tail: `tail = []`
            rw [hne] at het
            have ht : decodeFull b64TailElem b64TailConsumesByte
                (Suffix.drop m₁ (Codec.concat blkBytes tailBytes)).remaining
                (Suffix.drop m₁ (Codec.concat blkBytes tailBytes)).bytes = some [] :=
              decodeFull_b64Tail_suffix_nil (sb := blkBytes) (st := tailBytes) het
            simp [ht]
            rw [hne] at hflat
            simpa using hflat
          · -- non-empty tail
            have ht : decodeFull b64TailElem b64TailConsumesByte
                (Suffix.drop m₁ (Codec.concat blkBytes tailBytes)).remaining
                (Suffix.drop m₁ (Codec.concat blkBytes tailBytes)).bytes = some [tail] :=
              decodeFull_b64Tail_suffix_cons tail (sb := blkBytes) (st := tailBytes) het hne
            simp [ht]
            rw [hflat]

/-- The whole-input roundtrip: `decodeFullB64 (encodeB64 bs) = some bs`. The
membership half is `decodeFullB64_mem_encode`; the singleton half pins every
`head?`-of-`filterMap` candidate to `bs` via the boundary pin + block/tail
uniqueness.  `[propext, Quot.sound]`-only. -/
theorem decodeFullB64_roundtrip (bs : List UInt8) {n : Nat} {s : Bytes n}
    (he : encodeB64 bs = some ⟨n, s⟩) :
    decodeFullB64 s = some bs := by
  unfold decodeFullB64
  apply head?_eq_some_of_mem_eq bs
  · exact decodeFullB64_mem_encode bs he
  · intro x hx
    rw [List.mem_filterMap] at hx
    rcases hx with ⟨pr, hmem, hfx⟩
    rcases pr with ⟨blocks', t'⟩
    cases htaildec : decodeFull b64TailElem b64TailConsumesByte t'.remaining t'.bytes with
    | none =>
        simp [htaildec] at hfx
    | some tail' =>
        -- recover the committed encode components
        let blocks := (b64Split_ofBytes (b64OfBytes bs)).1
        let tail := (b64Split_ofBytes (b64OfBytes bs)).2
        cases heb : encodeRepeat b64BlockElem blocks with
        | none =>
            unfold encodeB64 encodeB64' at he
            simp [blocks, heb] at he
        | some b =>
            cases het : encodeB64Tail tail with
            | none =>
                unfold encodeB64 encodeB64' at he
                simp [blocks, tail, heb, het] at he
            | some t =>
                rcases b with ⟨m₁, blkBytes⟩
                rcases t with ⟨m₂, tailBytes⟩
                have hpair : (⟨m₁ + m₂, Codec.concat blkBytes tailBytes⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by
                  have he' : some (⟨m₁ + m₂, Codec.concat blkBytes tailBytes⟩ : Sigma fun k => Bytes k) = some ⟨n, s⟩ := by
                    unfold encodeB64 encodeB64' at he
                    simpa [blocks, tail, heb, het] using he
                  exact Option.some.inj he'
                cases hpair
                have hflat : blocks.flatten ++ tail = bs := by
                  dsimp [blocks, tail]
                  rw [b64Split_ofBytes_shape (b64OfBytes bs), b64BytesOf_ofBytes bs]
                -- recover the block-run relation from the decoded candidate
                rcases (decodeRepeat_spec b64BlockElem b64BlockConsumesByte blocks'
                    (m₁ + m₂) (Codec.concat blkBytes tailBytes) t').1 hmem with ⟨s₀, hs, hblocks'⟩
                -- recover the tail-run relation from the decoded tail
                have htailmem : (tail', Suffix.empty t'.remaining) ∈
                    decodeRepeat b64TailElem b64TailConsumesByte t'.remaining t'.bytes :=
                  decodeFull_some b64TailElem b64TailConsumesByte t'.bytes tail' htaildec
                rcases (decodeRepeat_spec b64TailElem b64TailConsumesByte tail'
                    t'.remaining t'.bytes (Suffix.empty t'.remaining)).1 htailmem with ⟨s₀t, htbs, htail⟩
                -- the decoded tail list relates to t'.bytes (bridging the `- 0` length)
                have htailn : relRepeat (Rel b64TailElem) tail' t'.remaining t'.bytes := by
                  have hs₀t : cast (congrArg Bytes (Nat.sub_zero t'.remaining)) s₀t = t'.bytes := by
                    rw [prepend_empty s₀t] at htbs
                    exact htbs.symm
                  have htailcast : relRepeat (Rel b64TailElem) tail' t'.remaining
                      (cast (congrArg Bytes (Nat.sub_zero t'.remaining)) s₀t) :=
                    (relRepeat_cast (Rel b64TailElem) tail' (Nat.sub_zero t'.remaining) s₀t).2 htail
                  rw [hs₀t] at htailcast
                  exact htailcast
                -- the boundary pin inputs
                have henc : relRepeat (Rel b64BlockElem) blocks m₁ blkBytes :=
                  encodeRepeat_rel b64BlockElem blocks heb
                have hm₂ : m₂ = 0 ∨ m₂ = 4 := encodeB64Tail_len tail het
                have htail_ne_of_m₂ : m₂ ≠ 0 → tail ≠ [] := by
                  intro hm₂ne htnil
                  rw [htnil] at het
                  have hge := Option.some.inj het
                  have hm₂zero : m₂ = 0 := (congrArg Sigma.fst hge).symm
                  exact hm₂ne hm₂zero
                have hpad : m₂ ≠ 0 → ∃ i : Fin m₂, (tailBytes i).toNat = 61 := by
                  intro hm₂ne
                  exact encodeB64Tail_has_pad tail (htail_ne_of_m₂ hm₂ne) het
                -- the boundary pin
                have hbnd : t'.remaining = m₂ :=
                  b64_boundary_pin blkBytes tailBytes blocks blocks' tail' t' s₀ henc hblocks' htailn
                    hs.symm hm₂ hpad
                -- block-run uniqueness
                have hblocks_eq : blocks' = blocks :=
                  b64_block_run_of_boundary blkBytes tailBytes blocks blocks' t' s₀ henc hblocks'
                    hs.symm hbnd
                -- extract x from the filter step
                have hx : x = blocks'.flatten ++ tail'.flatten := by
                  simp [htaildec] at hfx
                  exact hfx.2.symm
                rw [hblocks_eq] at hx
                -- tail pin: the decoded tail flattens to the committed tail
                have htailflat : tail'.flatten = tail := by
                  -- bridge t'.bytes to tailBytes via the boundary (prepend_concat_suffix)
                  have hbytescast : cast (congrArg Bytes hbnd) t'.bytes = tailBytes := by
                    apply Bytes.ext
                    intro i
                    rw [cast_bytes_val' (e := hbnd)]
                    have hread := prepend_suffix_read blkBytes tailBytes t' s₀ hs.symm
                        ⟨i.val, Nat.lt_of_lt_of_eq i.isLt hbnd.symm⟩
                    rw [hread]
                    have hk : m₁ + m₂ - t'.remaining = m₁ := by rw [hbnd]; omega
                    simpa [hk, Nat.add_comm, Nat.add_left_comm] using (concat_tail_read blkBytes tailBytes i)
                  -- the decoded tail on m₂/(cast t'.bytes) equals some tail'
                  have htaildec' : decodeFull b64TailElem b64TailConsumesByte m₂
                      (cast (congrArg Bytes hbnd) t'.bytes) = some tail' := by
                    have hc := decodeFull_cast b64TailElem b64TailConsumesByte hbnd t'.bytes
                    rw [← hc] at htaildec
                    exact htaildec
                  have htaildec'' : decodeFull b64TailElem b64TailConsumesByte m₂ tailBytes = some tail' := by
                    rw [hbytescast] at htaildec'
                    exact htaildec'
                  cases htailc : tail with
                  | nil =>
                      have het' : encodeB64Tail [] = some ⟨m₂, tailBytes⟩ := by
                        simpa [htailc] using het
                      have htail_enc' : decodeFull b64TailElem b64TailConsumesByte m₂ tailBytes = some [] := by
                        simpa using (decodeFull_b64Tail_of_encode [] het')
                      have htail' : tail' = [] := (Option.some.inj (htail_enc'.symm.trans htaildec'')).symm
                      rw [htail']
                      rfl
                  | cons b rest =>
                      have het' : encodeB64Tail (b :: rest) = some ⟨m₂, tailBytes⟩ := by
                        simpa [htailc] using het
                      have htail_enc' : decodeFull b64TailElem b64TailConsumesByte m₂ tailBytes = some [b :: rest] := by
                        simpa using (decodeFull_b64Tail_of_encode (b :: rest) het')
                      have htail' : tail' = [b :: rest] := (Option.some.inj (htail_enc'.symm.trans htaildec'')).symm
                      rw [htail']
                      simp
                rw [hx, htailflat]
                exact hflat

/-! ## Rejection (task 3.1)

The whole-input decoder rejects every malformed input: a byte outside the
alphabet, `=` in an illegal position, wrong arity, and any data after the
terminal `=` run.  Rejection is `decodeFullB64 s = none`, proved as an inequation
over the composition: the full-block run cannot consume a block containing `=`,
and the leftover bytes cannot decode as a terminal tail (which must be a single
padded block). -/

/-- A successful `decodeFullB64 s = some v` decomposes into a full-block run
prefix `blocks` and a terminal tail `tails` that decode (with `tails.length ≤ 1`,
the D8 single-block guard), with `v` their flatten.  This is the contrapositive
bridge: to show `= none`, assume `= some v`, reach a length/\alphabet
contradiction from this decomposition. -/
theorem decodeFullB64_some {n : Nat} (s : Bytes n) (v : List UInt8)
    (h : decodeFullB64 s = some v) :
    ∃ (blocks : List (List UInt8)) (t : Suffix n) (tails : List (List UInt8)),
      (blocks, t) ∈ decodeRepeat b64BlockElem b64BlockConsumesByte n s ∧
      decodeFull b64TailElem b64TailConsumesByte t.remaining t.bytes = some tails ∧
      tails.length ≤ 1 ∧
      blocks.flatten ++ tails.flatten = v := by
  unfold decodeFullB64 at h
  have hmem : v ∈ (decodeRepeat b64BlockElem b64BlockConsumesByte n s).filterMap
      (fun ⟨blocks, t⟩ =>
        match decodeFull b64TailElem b64TailConsumesByte t.remaining t.bytes with
        | some tail => if tail.length ≤ 1 then some (blocks.flatten ++ tail.flatten) else none
        | none => none) := by
    rcases List.head?_eq_some_iff.mp h with ⟨ys, hys⟩
    rw [hys]
    simp
  rw [List.mem_filterMap] at hmem
  rcases hmem with ⟨pr, hmemp, hfx⟩
  rcases pr with ⟨blocks, t⟩
  cases hd : decodeFull b64TailElem b64TailConsumesByte t.remaining t.bytes with
  | none => simp [hd] at hfx
  | some tail =>
      have hlen : tail.length ≤ 1 := by
        by_cases hlen : tail.length ≤ 1
        · exact hlen
        · simp [hd, hlen] at hfx
      refine ⟨blocks, t, tail, hmemp, hd, hlen, ?_⟩
      simpa [hd, hlen] using hfx

/-- The `Zg==AAAA` byte vector (the flagship rejection input). -/
def zgAAAA : Bytes 8 := fun i : Fin 8 => [0x5A, 0x67, 0x3D, 0x3D, 0x41, 0x41, 0x41, 0x41][i]

/-- Rejection: trailing data after a terminal `=` (`Zg==AAAA`) is `none`.  The
full-block run cannot consume a 4-char block containing `=` (its element is
alphabet-only), so it consumes nothing; the terminal tail must then consume the
whole input, whose second 4-byte block (`AAAA`) has no `=` pad — but a tail block
always contains `=` (`Rel_b64TailElem_has_pad`).  Contradiction. -/
theorem decodeFullB64_reject_ZgAAAA :
    decodeFullB64 zgAAAA = none := by
  let s₀ : Bytes 8 := zgAAAA
  change decodeFullB64 s₀ = none
  cases h : decodeFullB64 s₀ with
  | none => rfl
  | some v =>
      rcases decodeFullB64_some s₀ v h with ⟨blocks, t, tails, hmem, htail, _, _⟩
      rcases (decodeRepeat_spec b64BlockElem b64BlockConsumesByte blocks 8 s₀ t).1 hmem with ⟨s₁, hs, hrel⟩
      have hcanon : ∀ i : Fin (8 - t.remaining), b64Char (s₁ i) = true :=
        relRepeat_forall b64Char (fun x {m} tt ht => Rel_b64BlockElem_canonical (t := tt) ht) blocks (8 - t.remaining) s₁ hrel
      -- s₀ 2 = 61: a block prefix reaching index 2 would read that pad as an alphabet byte
      have hblock_stop : ¬ (2 < 8 - t.remaining) := by
        intro hi2
        have hs₁2 : s₁ ⟨2, hi2⟩ = s₀ ⟨2, by decide⟩ := by
          rw [hs]
          exact (Codec.prepend_prefix_read t s₁ ⟨2, by decide⟩ hi2).symm
        have hs₁2pad : (s₁ ⟨2, hi2⟩).toNat = 61 := by
          rw [hs₁2]
          rfl
        have hch := hcanon ⟨2, hi2⟩
        unfold b64Char at hch
        rw [hs₁2pad] at hch
        have hfalse : b64Valid 61 = false := by rfl
        rw [hfalse] at hch
        exact Bool.false_ne_true hch
      -- the block run is empty or consumes a first 4-byte block; both contradict s₀ 2 = 61
      cases blocks with
      | cons b bs =>
          rw [relRepeat_cons] at hrel
          rcases hrel with ⟨m, hm, sb, srest, hsplice, hb, _⟩
          have hm4 : m = 4 := Rel_b64BlockElem_len b sb hb
          have h4le : 4 ≤ 8 - t.remaining := by
            simpa [hm4] using hm
          have hle2 : 8 - t.remaining ≤ 2 := Nat.le_of_not_gt hblock_stop
          have h42 : 4 ≤ 2 := Nat.le_trans h4le hle2
          exact False.elim ((by omega : ¬ (4 : Nat) ≤ 2) h42)
      | nil =>
          rw [relRepeat_nil] at hrel
          have hrem8 : t.remaining = 8 := by
            have hz : 8 - t.remaining = 0 := hrel
            have htle : t.remaining ≤ 8 := t.hle
            have hle8 : 8 ≤ t.remaining := by
              exact (Nat.sub_eq_zero_iff_le.mp hz)
            exact Nat.le_antisymm htle hle8
          have htail_mem : (tails, Suffix.empty t.remaining) ∈ decodeRepeat b64TailElem b64TailConsumesByte t.remaining t.bytes :=
            decodeFull_some b64TailElem b64TailConsumesByte t.bytes tails htail
          rcases (decodeRepeat_spec b64TailElem b64TailConsumesByte tails t.remaining t.bytes (Suffix.empty t.remaining)).1 htail_mem with ⟨s₂, hs₂, htailrel⟩
          have htailrel' : relRepeat (Rel b64TailElem) tails t.remaining t.bytes := by
            have hne : t.bytes = cast (congrArg Bytes (Nat.sub_zero t.remaining)) s₂ := by
              rw [hs₂]
              exact prepend_empty_eq s₂
            rw [hne]
            exact (relRepeat_cast (Rel b64TailElem) tails (Nat.sub_zero t.remaining) s₂).1 htailrel
          have ht_sid : t = Suffix.id 8 s₀ :=
            decodeRepeat_nil_mem_eq_id b64BlockElem b64BlockConsumesByte s₀ t hmem
          subst t
          dsimp [Suffix.id] at htailrel'
          cases tails with
          | nil =>
              rw [relRepeat_nil] at htailrel'
              exact False.elim ((by omega : ¬ (8 : Nat) = 0) htailrel')
          | cons x xs =>
              rw [relRepeat_cons] at htailrel'
              rcases htailrel' with ⟨m₁, hm₁, sb₁, srest, hsplice1, hx, hrest⟩
              have hm₁4 : m₁ = 4 := Rel_b64TailElem_len x sb₁ hx
              subst m₁
              cases xs with
              | nil =>
                  rw [relRepeat_nil] at hrest
                  exact False.elim ((by omega : ¬ (4 : Nat) = 0) hrest)
              | cons y ys =>
                  rw [relRepeat_cons] at hrest
                  rcases hrest with ⟨m₂, hm₂, sb₂, srest2, hsplice2, hy, _⟩
                  have hm₂4 : m₂ = 4 := Rel_b64TailElem_len y sb₂ hy
                  subst m₂
                  have hpad₂ : ∃ i : Fin 4, (sb₂ i).toNat = 61 := Rel_b64TailElem_has_pad y sb₂ hy
                  have hall : ∀ i : Fin 4, (sb₂ i).toNat = 65 := by
                    intro i
                    dsimp [Suffix.id] at hsplice1 hsplice2 hm₁ hm₂
                    have hb4 : bdrop 4 s₀ = srest := by
                      rw [hsplice1]
                      exact bdrop_splice hm₁ sb₁ srest
                    have hb4' : bdrop 4 s₀ = splice hm₂ sb₂ srest2 := by
                      rw [hb4, hsplice2]
                    have hsbread : sb₂ i = (bdrop 4 s₀) ⟨i.val, show i.val < 4 by exact i.isLt⟩ := by
                      rw [hb4']
                      exact (Codec.splice_prefix_read hm₂ sb₂ srest2 ⟨i.val, show i.val < 4 by exact i.isLt⟩ i.isLt).symm
                    rw [hsbread]
                    dsimp [bdrop]
                    rcases i with ⟨k, hk⟩
                    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := nat_lt_four k hk
                    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
                  rcases hpad₂ with ⟨i, hpad⟩
                  exact False.elim (by
                    have h65 : (sb₂ i).toNat = 65 := hall i
                    have hbot : (61 : Nat) = 65 := hpad.symm.trans h65
                    have hbad : (61 : Nat) ≠ 65 := by intro h; cases h
                    exact hbad hbot)

/-! ## Rejection family (task 3.1)

The RFC 4648 §4 malformed-input rejection vectors, re-expressed over the
uniform `decodeFullB64`.  Each is `decodeFullB64 s = none`, proved as an
inequation over the block-run + terminal-tail composition via `decodeFullB64_some`
and the pad-dichotomy primitives. -/

/-- A `b64TailElem`-related string's first byte is a valid alphabet character
(never `=` and never invalid).  `b64BlockApply` (hence `b64TailApply`) recovers the
tail value via `b64BlockUnapply`, whose first char is `valToB64 (v0 / 4)` — a valid,
non-pad alphabet byte (`valToB64_valid`).  With `a = List.ofFn s` that pins
`s ⟨0, ·⟩`. -/
theorem Rel_b64TailElem_first_char (x : List UInt8) {n : Nat} (s : Bytes n)
    (h : Rel b64TailElem x s) :
    b64Valid (s ⟨0, by
      have hn4 : n = 4 := Rel_b64TailElem_len x s h
      omega⟩).toNat = true := by
  unfold b64TailElem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, ha, hr⟩
  have hofn : List.ofFn s = a := Rel_count_satisfy_ofFn b64OrPad 4 a s hr
  have hn4 : n = 4 := Rel_count_satisfy_len b64OrPad 4 a s hr
  subst n
  unfold b64TailIso at ha
  change b64TailApply a = some x at ha
  unfold b64TailApply at ha
  cases hb : b64BlockApply a with
  | none => simp [hb] at ha
  | some bl =>
    cases bl with
    | nil => simp [hb] at ha
    | cons b0 bl1 =>
      cases bl1 with
      | nil =>
        have hun : b64BlockUnapply [b0] = some a := (b64BlockIso_law a [b0]).1 (by simpa using hb)
        have htail : a = [toByte (valToB64 (b0.toNat / 4)), toByte (valToB64 ((b0.toNat % 4) * 16)), toByte 61, toByte 61] := by
          simp [b64BlockUnapply] at hun
          exact hun.symm
        rw [← hofn] at htail
        have hc0 : s ⟨0, by decide⟩ = toByte (valToB64 (b0.toNat / 4)) := by
          have hsucc : List.ofFn s = s ⟨0, by decide⟩ :: List.ofFn (fun i : Fin 3 => s i.succ) := List.ofFn_succ
          have hcons : s ⟨0, by decide⟩ :: List.ofFn (fun i : Fin 3 => s i.succ) = [toByte (valToB64 (b0.toNat / 4)), toByte (valToB64 ((b0.toNat % 4) * 16)), toByte 61, toByte 61] := by
            rw [← hsucc, htail]
          have hhead := congrArg (fun l : List UInt8 => l.head!) hcons
          simp [List.head!] at hhead
          exact hhead
        have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
        have hc0v : b64Valid (valToB64 (b0.toNat / 4)) = true :=
          valToB64_valid (b0.toNat / 4) (by omega)
        rw [hc0, toByte_valToB64 (b0.toNat / 4) (by omega)]
        exact hc0v
      | cons b1 bl2 =>
        cases bl2 with
        | nil =>
          have hun : b64BlockUnapply [b0, b1] = some a := (b64BlockIso_law a [b0, b1]).1 (by simpa using hb)
          have htail : a = [toByte (valToB64 (b0.toNat / 4)), toByte (valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16)), toByte (valToB64 ((b1.toNat % 16) * 4)), toByte 61] := by
            simp [b64BlockUnapply] at hun
            exact hun.symm
          rw [← hofn] at htail
          have hc0 : s ⟨0, by decide⟩ = toByte (valToB64 (b0.toNat / 4)) := by
            have hsucc : List.ofFn s = s ⟨0, by decide⟩ :: List.ofFn (fun i : Fin 3 => s i.succ) := List.ofFn_succ
            have hcons : s ⟨0, by decide⟩ :: List.ofFn (fun i : Fin 3 => s i.succ) = [toByte (valToB64 (b0.toNat / 4)), toByte (valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16)), toByte (valToB64 ((b1.toNat % 16) * 4)), toByte 61] := by
              rw [← hsucc, htail]
            have hhead := congrArg (fun l : List UInt8 => l.head!) hcons
            simp [List.head!] at hhead
            exact hhead
          have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
          have hc0v : b64Valid (valToB64 (b0.toNat / 4)) = true :=
            valToB64_valid (b0.toNat / 4) (by omega)
          rw [hc0, toByte_valToB64 (b0.toNat / 4) (by omega)]
          exact hc0v
        | cons _ _ => simp [hb] at ha

/-- A 4-byte input whose first byte is not a valid alphabet character is rejected:
the block run and the terminal tail both force the first byte to be `b64Valid`
(`Rel_b64BlockElem_canonical` / `Rel_b64TailElem_first_char`), so a first byte that
is `=` or `!` cannot decode. -/
theorem decodeFullB64_reject_first_invalid (s : Bytes 4)
    (hbad : b64Valid (s ⟨0, by decide⟩).toNat = false) :
    decodeFullB64 s = none := by
  cases h : decodeFullB64 s with
  | none => rfl
  | some v =>
      rcases decodeFullB64_some s v h with ⟨blocks, t, tails, hmem, htail, _, _⟩
      rcases (decodeRepeat_spec b64BlockElem b64BlockConsumesByte blocks 4 s t).1 hmem with ⟨s₁, hs, hrel⟩
      have hcanon : ∀ i : Fin (4 - t.remaining), b64Char (s₁ i) = true :=
        relRepeat_forall b64Char (fun x {m} tt ht => Rel_b64BlockElem_canonical ht) blocks (4 - t.remaining) s₁ hrel
      cases blocks with
      | cons b bs =>
          -- a block consumes the first byte; that byte is b64Valid
          rw [relRepeat_cons] at hrel
          rcases hrel with ⟨m, hm, sb, srest, hsplice, hb, _⟩
          have hm4 : m = 4 := Rel_b64BlockElem_len b sb hb
          subst m
          have hfirst : b64Valid (s ⟨0, by decide⟩).toNat = true := by
            have hge : 0 < 4 - t.remaining := by omega
            have hsread : s ⟨0, by decide⟩ = s₁ ⟨0, hge⟩ := by
              rw [hs]
              exact (Codec.prepend_prefix_read t s₁ ⟨0, by decide⟩ hge)
            have hc : b64Char (s₁ ⟨0, hge⟩) = true := hcanon ⟨0, hge⟩
            rw [hsread]
            exact hc
          have hfalse : b64Valid (s ⟨0, by decide⟩).toNat = false := hbad
          rw [hfirst] at hfalse
          exact False.elim (Bool.false_ne_true hfalse.symm)
      | nil =>
          -- no block consumed: t = Suffix.id 4 s, the tail decodes the whole input
          have ht : t = Suffix.id 4 s := decodeRepeat_nil_mem_eq_id b64BlockElem b64BlockConsumesByte s t hmem
          subst t
          have htail_mem : (tails, Suffix.empty 4) ∈ decodeRepeat b64TailElem b64TailConsumesByte 4 s := by
            simpa using (decodeFull_some b64TailElem b64TailConsumesByte s tails htail)
          rcases (decodeRepeat_spec b64TailElem b64TailConsumesByte tails 4 s (Suffix.empty 4)).1 htail_mem with ⟨s₂, hs₂, htailrel⟩
          have htailrel' : relRepeat (Rel b64TailElem) tails 4 s := by
            have hne : s = cast (congrArg Bytes (Nat.sub_zero 4)) s₂ := by
              rw [hs₂]
              exact prepend_empty_eq s₂
            rw [hne]
            exact (relRepeat_cast (Rel b64TailElem) tails (Nat.sub_zero 4) s₂).1 htailrel
          cases tails with
          | nil => rw [relRepeat_nil] at htailrel'; omega
          | cons x xs =>
              rw [relRepeat_cons] at htailrel'
              rcases htailrel' with ⟨m, hm, sb, srest, hsplice, hx, _⟩
              have hm4 : m = 4 := Rel_b64TailElem_len x sb hx
              subst m
              have hfirst : b64Valid (s ⟨0, by decide⟩).toNat = true := by
                have hf_sb : b64Valid (sb ⟨0, by decide⟩).toNat = true :=
                  Rel_b64TailElem_first_char x sb hx
                have hsread : s ⟨0, by decide⟩ = sb ⟨0, by decide⟩ := by
                  rw [hsplice]
                  exact (Codec.splice_prefix_read hm sb srest ⟨0, by decide⟩ (by decide)).symm
                rw [hsread]
                exact hf_sb
              have hfalse : b64Valid (s ⟨0, by decide⟩).toNat = false := hbad
              rw [hfirst] at hfalse
              exact False.elim (Bool.false_ne_true hfalse.symm)

/-- Invalid base64 character `!` (0x21) is rejected. -/
def bangGEqEq : Bytes 4 := fun i => [0x21, 0x67, 0x3D, 0x3D][i]

/-- `=` in the first position (illegal padding) is rejected. -/
def eqGEqEq : Bytes 4 := fun i => [0x3D, 0x67, 0x3D, 0x3D][i]

/-- Two-char input (wrong arity) is rejected. -/
def zgTwo : Bytes 2 := fun i => [0x5A, 0x67][i]

theorem decodeFullB64_reject_invalid_char : decodeFullB64 bangGEqEq = none := by
  exact decodeFullB64_reject_first_invalid bangGEqEq (by decide)

theorem decodeFullB64_reject_pad_first : decodeFullB64 eqGEqEq = none := by
  exact decodeFullB64_reject_first_invalid eqGEqEq (by decide)

/-- Wrong-arity input `Zg` (2 base64 chars) is rejected: neither a full 4-char block
nor a 4-char padded tail can be formed from 2 bytes. -/
theorem decodeFullB64_reject_bad_length : decodeFullB64 zgTwo = none := by
  cases h : decodeFullB64 zgTwo with
  | none => rfl
  | some v =>
      rcases decodeFullB64_some zgTwo v h with ⟨blocks, t, tails, hmem, htail, _, _⟩
      rcases (decodeRepeat_spec b64BlockElem b64BlockConsumesByte blocks 2 zgTwo t).1 hmem with ⟨s₁, hs, hrel⟩
      cases blocks with
      | nil =>
          have ht : t = Suffix.id 2 zgTwo := decodeRepeat_nil_mem_eq_id b64BlockElem b64BlockConsumesByte zgTwo t hmem
          subst t
          have htail_mem : (tails, Suffix.empty 2) ∈ decodeRepeat b64TailElem b64TailConsumesByte 2 zgTwo := by
            simpa using (decodeFull_some b64TailElem b64TailConsumesByte zgTwo tails htail)
          rcases (decodeRepeat_spec b64TailElem b64TailConsumesByte tails 2 zgTwo (Suffix.empty 2)).1 htail_mem with ⟨s₂, hs₂, htailrel⟩
          have htailrel' : relRepeat (Rel b64TailElem) tails 2 zgTwo := by
            have hne : zgTwo = cast (congrArg Bytes (Nat.sub_zero 2)) s₂ := by
              rw [hs₂]
              exact prepend_empty_eq s₂
            rw [hne]
            exact (relRepeat_cast (Rel b64TailElem) tails (Nat.sub_zero 2) s₂).1 htailrel
          cases tails with
          | nil => rw [relRepeat_nil] at htailrel'; omega
          | cons x xs =>
              rw [relRepeat_cons] at htailrel'
              rcases htailrel' with ⟨m, hm, sb, srest, hsplice, hx, _⟩
              have hm4 : m = 4 := Rel_b64TailElem_len x sb hx
              subst m
              omega
      | cons b bs =>
          rw [relRepeat_cons] at hrel
          rcases hrel with ⟨m, hm, sb, srest, hsplice, hb, _⟩
          have hm4 : m = 4 := Rel_b64BlockElem_len b sb hb
          subst m
          omega

/-! ## Conformance: canonical encoding (task 4.2, base64)

The whole-input `encodeB64` output is canonical: alphabet-only full blocks
followed by a single padded tail, whose pad is terminal and RFC-arity-correct
(1-byte tail → `==`, 2-byte → `=`, 3-byte → none).  Stated as a decomposition
over `List.ofFn` (no `Fin` index bookkeeping); the empty tail is reported as
`List.ofFn tailBytes = []`.  `[propext, Quot.sound]`-only. -/

/-- A tail encoding is either empty (length 0) or a single 4-byte padded block
whose pad bytes are exactly the RFC tail (1 byte → `==`, 2 bytes → `=`).  The
non-pad prefix is alphabet-only, the pad is terminal. -/
theorem b64TailBlock_canonical (tail : List UInt8) {m : Nat} {t : Bytes m}
    (he : encodeB64Tail tail = some ⟨m, t⟩) :
    (tail = [] ∧ m = 0) ∨
    (∃ b, tail = [b] ∧ m = 4 ∧ ∃ c0 c1 : UInt8,
      List.ofFn t = [c0, c1, toByte 61, toByte 61] ∧
      b64Valid c0.toNat = true ∧ b64Valid c1.toNat = true) ∨
    (∃ b0 b1, tail = [b0, b1] ∧ m = 4 ∧ ∃ c0 c1 c2 : UInt8,
      List.ofFn t = [c0, c1, c2, toByte 61] ∧
      b64Valid c0.toNat = true ∧ b64Valid c1.toNat = true ∧ b64Valid c2.toNat = true) := by
  cases tail with
  | nil =>
      have hs : (⟨0, (Codec.emptyBytes : Bytes 0)⟩ : Sigma fun k => Bytes k) = ⟨m, t⟩ := by
        simpa [encodeB64Tail] using he
      cases hs
      left
      simp
  | cons b t1 =>
      cases t1 with
      | nil =>
          have henc : Codec.encode b64TailElem [b] = some ⟨m, t⟩ := by simpa [encodeB64Tail] using he
          have hrel : Rel b64TailElem [b] t := encode_rel b64TailElem [b] henc
          have hm4 : m = 4 := Rel_b64TailElem_len [b] t hrel
          subst m
          right; left
          refine ⟨b, rfl, rfl, ?_⟩
          unfold b64TailElem at hrel
          rw [Rel_iso] at hrel
          rcases hrel with ⟨a, ha, hr⟩
          have hofn : List.ofFn t = a := Rel_count_satisfy_ofFn b64OrPad 4 a t hr
          unfold b64TailIso at ha
          change b64TailApply a = some [b] at ha
          unfold b64TailApply at ha
          cases hb : b64BlockApply a with
          | none => simp [hb] at ha
          | some bl =>
            cases bl with
            | nil => simp [hb] at ha
            | cons x bl1 =>
              cases bl1 with
              | nil =>
                have hun : b64BlockUnapply [x] = some a := (b64BlockIso_law a [x]).1 (by simpa using hb)
                simp [b64BlockUnapply] at hun
                have ha' : a = [toByte (valToB64 (x.toNat / 4)), toByte (valToB64 ((x.toNat % 4) * 16)), toByte 61, toByte 61] := hun.symm
                have hx : x.toNat < 256 := UInt8.toNat_lt x
                refine ⟨toByte (valToB64 (x.toNat / 4)), toByte (valToB64 ((x.toNat % 4) * 16)), ?_, ?_, ?_⟩
                · rw [hofn]; exact ha'
                · rw [toByte_valToB64 (x.toNat / 4) (by omega)]
                  exact valToB64_valid (x.toNat / 4) (by omega)
                · rw [toByte_valToB64 ((x.toNat % 4) * 16) (by omega)]
                  exact valToB64_valid ((x.toNat % 4) * 16) (by omega)
              | cons b2 bl2 =>
                cases bl2 with
                | nil => simp [hb] at ha
                | cons _ _ => simp [hb] at ha
      | cons b1 t2 =>
          cases t2 with
          | nil =>
            have henc : Codec.encode b64TailElem [b, b1] = some ⟨m, t⟩ := by simpa [encodeB64Tail] using he
            have hrel : Rel b64TailElem [b, b1] t := encode_rel b64TailElem [b, b1] henc
            have hm4 : m = 4 := Rel_b64TailElem_len [b, b1] t hrel
            subst m
            right; right
            refine ⟨b, b1, rfl, rfl, ?_⟩
            unfold b64TailElem at hrel
            rw [Rel_iso] at hrel
            rcases hrel with ⟨a, ha, hr⟩
            have hofn : List.ofFn t = a := Rel_count_satisfy_ofFn b64OrPad 4 a t hr
            unfold b64TailIso at ha
            change b64TailApply a = some [b, b1] at ha
            unfold b64TailApply at ha
            cases hb : b64BlockApply a with
            | none => simp [hb] at ha
            | some bl =>
              cases bl with
              | nil => simp [hb] at ha
              | cons x bl1 =>
                cases bl1 with
                | nil => simp [hb] at ha
                | cons y bl2 =>
                  cases bl2 with
                  | nil =>
                    have hun : b64BlockUnapply [x, y] = some a := (b64BlockIso_law a [x, y]).1 (by simpa using hb)
                    simp [b64BlockUnapply] at hun
                    have ha' : a = [toByte (valToB64 (x.toNat / 4)), toByte (valToB64 ((x.toNat % 4) * 16 + y.toNat / 16)), toByte (valToB64 ((y.toNat % 16) * 4)), toByte 61] := hun.symm
                    have hx : x.toNat < 256 := UInt8.toNat_lt x
                    have hy : y.toNat < 256 := UInt8.toNat_lt y
                    refine ⟨toByte (valToB64 (x.toNat / 4)), toByte (valToB64 ((x.toNat % 4) * 16 + y.toNat / 16)), toByte (valToB64 ((y.toNat % 16) * 4)), ?_, ?_, ?_, ?_⟩
                    · rw [hofn]; exact ha'
                    · rw [toByte_valToB64 (x.toNat / 4) (by omega)]
                      exact valToB64_valid (x.toNat / 4) (by omega)
                    · rw [toByte_valToB64 ((x.toNat % 4) * 16 + y.toNat / 16) (by omega)]
                      exact valToB64_valid ((x.toNat % 4) * 16 + y.toNat / 16) (by omega)
                    · rw [toByte_valToB64 ((y.toNat % 16) * 4) (by omega)]
                      exact valToB64_valid ((y.toNat % 16) * 4) (by omega)
                  | cons _ _ => simp [hb] at ha
          | cons _ _ => simp [encodeB64Tail] at he

/-- `List.ofFn` lifts `b64Char` pointwise to list membership. -/
private theorem ofFn_mem_b64Char {m : Nat} (s : Bytes m)
    (h : ∀ i : Fin m, b64Char (s i) = true) :
    ∀ b : UInt8, b ∈ List.ofFn s → b64Valid b.toNat = true := by
  intro b hb
  rcases List.mem_iff_getElem.mp hb with ⟨i, hi, hi'⟩
  have hchar : b64Char (s ⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩) = true :=
    h ⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩
  unfold b64Char at hchar
  have hb_eq : b = s ⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩ := by
    exact ((List.getElem_ofFn hi).symm.trans hi').symm
  rw [hb_eq]
  exact hchar

/-- The whole-input `encodeB64` output decomposes into alphabet-only full
blocks plus a single RFC-arity padded tail (empty, `[·,·,=,=]`, or `[·,·,·,=]`),
so the output is canonical: alphabet-or-pad, with terminal, arity-correct `=`.
`[propext, Quot.sound]`-only. -/
theorem encodeB64_canonical (bs : List UInt8) {n : Nat} {s : Bytes n}
    (he : encodeB64 bs = some ⟨n, s⟩) :
    ∃ (blocks : List (List UInt8)) (m₁ m₂ : Nat) (blkBytes : Bytes m₁) (tailBytes : Bytes m₂),
      encodeRepeat b64BlockElem blocks = some ⟨m₁, blkBytes⟩ ∧
      encodeB64Tail (b64Split_ofBytes (b64OfBytes bs)).2 = some ⟨m₂, tailBytes⟩ ∧
      List.ofFn s = List.ofFn blkBytes ++ List.ofFn tailBytes ∧
      (∀ b : UInt8, b ∈ List.ofFn blkBytes → b64Valid b.toNat = true) ∧
      (List.ofFn tailBytes = [] ∨
        (∃ c0 c1 : UInt8, List.ofFn tailBytes = [c0, c1, toByte 61, toByte 61] ∧
          b64Valid c0.toNat = true ∧ b64Valid c1.toNat = true) ∨
        (∃ c0 c1 c2 : UInt8, List.ofFn tailBytes = [c0, c1, c2, toByte 61] ∧
          b64Valid c0.toNat = true ∧ b64Valid c1.toNat = true ∧ b64Valid c2.toNat = true)) := by
  let blocks := (b64Split_ofBytes (b64OfBytes bs)).1
  let tail := (b64Split_ofBytes (b64OfBytes bs)).2
  cases heb : encodeRepeat b64BlockElem blocks with
  | none => unfold encodeB64 encodeB64' at he; simp [blocks, heb] at he
  | some b =>
      cases het : encodeB64Tail tail with
      | none => unfold encodeB64 encodeB64' at he; simp [blocks, tail, heb, het] at he
      | some t =>
          rcases b with ⟨m₁, blkBytes⟩
          rcases t with ⟨m₂, tailBytes⟩
          have hpair : (⟨m₁ + m₂, Codec.concat blkBytes tailBytes⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by
            have he' : some (⟨m₁ + m₂, Codec.concat blkBytes tailBytes⟩ : Sigma fun k => Bytes k) = some ⟨n, s⟩ := by
              unfold encodeB64 encodeB64' at he
              simpa [blocks, tail, heb, het] using he
            exact Option.some.inj he'
          cases hpair
          refine ⟨blocks, m₁, m₂, blkBytes, tailBytes, ?_, ?_, ?_, ?_, ?_⟩
          · simpa using heb
          · simpa [tail] using het
          · exact Codec.ofFn_concat blkBytes tailBytes
          · exact ofFn_mem_b64Char blkBytes (encodeB64Block_nopad blocks (by simpa using heb))
          · rcases b64TailBlock_canonical tail (by simpa using het) with h0 | h1 | h2
            · left
              rcases h0 with ⟨_, hm0⟩
              subst m₂
              subst tail
              simpa [Codec.emptyBytes] using (show List.ofFn (Codec.emptyBytes : Bytes 0) = [] by rfl)
            · right; left
              rcases h1 with ⟨b0, hb0, hm4, c0, c1, hofn, hc0, hc1⟩
              subst m₂
              refine ⟨c0, c1, ?_, ?_, ?_⟩
              · simpa [tail] using hofn
              · exact hc0
              · exact hc1
            · right; right
              rcases h2 with ⟨b0, b1, hb0, hm4, c0, c1, c2, hofn, hc0, hc1, hc2⟩
              subst m₂
              refine ⟨c0, c1, c2, ?_, ?_, ?_, ?_⟩
              · simpa [tail] using hofn
              · exact hc0
              · exact hc1
              · exact hc2

/-! ## Converse (task 4.3) and injectivity (task 4.4)

`decodeFullB64 s = some v → encodeB64 v = some ⟨n, s⟩` (the decode→encode
converse: a successful decode re-encodes to the exact input) and
`encodeB64 v = encodeB64 v' = some ⟨n, s⟩ → v = v'` (injectivity).  Both
`[propext, Quot.sound]`-only. -/

/-- A `b64BlockElem`-related value is a 3-byte list (already in
`Rel_b64BlockElem_size`); lifted to a `relRepeat`, every block of a block-run is
exactly 3 bytes.  Proved by induction on the block list: each `cons` step's head
relates via `Rel b64BlockElem` over a 4-byte window, so `Rel_b64BlockElem_size`
pins its value to length 3, and the tail is handled by the IH. -/
theorem relB64Block_all_size3 :
    ∀ {blocks : List (List UInt8)} {m : Nat} (s : Bytes m),
      relRepeat (Rel b64BlockElem) blocks m s → ∀ b ∈ blocks, b.length = 3 := by
  intro blocks m s hrel
  induction blocks generalizing m s with
  | nil =>
      intro b hb
      simp at hb
  | cons x xs ih =>
      intro b hb
      rw [relRepeat_cons] at hrel
      rcases hrel with ⟨m₁, hm₁, s₁, s₂, _hs, hx, hxs⟩
      rw [List.mem_cons] at hb
      rcases hb with hbeq | hbmem
      · subst b
        exact Rel_b64BlockElem_size x s₁ hx
      · exact ih s₂ hxs b hbmem

/-- `b64Split` reconstructs a run of 3-byte blocks plus a ≤ 2-byte tail: given
`blocks` all length-3 and `tail.length ≤ 2`, splitting `blocks.flatten ++ tail`
recovers exactly `(blocks, tail)`.  This is the split-back fact the converse needs
to turn a decoded value `blocks.flatten ++ tail.flatten` back into the same
`blocks`/`tail` the encoder will re-emit. -/
theorem b64Split_blocks_tail (blocks : List (List UInt8)) (tail : List UInt8)
    (hblocks : ∀ b ∈ blocks, b.length = 3) (htail : tail.length ≤ 2) :
    b64Split (blocks.flatten ++ tail) = (blocks, tail) := by
  induction blocks generalizing tail with
  | nil =>
      cases tail with
      | nil => rfl
      | cons a t =>
          cases t with
          | nil => rfl
          | cons b t2 =>
              cases t2 with
              | nil => rfl
              | cons c t3 =>
                  simp at htail
  | cons b bs ih =>
      have hb : b.length = 3 := hblocks b (by simp)
      have hbs : ∀ b' ∈ bs, b'.length = 3 := by
        intro b' hb'; exact hblocks b' (by simp [hb'])
      cases b with
      | nil => simp at hb
      | cons b0 t0 =>
          cases t0 with
          | nil => simp at hb
          | cons b1 t1 =>
              cases t1 with
              | nil => simp at hb
              | cons b2 t2 =>
                  cases t2 with
                  | nil =>
                      show b64Split (b0 :: b1 :: b2 :: (bs.flatten ++ tail)) = ([b0, b1, b2] :: bs, tail)
                      rw [b64Split.eq_4]
                      rw [ih tail hbs htail]
                  | cons c t3 => simp at hb

/-! ## The converse: a successful decode re-encodes to the input -/

/-- A single decoded tail block re-encodes: from `relRepeat (Rel b64TailElem)
tails m st` with `tails.length ≤ 1`, the tail encoder `encodeB64Tail
tails.flatten` reproduces `⟨m, st⟩` exactly (functionality of `b64TailElem` pins
the bytes).  `[propext, Quot.sound]`-only. -/
theorem encodeB64Tail_of_rel (tails : List (List UInt8)) {m : Nat} (st : Bytes m)
    (hrel : relRepeat (Rel b64TailElem) tails m st) (hlen : tails.length ≤ 1) :
    encodeB64Tail tails.flatten = some ⟨m, st⟩ := by
  cases tails with
  | nil =>
      rw [relRepeat_nil] at hrel
      subst m
      have hst0 : st = (Codec.emptyBytes : Bytes 0) := by
        apply Bytes.ext
        intro i
        exact Fin.elim0 i
      subst hst0
      rfl
  | cons x txs =>
      cases txs with
      | nil =>
          -- tails = [x]: extract `Rel b64TailElem x st` (the run is a single step)
          have hrelx : Rel b64TailElem x st := by
            rw [relRepeat_cons] at hrel
            rcases hrel with ⟨m₁, hm₁, s₁, s₂, hs, hx, hr⟩
            rw [relRepeat_nil] at hr
            have hm₁m : m₁ = m := by omega
            subst hm₁m
            -- s₂ : Bytes (m - m) = Bytes 0; st = splice .. s₁ (empty), so s₁ = st
            have hs₁st : s₁ = st := by
              apply Bytes.ext
              intro i
              rw [hs]
              rw [Codec.splice_apply]
              rw [cast_fin_symm]
              · unfold Codec.concat
                simp [i.isLt]
              · omega
            rw [hs₁st] at hx
            exact hx
          -- now re-encode via functionality
          have hxlen : x.length = 1 ∨ x.length = 2 := Rel_b64TailElem_size x st hrelx
          have henc_ne : Codec.encode b64TailElem x ≠ none :=
            encode_ne_none b64TailElem x st hrelx
          cases he : Codec.encode b64TailElem x with
          | none => exact False.elim (henc_ne he)
          | some e =>
              rcases e with ⟨n₁, s₁⟩
              have hrel' : Rel b64TailElem x s₁ := encode_rel b64TailElem x he
              have hpin : (⟨n₁, s₁⟩ : Sigma fun k => Bytes k) = ⟨m, st⟩ :=
                b64TailElem_functional x s₁ st hrel' hrelx
              cases hpin
              -- encodeB64Tail x = Codec.encode b64TailElem x (x is 1 or 2 bytes)
              rcases hxlen with h1 | h2
              · -- x.length = 1: x = [a]
                rcases x with _ | ⟨a, t⟩
                · simp only [List.length_nil] at h1; omega
                · cases t with
                    | nil => simp [encodeB64Tail]; exact he
                    | cons _ _ => simp only [List.length_cons] at h1; omega
              · -- x.length = 2: x = [a, b]
                rcases x with _ | ⟨a, t⟩
                · simp only [List.length_nil] at h2; omega
                · cases t with
                    | nil => simp only [List.length_cons, List.length_nil] at h2; omega
                    | cons b t2 =>
                        cases t2 with
                        | nil => simp [encodeB64Tail]; exact he
                        | cons _ _ => simp only [List.length_cons] at h2; omega
      | cons y ys =>
          have hnle : ¬ (x :: y :: ys).length ≤ 1 := by simp
          exact False.elim (hnle hlen)

/-- The converse (`decodeFullB64 s = some v → encodeB64 v = some ⟨n, s⟩`).  A
successful decode decomposes (via `decodeFullB64_some`) into a block run
`blocks` and an at-most-one-block tail `tails`, with `v = blocks.flatten ++
tails.flatten`.  Re-encode the blocks by `encodeRepeat_of_rel` and the tail by
`encodeB64Tail_of_rel` (functionality pins the exact bytes), then reassemble
`concat s₀ t.bytes` back to `s` via the `t.prepend s₀ = s` transport.
`[propext, Quot.sound]`-only. -/
theorem decodeFullB64_conv {n : Nat} (s : Bytes n) (v : List UInt8)
    (h : decodeFullB64 s = some v) :
    encodeB64 v = some ⟨n, s⟩ := by
  rcases decodeFullB64_some s v h with ⟨blocks, t, tails, hmem, htail, hlen, hflat⟩
  rcases (decodeRepeat_spec b64BlockElem b64BlockConsumesByte blocks n s t).1 hmem with
    ⟨s₀, hs₀, hrel₀⟩
  have hblock3 : ∀ b ∈ blocks, b.length = 3 := relB64Block_all_size3 s₀ hrel₀
  -- re-encode the block run
  have henc₀ : encodeRepeat b64BlockElem blocks = some ⟨n - t.remaining, s₀⟩ :=
    encodeRepeat_of_rel b64BlockElem b64BlockElem_functional blocks s₀ hrel₀
  -- re-encode the tail
  have hmemt : (tails, Suffix.empty t.remaining) ∈ decodeRepeat b64TailElem b64TailConsumesByte t.remaining t.bytes :=
    decodeFull_some b64TailElem b64TailConsumesByte t.bytes tails htail
  rcases (decodeRepeat_spec b64TailElem b64TailConsumesByte tails t.remaining t.bytes (Suffix.empty t.remaining)).1 hmemt with
    ⟨st, hst, hrelt⟩
  -- `st : Bytes (t.remaining - (Suffix.empty t.remaining).remaining)`; that length
  -- is `t.remaining - 0 = t.remaining`, so normalise it in place
  simp only [Suffix.empty, Nat.sub_zero] at st hrelt
  have henct : encodeB64Tail tails.flatten = some ⟨t.remaining, st⟩ :=
    encodeB64Tail_of_rel tails st hrelt hlen
  -- the flattened tail is at most 2 bytes (the split-back length hypothesis)
  have htail2 : tails.flatten.length ≤ 2 := by
    cases tails with
    | nil => simp
    | cons x txs =>
        cases txs with
        | nil =>
            have hxlen : x.length = 1 ∨ x.length = 2 := by
              rw [relRepeat_cons] at hrelt
              rcases hrelt with ⟨mh, hmh, sh, srest, hsp, hxr, _⟩
              exact Rel_b64TailElem_size x sh hxr
            simpa using hxlen.elim (fun h => (h ▸ (by decide : 1 ≤ 2))) (fun h => (h ▸ (by decide : 2 ≤ 2)))
        | cons y ys =>
            have hnle : ¬ (x :: y :: ys).length ≤ 1 := by simp
            exact absurd hlen hnle
  -- split-back: `v = blocks.flatten ++ tails.flatten` splits as `(blocks, tails.flatten)`
  have hsplit : b64Split (blocks.flatten ++ tails.flatten) = (blocks, tails.flatten) :=
    b64Split_blocks_tail blocks tails.flatten hblock3 htail2
  -- `st` is `t.bytes` (read through the empty-suffix prepend)
  have hst_eq : st = t.bytes := by
    have h1 : (Suffix.empty t.remaining).prepend st = t.bytes := hst.symm
    rw [Codec.prepend_empty] at h1
    apply Bytes.ext
    intro j
    have hj := congrFun h1 j
    rw [cast_bytes_val' (e := Nat.sub_zero t.remaining)] at hj
    exact hj
  subst hst_eq
  -- expand `encodeB64 v` and rewrite the two component encodes
  rw [encodeB64, b64Split_ofBytes_ofBytes v]
  rw [← hflat]
  rw [hsplit]
  rw [encodeB64']
  rw [henc₀, henct]
  dsimp only []
  -- goal: `some ⟨(n - t.remaining) + t.remaining, concat s₀ t.bytes⟩ = some ⟨n, s⟩`
  have hlen : n - t.remaining + t.remaining = n := Nat.sub_add_cancel t.hle
  -- the reassembled bytes: `concat s₀ st = s` (transported along `hlen.symm`)
  have hbytes : Codec.concat s₀ t.bytes = cast (congrArg Bytes hlen.symm) s := by
    apply Bytes.ext
    intro j
    rw [cast_bytes_val' (e := hlen.symm)]
    unfold Codec.concat
    by_cases hj : j.val < n - t.remaining
    · simp [hj]
      -- prefix read: `s₀ ⟨j.val⟩ = s ⟨j.val⟩` via `t.prepend s₀ = s`
      have hread : s₀ ⟨j.val, hj⟩ = (t.prepend s₀) ⟨j.val, by omega⟩ :=
        (Codec.prepend_prefix_read t s₀ ⟨j.val, by omega⟩ hj).symm
      rw [hread]
      exact (congrFun hs₀ _).symm
    · -- suffix read
      have hidx : j.val - (n - t.remaining) < t.remaining := by
        have := t.hle
        omega
      -- st reads as t.bytes at the suffix index
      have hread : ∀ (hix : j.val - (n - t.remaining) < t.remaining),
          t.bytes ⟨j.val - (n - t.remaining), hix⟩ = s ⟨j.val, by omega⟩ := by
        intro hix
        have hprep : t.bytes ⟨j.val - (n - t.remaining), hix⟩ =
            (t.prepend s₀) ⟨j.val, by omega⟩ := by
          unfold Suffix.prepend
          rw [Codec.splice_apply]
          rw [cast_fin_symm]
          · simp only [Nat.not_lt.mpr (Nat.le_of_not_gt hj), Codec.concat, dite_eq_right (by decide : ¬ False)]
            rw [cast_bytes_val']
            omega
          · omega
        exact hprep.trans (congrFun hs₀ _).symm
      -- take the else branch of the (already-unfolded) `concat`
      simp only [hj]
      exact hread _
  -- conclude the `Option`/`Sigma` equality from the length and byte identities
  have hsig : (⟨n - t.remaining + t.remaining, Codec.concat s₀ t.bytes⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ :=
    Sigma.ext hlen (by
      have h1 : HEq (Codec.concat s₀ t.bytes) (cast (congrArg Bytes hlen.symm) s) :=
        heq_of_eq hbytes
      exact h1.trans (cast_heq (congrArg Bytes hlen.symm) s))
  rw [hsig]

/-! ## Injectivity (task 4.4)

`encodeB64` is injective on its value: two byte lists that encode to the same
`(length, bytes)` are equal.  This is immediate from the roundtrip
`decodeFullB64_roundtrip` (both `v` and `v'` decode from the same `s`), so
`decodeFullB64` is the left inverse and `encodeB64` a partial bijection.
`[propext, Quot.sound]`-only. -/

/-- `encodeB64` injectivity: `encodeB64 v = encodeB64 v' = some ⟨n, s⟩ → v = v'`. -/
theorem encodeB64_injective {v v' : List UInt8} {n : Nat} {s : Bytes n}
    (h : encodeB64 v = some ⟨n, s⟩) (h' : encodeB64 v' = some ⟨n, s⟩) :
    v = v' := by
  have hv : decodeFullB64 s = some v := decodeFullB64_roundtrip v h
  have hv' : decodeFullB64 s = some v' := decodeFullB64_roundtrip v' h'
  exact Option.some.inj (hv.symm.trans hv')

end BaseN.Base64
