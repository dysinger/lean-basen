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

`B64` is the canonical base64 value: full 3-byte blocks, then at most one
terminal tail of 1 or 2 bytes.  Its tail constructors are terminal (no
continuation), so "data after a pad" is unrepresentable by construction.
-/

/-- The canonical base64 value. -/
inductive B64 where
  | nil
  | full (b0 b1 b2 : UInt8) (rest : B64)
  | tail1 (b0 : UInt8)
  | tail2 (b0 b1 : UInt8)

/-- The 4-character (no pad) encoding of a full 3-byte block. -/
def b64FullChars (b0 b1 b2 : UInt8) : List UInt8 :=
  [toByte (valToB64 (b0.toNat / 4)), toByte (valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16)),
   toByte (valToB64 ((b1.toNat % 16) * 4 + b2.toNat / 64)), toByte (valToB64 (b2.toNat % 64))]

/-- The `3 chars + "="` encoding of a 2-byte tail. -/
def b64Tail2Chars (b0 b1 : UInt8) : List UInt8 :=
  [toByte (valToB64 (b0.toNat / 4)), toByte (valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16)),
   toByte (valToB64 ((b1.toNat % 16) * 4)), 61]

/-- The `2 chars + "=="` encoding of a 1-byte tail. -/
def b64Tail1Chars (b0 : UInt8) : List UInt8 :=
  [toByte (valToB64 (b0.toNat / 4)), toByte (valToB64 ((b0.toNat % 4) * 16)), 61, 61]

/-- The canonical character list of a `B64` value. -/
def b64CharsOf : B64 → List UInt8
  | B64.nil => []
  | B64.full b0 b1 b2 rest => b64FullChars b0 b1 b2 ++ b64CharsOf rest
  | B64.tail2 b0 b1 => b64Tail2Chars b0 b1
  | B64.tail1 b0 => b64Tail1Chars b0

/-- `b64FullChars` is exactly `b64BlockUnapply` on a 3-byte block. -/
theorem b64FullChars_eq_unapply (b0 b1 b2 : UInt8) :
    b64FullChars b0 b1 b2 = [toByte (valToB64 (b0.toNat / 4)), toByte (valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16)),
      toByte (valToB64 ((b1.toNat % 16) * 4 + b2.toNat / 64)), toByte (valToB64 (b2.toNat % 64))] := rfl

/-- The strict base64 encoder: a structural fold over `B64`, always canonical. -/
def encodeB64Strict : B64 → List UInt8 := b64CharsOf

/-- Strict (canonical) base64 parse: decode 4 chars via the canonical
`b64BlockApply` (which re-checks that the bytes re-encode to the input chars,
so non-canonical dropped-bit blocks are rejected), map the block's byte-list
shape to a `B64` constructor (1 byte = tail1, 2 = tail2, 3 = full/recursive),
and thread the remainder. -/
def parseB64 : List UInt8 → Option (B64 × List UInt8)
  | [] => some (B64.nil, [])
  | c0 :: c1 :: c2 :: c3 :: rest =>
      match b64BlockApply [c0, c1, c2, c3] with
      | some [b0] => some (B64.tail1 b0, rest)
      | some [b0, b1] => some (B64.tail2 b0 b1, rest)
      | some [b0, b1, b2] =>
          match parseB64 rest with
          | some (v, r) => some (B64.full b0 b1 b2 v, r)
          | none => none
      | some _ => none
      | none => none
  | _ => none

/-- The strict base64 decoder over a `List UInt8` of input bytes. -/
def decodeB64Strict (s : List UInt8) : Option B64 :=
  match parseB64 s with
  | some (v, []) => some v
  | _ => none

/-! ## Strict roundtrip and rejection (base64)

The strict decoder is total and returns `B64`; the malformed shape has no
inhabitant.  Roundtrip is an induction over `B64` using the per-shape
block-decode identities; rejection of trailing data is structural. -/

/-- Full-block parse: the canonical chars of a full block parse to it, threading
`rest`. -/
private theorem parseB64_full (b0 b1 b2 : UInt8) (rest : List UInt8) :
    parseB64 (b64FullChars b0 b1 b2 ++ rest) =
      (match parseB64 rest with | some (v, r) => some (B64.full b0 b1 b2 v, r) | none => none) := by
  simp [parseB64, b64FullChars, b64BlockApply, b64BlockUnapply, b64BlockDecodeLenient_unapply_triple]

/-- 2-byte-tail parse: the canonical chars parse to the tail, threading `rest`. -/
private theorem parseB64_tail2 (b0 b1 : UInt8) (rest : List UInt8) :
    parseB64 (b64Tail2Chars b0 b1 ++ rest) = some (B64.tail2 b0 b1, rest) := by
  simp [parseB64, b64Tail2Chars, b64BlockApply, b64BlockUnapply, b64BlockDecodeLenient_unapply_pair]

/-- 1-byte-tail parse: the canonical chars parse to the tail, threading `rest`. -/
private theorem parseB64_tail1 (b0 : UInt8) (rest : List UInt8) :
    parseB64 (b64Tail1Chars b0 ++ rest) = some (B64.tail1 b0, rest) := by
  simp [parseB64, b64Tail1Chars, b64BlockApply, b64BlockUnapply, b64BlockDecodeLenient_unapply_single]

/-- The canonical chars of a `B64` value parse back to that value with empty
remainder. -/
private theorem parseB64_charsOf (v : B64) : parseB64 (b64CharsOf v) = some (v, []) := by
  induction v with
  | nil => rfl
  | full b0 b1 b2 rest ih =>
      unfold b64CharsOf
      rw [parseB64_full b0 b1 b2 (b64CharsOf rest)]
      rw [ih]
  | tail2 b0 b1 =>
      unfold b64CharsOf
      rw [← List.append_nil (b64Tail2Chars b0 b1)]
      rw [parseB64_tail2 b0 b1 []]
  | tail1 b0 =>
      unfold b64CharsOf
      rw [← List.append_nil (b64Tail1Chars b0)]
      rw [parseB64_tail1 b0 []]

/-- Strict roundtrip: encoding then strict-decoding a `B64` value returns it. -/
theorem strict_roundtrip (v : B64) : decodeB64Strict (encodeB64Strict v) = some v := by
  unfold encodeB64Strict decodeB64Strict
  rw [parseB64_charsOf v]

/-- The run-level rejection: `Zg==AAAA` (a pad-terminated block followed by data)
is `none` — the malformed shape has no `B64` inhabitant. -/
theorem rejects_trailing :
    decodeB64Strict [0x5A, 0x67, 0x3D, 0x3D, 0x41, 0x41, 0x41, 0x41] = none := by
  unfold decodeB64Strict parseB64
  decide

/-! ## Converse (decode → encode) -/

/-- `b64BlockApply cs = some bs → b64BlockUnapply bs = some cs` — a successful
canonical block decode re-encodes to exactly the input chars (the backward half
of `b64BlockIso_law`). -/
theorem b64BlockApply_canonical (cs bs : List UInt8) :
    b64BlockApply cs = some bs → b64BlockUnapply bs = some cs :=
  (b64BlockIso_law cs bs).1

/-- Parse completeness: a successful `parseB64 s = some (v, r)` means `s` is the
canonical chars of `v` followed by `r`.  Proved by structural recursion on `s`:
the recursive full-block branch recurses on `rest`, which is four elements
deeper, hence a strict subterm. -/
private theorem parseB64_inv : (s : List UInt8) → (v : B64) → (r : List UInt8) →
    parseB64 s = some (v, r) → b64CharsOf v ++ r = s
  | [], v, r, h => by
      simp [parseB64] at h
      rcases h with ⟨hv, hr⟩
      subst v; subst r; rfl
  | [_], _, _, h => by simp [parseB64] at h
  | [_, _], _, _, h => by simp [parseB64] at h
  | [_, _, _], _, _, h => by simp [parseB64] at h
  | c0 :: c1 :: c2 :: c3 :: rest, v, r, h => by
      unfold parseB64 at h
      cases hb : b64BlockApply [c0, c1, c2, c3] with
      | none => simp [hb] at h
      | some bs =>
          cases bs with
          | nil => simp [hb] at h
          | cons b0 t =>
            cases t with
            | nil =>
                -- single-byte tail: bs = [b0]
                simp [hb] at h
                rcases h with ⟨hv, hr⟩
                subst v; subst r
                have hun : b64BlockUnapply [b0] = some [c0, c1, c2, c3] :=
                  b64BlockApply_canonical [c0, c1, c2, c3] [b0] hb
                have hc : b64Tail1Chars b0 = [c0, c1, c2, c3] := by
                  simpa [b64BlockUnapply, b64Tail1Chars] using hun
                unfold b64CharsOf
                rw [hc]
                rfl
            | cons b1 t =>
              cases t with
              | nil =>
                  -- two-byte tail: bs = [b0, b1]
                  simp [hb] at h
                  rcases h with ⟨hv, hr⟩
                  subst v; subst r
                  have hun : b64BlockUnapply [b0, b1] = some [c0, c1, c2, c3] :=
                    b64BlockApply_canonical [c0, c1, c2, c3] [b0, b1] hb
                  have hc : b64Tail2Chars b0 b1 = [c0, c1, c2, c3] := by
                    simpa [b64BlockUnapply, b64Tail2Chars] using hun
                  unfold b64CharsOf
                  rw [hc]
                  rfl
              | cons b2 t =>
                cases t with
                | nil =>
                    -- full block: bs = [b0, b1, b2], recurse on rest
                    simp [hb] at h
                    cases hrest : parseB64 rest with
                    | none => simp [hrest] at h
                    | some pr' =>
                        rcases pr' with ⟨v', r'⟩
                        simp [hrest] at h
                        rcases h with ⟨hv, hr⟩
                        subst v; subst r
                        have hun : b64BlockUnapply [b0, b1, b2] = some [c0, c1, c2, c3] :=
                          b64BlockApply_canonical [c0, c1, c2, c3] [b0, b1, b2] hb
                        have hc : b64FullChars b0 b1 b2 = [c0, c1, c2, c3] := by
                          simpa [b64BlockUnapply, b64FullChars] using hun
                        have ih : b64CharsOf v' ++ r' = rest :=
                          parseB64_inv rest v' r' hrest
                        unfold b64CharsOf
                        rw [hc]
                        rw [List.append_assoc]
                        rw [ih]
                        rfl
                | cons _ _ => simp [hb] at h

/-- Converse: a successful strict decode re-encodes to exactly the input bytes. -/
theorem decodeB64Strict_inverse (s : List UInt8) (v : B64) :
    decodeB64Strict s = some v → encodeB64Strict v = s := by
  intro h
  unfold decodeB64Strict at h
  cases hp : parseB64 s with
  | none => simp [hp] at h
  | some pr =>
      rcases pr with ⟨v', r⟩
      cases r with
      | nil =>
          have hvr : v' = v := by simpa [hp] using h
          have hcomp := parseB64_inv s v' [] (by simpa using hp)
          unfold encodeB64Strict
          rw [← hvr]
          simpa using hcomp
      | cons _ _ => simp [hp] at h

/-! ## Conformance: canonical encoding, converse, injectivity (base64) -/

/-- A `valToB64` character embedding (`toByte ·`) is a valid base64 alphabet byte. -/
theorem b64CharAlphabet (i : Nat) (hi : i ≤ 63) : b64Valid (toByte (valToB64 i)).toNat = true := by
  rw [toByte_valToB64 i hi]
  exact valToB64_valid i hi

/-- Canonical encoding: every byte of `encodeB64Strict v` is an alphabet character
or the `=` pad, and pad bytes are exactly the terminal tail's RFC arity. The
first conjunct is the alphabet-or-pad form; the `=` byte (61) appears only from
the explicit tail pads (never from `valToB64`, cf. `valToB64_not_pad`). -/
theorem encodeB64Strict_alphabetOrPad (v : B64) :
    ∀ b ∈ encodeB64Strict v, b64Valid b.toNat = true ∨ b.toNat = 61 := by
  induction v with
  | nil => intro b hb; simp [encodeB64Strict, b64CharsOf] at hb
  | full b0 b1 b2 rest ih =>
      have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
      have hb1 : b1.toNat < 256 := UInt8.toNat_lt b1
      have hb2 : b2.toNat < 256 := UInt8.toNat_lt b2
      intro b hb
      rw [encodeB64Strict, b64CharsOf] at hb
      rw [List.mem_append] at hb
      rcases hb with hb | hb
      · rw [b64FullChars] at hb
        simp at hb
        rcases hb with rfl | rfl | rfl | rfl
        · left; exact b64CharAlphabet (b0.toNat / 4) (by omega)
        · left; exact b64CharAlphabet ((b0.toNat % 4) * 16 + b1.toNat / 16) (by omega)
        · left; exact b64CharAlphabet ((b1.toNat % 16) * 4 + b2.toNat / 64) (by omega)
        · left; exact b64CharAlphabet (b2.toNat % 64) (by omega)
      · exact ih b hb
  | tail2 b0 b1 =>
      have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
      have hb1 : b1.toNat < 256 := UInt8.toNat_lt b1
      intro b hb
      rw [encodeB64Strict, b64CharsOf] at hb
      rw [b64Tail2Chars] at hb
      simp at hb
      rcases hb with rfl | rfl | rfl | rfl
      · left; exact b64CharAlphabet (b0.toNat / 4) (by omega)
      · left; exact b64CharAlphabet ((b0.toNat % 4) * 16 + b1.toNat / 16) (by omega)
      · left; exact b64CharAlphabet ((b1.toNat % 16) * 4) (by omega)
      · right; rfl
  | tail1 b0 =>
      have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
      intro b hb
      rw [encodeB64Strict, b64CharsOf] at hb
      rw [b64Tail1Chars] at hb
      simp at hb
      rcases hb with rfl | rfl | rfl
      · left; exact b64CharAlphabet (b0.toNat / 4) (by omega)
      · left; exact b64CharAlphabet ((b0.toNat % 4) * 16) (by omega)
      · right; rfl

/-- Encoding is injective on `B64`: equal encodings identify equal values. -/
theorem encodeB64Strict_injective {v v' : B64} :
    encodeB64Strict v = encodeB64Strict v' → v = v' := by
  intro h
  have h1 := strict_roundtrip v
  have h2 := strict_roundtrip v'
  rw [h] at h1
  have h12 : some v = some v' := h1.symm.trans h2
  exact Option.some.inj h12

/-! ## The uniform `List UInt8` transport (facade value type)

The base64 *value* is `B64` (terminal-tail, so illegal "data after `=`" is
unrepresentable); the facade exposes the uniform `List UInt8` value type via
this bijective byte flatten. -/

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

/-- The uniform `List UInt8 → Option (List UInt8)` decoder: strict-decode to
`B64`, then flatten to the byte list. -/
def decodeBytes (s : List UInt8) : Option (List UInt8) :=
  (decodeB64Strict s).map b64BytesOf

/-- The uniform `List UInt8 → List UInt8` encoder: split bytes to `B64`,
then encode canonically.  Total (every byte list is a `B64`). -/
def encodeBytes (bs : List UInt8) : List UInt8 :=
  encodeB64Strict (b64OfBytes bs)

/-- The uniform roundtrip: `decodeBytes (encodeBytes bs) = some bs`. -/
theorem roundtripBytes (bs : List UInt8) : decodeBytes (encodeBytes bs) = some bs := by
  unfold decodeBytes encodeBytes
  rw [strict_roundtrip (b64OfBytes bs)]
  simp [b64BytesOf_ofBytes bs]

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

/-- The whole-input base64 decoder over a length-indexed byte string. -/
def decodeFullB64 {n : Nat} (s : Bytes n) : Option (List UInt8) :=
  List.head? ((decodeRepeat b64BlockElem b64BlockConsumesByte n s).filterMap fun ⟨blocks, t⟩ =>
    match decodeFull b64TailElem b64TailConsumesByte t.remaining t.bytes with
    | some tail => some (blocks.flatten ++ tail.flatten)
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

end BaseN.Base64
