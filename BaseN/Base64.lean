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

/-! ## The strict value type and the run triple

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

/-- Strict (canonical) base64 parse: decode 4 chars via the already-proved
`b64BlockDecodeLenient`, map the block's byte-list shape to a `B64` constructor
(1 byte = tail1, 2 = tail2, 3 = full/recursive), and thread the remainder. -/
def parseB64 : List UInt8 → Option (B64 × List UInt8)
  | [] => some (B64.nil, [])
  | c0 :: c1 :: c2 :: c3 :: rest =>
      match b64BlockDecodeLenient [c0, c1, c2, c3] with
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
  simp [parseB64, b64FullChars, b64BlockDecodeLenient_unapply_triple]

/-- 2-byte-tail parse: the canonical chars parse to the tail, threading `rest`. -/
private theorem parseB64_tail2 (b0 b1 : UInt8) (rest : List UInt8) :
    parseB64 (b64Tail2Chars b0 b1 ++ rest) = some (B64.tail2 b0 b1, rest) := by
  simp [parseB64, b64Tail2Chars, b64BlockDecodeLenient_unapply_pair]

/-- 1-byte-tail parse: the canonical chars parse to the tail, threading `rest`. -/
private theorem parseB64_tail1 (b0 : UInt8) (rest : List UInt8) :
    parseB64 (b64Tail1Chars b0 ++ rest) = some (B64.tail1 b0, rest) := by
  simp [parseB64, b64Tail1Chars, b64BlockDecodeLenient_unapply_single]

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

end BaseN.Base64
