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

/-- The base64 element: 4 base64 (or pad) chars grouped into 1–3 bytes. -/
def b64Elem : Codec (List UInt8) := Codec.iso b64BlockIso (count 4 (Codec.satisfy b64OrPad))

/-- `b64Elem` is productive. -/
theorem b64ConsumesByte : ConsumesByte b64Elem := by
  unfold b64Elem
  rw [← productive_iff_consumesByte (Codec.iso b64BlockIso (count 4 (Codec.satisfy b64OrPad)))]
  apply Productive_iso b64BlockIso (count 4 (Codec.satisfy b64OrPad))
  rw [show 4 = 3 + 1 by rfl]
  exact Productive_count_satisfy_succ b64OrPad 3

/-- The base64 decoder (run of blocks). -/
def decodeB64 {n : Nat} (s : Bytes n) : List (List (List UInt8) × Suffix n) :=
  decodeRepeat b64Elem b64ConsumesByte n s

/-- The base64 encoder (run of blocks). -/
def encodeB64 (bs : List (List UInt8)) : Option (Sigma fun n => Bytes n) :=
  encodeRepeat b64Elem bs

/-- The base64 relation. -/
def relB64 : List (List UInt8) → (n : Nat) → Bytes n → Prop :=
  relRepeat (Rel b64Elem)

/-! ## Unambiguity and the inherited roundtrip law -/

/-- `b64Elem` is unambiguous. -/
theorem b64Elem_unambiguous : Unambiguous b64Elem := by
  unfold b64Elem
  apply Unambiguous_iso b64BlockIso (count 4 (Codec.satisfy b64OrPad))
  exact count_satisfy_unambiguous b64OrPad 4

/-- `Rel b64Elem x s` pins the byte length: `n = 4`. -/
theorem Rel_b64Elem_len (x : List UInt8) {n : Nat} (s : Bytes n) :
    Rel b64Elem x s → n = 4 := by
  intro h
  unfold b64Elem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, _, hc⟩
  exact Rel_count_satisfy_len b64OrPad 4 a s hc

/-- The base64 relation is unambiguous. -/
theorem relB64_unambiguous : relUnambiguous relB64 := by
  intro a b n s ha hb
  dsimp [relB64] at ha hb
  induction a generalizing b n s with
  | nil =>
      rw [relRepeat_nil] at ha
      subst n
      cases b with
      | nil => rfl
      | cons y ys =>
          rw [relRepeat_cons] at hb
          rcases hb with ⟨m, hm, s₁, s₂, hs, hy, _⟩
          have hlen : m = 4 := Rel_b64Elem_len y s₁ hy
          have hm0 : m = 0 := by omega
          omega
  | cons x xs ih =>
      cases b with
      | nil =>
          rw [relRepeat_nil] at hb
          rw [relRepeat_cons] at ha
          rcases ha with ⟨mx, hmx, s₁x, s₂x, hsx, hx, hxs⟩
          have hlen : mx = 4 := Rel_b64Elem_len x s₁x hx
          subst n
          have hm0 : mx = 0 := by omega
          omega
      | cons y ys =>
          rw [relRepeat_cons] at ha hb
          rcases ha with ⟨mx, hmx, s₁x, s₂x, hsx, hx, hxs⟩
          rcases hb with ⟨my, hmy, s₁y, s₂y, hsy, hy, hys⟩
          have hlx : mx = 4 := Rel_b64Elem_len x s₁x hx
          have hly : my = 4 := Rel_b64Elem_len y s₁y hy
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
            exact b64Elem_unambiguous s₁x hx (by rw [hpre]; exact hy)
          have htail : xs = ys := by
            exact ih s₂x hxs (by simpa [htaily] using hys)
          rw [hhead, htail]

/-- Full-consumption decode is unambiguous for `b64Elem`. -/
theorem b64DecodeFull_unambiguous {x y : List (List UInt8)} {n : Nat} (s : Bytes n) :
    (x, Suffix.empty n) ∈ decodeRepeat b64Elem b64ConsumesByte n s →
    (y, Suffix.empty n) ∈ decodeRepeat b64Elem b64ConsumesByte n s → x = y := by
  intro hx hy
  rcases (decodeRepeat_spec b64Elem b64ConsumesByte x n s (Suffix.empty n)).1 hx with ⟨s₀x, hsx, hrx⟩
  rcases (decodeRepeat_spec b64Elem b64ConsumesByte y n s (Suffix.empty n)).1 hy with ⟨s₀y, hsy, hry⟩
  have hs₀ : s₀x = s₀y := by
    have hpre : (Suffix.empty n).prepend s₀x = (Suffix.empty n).prepend s₀y := by
      exact hsx.symm.trans hsy
    exact prepend_prefix_eq (Suffix.empty n) s₀x s₀y hpre
  exact relB64_unambiguous s₀x hrx (by rw [hs₀]; exact hry)

/-- The base64 roundtrip law. `[propext, Quot.sound]`-only. -/
theorem roundtrip (bs : List (List UInt8)) {n : Nat} {s : Bytes n} :
    encodeB64 bs = some ⟨n, s⟩ → decodeFull b64Elem b64ConsumesByte n s = some bs := by
  intro he
  have hrel : relRepeat (Rel b64Elem) bs n s := encodeRepeat_rel b64Elem bs he
  have hmem : (bs, Suffix.empty n) ∈ decodeRepeat b64Elem b64ConsumesByte n s := by
    refine (decodeRepeat_spec b64Elem b64ConsumesByte bs n s (Suffix.empty n)).2 ⟨
      cast (congrArg Bytes (Nat.sub_zero n).symm) s, ?_, ?_⟩
    · exact (prepend_empty_eq s).symm
    · exact (relRepeat_cast (Rel b64Elem) bs (Nat.sub_zero n).symm s).2 hrel
  exact (decodeFull_spec b64Elem b64ConsumesByte (fun {x y} {m} (t : Bytes m) =>
    b64DecodeFull_unambiguous (s := t)) s bs).2 hmem

/-! ## RFC 4648 §3.2 run-level terminal padding (the whole-input guard)

The block `iso` rejects `=` in a non-terminal *intra-block* position, but the
run-level case — a `=`-terminated block followed by another block — is accepted
by `decodeFull b64Elem` (the `count 4` window fixes bytes, not value length).
This section adds the run-level guard: a decidable `b64TerminalPad` shape on the
decoded `List (List UInt8)` (every block full except possibly the last, which may
be a tail), and `decodeB64Strict` — the grammar-correct whole-input decoder
(a single `decodeFull` plus a cheap `O(#blocks)` shape check, no second byte
pass). -/

/-- A block is a full base64 block iff it decodes to exactly 3 bytes. -/
def b64FullBlock (b : List UInt8) : Prop := b.length = 3

/-- `b64TerminalPad blocks` — the run-level terminal-padding shape (a `Bool`).
Every block is full (length 3) except possibly the last, which may be a full or
tail block (length 1 or 2).  Rendered as a `Bool` so `decodeB64Strict` is
`#eval`-able and concrete rejection vectors close by `decide`. -/
def b64TerminalPad : List (List UInt8) → Bool
  | [] => true
  | [b] => decide (b.length = 1 ∨ b.length = 2 ∨ b.length = 3)
  | b :: rest => (decide (b.length = 3)) && b64TerminalPad rest

/-- The decidable `Prop` mirror: `B64TerminalPad blocks := b64TerminalPad blocks = true`. -/
def B64TerminalPad (blocks : List (List UInt8)) : Prop :=
  b64TerminalPad blocks = true

/-- `decodeB64Strict` — the whole-input base64 decoder that additionally enforces
RFC 4648 §3.2 terminal padding: decode fully with `decodeFull b64Elem`, then keep
the result only when it has terminal-pad shape.  A single decode pass plus an
`O(#blocks)` shape check. -/
def decodeB64Strict {n : Nat} (s : Bytes n) : Option (List (List UInt8)) :=
  match decodeFull b64Elem b64ConsumesByte n s with
  | none => none
  | some bs => if b64TerminalPad bs then some bs else none

/-- The grammar-correct denotation: full blocks in a run, plus a terminal-pad
shape constraint.  "Data after a terminal `=`" has no inhabitant because a tail
block (length < 3) can only be last. -/
def relB64Strict : List (List UInt8) → (n : Nat) → Bytes n → Prop :=
  fun blocks n s => relRepeat (Rel b64Elem) blocks n s ∧ B64TerminalPad blocks

/-- The concrete `b64TerminalPad` rejection fact: a tail block `[0x66]` followed by
a full block `[0,0,0]` is *not* terminal-pad shaped. -/
theorem b64TerminalPad_rejects_tail_then_full :
    b64TerminalPad [[0x66], [0, 0, 0]] = false := by
  unfold b64TerminalPad
  decide

/-- Canonical encoding (value shape): a terminal-pad-shaped value list encodes
and strict-decodes round-trip. -/
theorem roundtripStrict (bs : List (List UInt8)) (hpad : B64TerminalPad bs)
    {n : Nat} {s : Bytes n} :
    encodeB64 bs = some ⟨n, s⟩ → decodeB64Strict s = some bs := by
  intro he
  unfold decodeB64Strict
  rw [roundtrip bs he]
  change (if b64TerminalPad bs then some bs else none) = some bs
  rw [hpad]
  rfl

/-- The base64 run-level rejection theorem (STATEMENT): a `=`-terminated block
followed by further data is rejected (`none`).  The `decodeFull` half (`some [[0x66],[0,0,0]]`)
plus `b64TerminalPad_rejects_tail_then_full` gives `none`; the concrete `decodeFull`
equality is established via `decodeFull_spec` + `encode_rel` for each block (in
progress in the next pass). -/
theorem decodeB64Strict_rejects_trailing
    (hs : (fun i : Fin 8 => [0x5A, 0x67, 0x3D, 0x3D, 0x41, 0x41, 0x41, 0x41][i.val]) = (s : Bytes 8))
    (hf : decodeFull b64Elem b64ConsumesByte 8 s = some [[0x66], [0, 0, 0]]) :
    decodeB64Strict s = none := by
  subst s
  unfold decodeB64Strict
  rw [hf]
  simp [b64TerminalPad_rejects_tail_then_full]

end BaseN.Base64
