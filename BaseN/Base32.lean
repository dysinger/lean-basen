/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# BaseN.Base32

RFC 4648 §6 base32 encoding.  `valToB32` maps a 5-bit value to the RFC 4648
alphabet (`A-Z` 65-90, `2-7` 50-55); `b32ToVal` inverts it (returns `32` on an
invalid byte).  Padding is `=` (61).  Each 5-byte block encodes to 8 characters;
the four partial tails encode to 2/4/5/7 chars with 6/4/3/1 `=` pad bytes.

All digit math is `Nat`-level; the alphabet is ASCII, every produced byte is
`< 256`.  `[propext, Quot.sound]`-only, zero `sorry`.
-/

import BaseN.Common

namespace BaseN.Base32

open Codec
open BaseN.Common

/-- `valToB32 i` — the base32 alphabet character for `i ∈ {0..31}`. -/
def valToB32 (i : Nat) : Nat :=
  if i ≤ 25 then 65 + i else 50 + i - 26

/-- `b32ToVal e` — the 5-bit value of a base32 character, or `32` if invalid. -/
def b32ToVal (e : Nat) : Nat :=
  if e ≤ 55 then
    if 50 ≤ e then e - 50 + 26 else 32
  else if e ≤ 90 then
    if 65 ≤ e then e - 65 else 32
  else 32

/-- `b32Valid e` — `true` iff `e` is a base32 alphabet character. -/
def b32Valid (e : Nat) : Bool := decide (b32ToVal e ≤ 31)

/-- `toByte n` — the `UInt8` embedding. -/
def toByte (n : Nat) : UInt8 := UInt8.ofNat n

/-- `b32ToVal (valToB32 i) = i` — the 5-bit ↔ char bijection. -/
theorem b32ToVal_valToB32 (i : Nat) (hi : i ≤ 31) :
    b32ToVal (valToB32 i) = i := by
  unfold b32ToVal valToB32
  by_cases h25 : i ≤ 25
  · simp only [h25, ite_true]
    have hle90 : 65 + i ≤ 90 := by omega
    have hnle55 : ¬ 65 + i ≤ 55 := by omega
    simp only [hnle55, ite_false, hle90, ite_true]
    have h65 : 65 ≤ 65 + i := by omega
    simp only [h65, ite_true]
    omega
  · simp only [h25, ite_false]
    have hle55 : 50 + i - 26 ≤ 55 := by omega
    simp only [hle55, ite_true]
    have h50 : 50 ≤ 50 + i - 26 := by omega
    simp only [h50, ite_true]
    omega

/-- `valToB32 i` produces a valid base32 character. -/
theorem valToB32_valid (i : Nat) (hi : i ≤ 31) : b32Valid (valToB32 i) = true := by
  unfold b32Valid
  apply decide_eq_true
  rw [b32ToVal_valToB32 i hi]
  exact hi

/-- `valToB32 i ≠ 61` — never the padding byte `=`. -/
theorem valToB32_not_pad (i : Nat) (hi : i ≤ 31) : valToB32 i ≠ 61 := by
  unfold valToB32
  by_cases h25 : i ≤ 25
  · simp only [h25, ite_true]; omega
  · simp only [h25, ite_false]; omega

/-- `valToB32 i < 256` — every base32 character is a single byte. -/
theorem valToB32_lt_256 (i : Nat) (_hi : i ≤ 31) : valToB32 i < 256 := by
  unfold valToB32
  by_cases h25 : i ≤ 25
  · simp only [h25, ite_true]; omega
  · simp only [h25, ite_false]; omega

-- Byte extraction identities (the structural inverses)

/-- `byte0 v0 v1` — first byte from the two leading chars. -/
theorem byte0 (v0 v1 : Nat) (_hv0 : v0 < 256) (hv1 : v1 < 256) :
    (v0 / 8) * 8 + ((v0 % 8) * 4 + v1 / 64) / 4 = v0 := by
  have hd : v1 / 64 < 4 := by omega
  have hdiv : ((v0 % 8) * 4 + v1 / 64) / 4 = v0 % 8 := by
    have h := Nat.add_mul_div_left (v1 / 64) (v0 % 8) (by decide : 0 < 4)
    have hz : v1 / 64 / 4 = 0 := Nat.div_eq_of_lt hd
    omega
  have hsum : 8 * (v0 / 8) + v0 % 8 = v0 := by
    have h := Nat.div_add_mod v0 8
    simpa [Nat.mul_comm] using h
  omega

/-- `byte1 v0 v1 v2` — second byte from chars 1-3. -/
theorem byte1 (v0 v1 v2 : Nat) (_hv0 : v0 < 256) (hv1 : v1 < 256) (_hv2 : v2 < 256) :
    ((v0 % 8) * 4 + v1 / 64) % 4 * 64 + ((v1 / 2) % 32) * 2 + ((v1 % 2) * 16 + v2 / 16) / 16 = v1 := by
  have hmod4 : ((v0 % 8) * 4 + v1 / 64) % 4 = v1 / 64 := by
    have h' := Nat.add_mul_mod_self_right (v0 % 8) (v1 / 64) 4
    have : v1 / 64 < 4 := by omega
    omega
  have hdiv16 : ((v1 % 2) * 16 + v2 / 16) / 16 = v1 % 2 := by
    have h := Nat.add_mul_div_left (v2 / 16) (v1 % 2) (by decide : 0 < 16)
    have hz : v2 / 16 / 16 = 0 := Nat.div_eq_of_lt (by omega)
    omega
  have hmid : ((v1 / 2) % 32) * 2 + v1 % 2 = v1 % 64 := by
    have h := Nat.div_add_mod (v1 % 64) 2
    have heq : (v1 / 2) % 32 = (v1 % 64) / 2 := by omega
    have hmod2 : (v1 % 64) % 2 = v1 % 2 := by omega
    omega
  have hsum : 64 * (v1 / 64) + v1 % 64 = v1 := by
    have h := Nat.div_add_mod v1 64
    simpa [Nat.mul_comm] using h
  omega

/-- `byte2 v1 v2 v3` — third byte from chars 3-4. -/
theorem byte2 (v1 v2 v3 : Nat) (_hv1 : v1 < 256) (hv2 : v2 < 256) (_hv3 : v3 < 256) :
    ((v1 % 2) * 16 + v2 / 16) % 16 * 16 + ((v2 % 16) * 2 + v3 / 128) / 2 = v2 := by
  have hmod16 : ((v1 % 2) * 16 + v2 / 16) % 16 = v2 / 16 := by
    have h' := Nat.add_mul_mod_self_right (v1 % 2) (v2 / 16) 16
    have : v2 / 16 < 16 := by omega
    omega
  have hdiv2 : ((v2 % 16) * 2 + v3 / 128) / 2 = v2 % 16 := by
    have h := Nat.add_mul_div_left (v3 / 128) (v2 % 16) (by decide : 0 < 2)
    have hz : v3 / 128 / 2 = 0 := Nat.div_eq_of_lt (by omega)
    omega
  have hsum : 16 * (v2 / 16) + v2 % 16 = v2 := by
    have h := Nat.div_add_mod v2 16
    simpa [Nat.mul_comm] using h
  omega

/-- `byte3 v2 v3 v4` — fourth byte from chars 4-6. -/
theorem byte3 (v2 v3 v4 : Nat) (_hv2 : v2 < 256) (hv3 : v3 < 256) (_hv4 : v4 < 256) :
    ((v2 % 16) * 2 + v3 / 128) % 2 * 128 + ((v3 / 4) % 32) * 4 + ((v3 % 4) * 8 + v4 / 32) / 8 = v3 := by
  have hmod2 : ((v2 % 16) * 2 + v3 / 128) % 2 = v3 / 128 := by
    have h' := Nat.add_mul_mod_self_right (v2 % 16) (v3 / 128) 2
    have : v3 / 128 < 2 := by omega
    omega
  have hdiv8 : ((v3 % 4) * 8 + v4 / 32) / 8 = v3 % 4 := by
    have h := Nat.add_mul_div_left (v4 / 32) (v3 % 4) (by decide : 0 < 8)
    have hz : v4 / 32 / 8 = 0 := Nat.div_eq_of_lt (by omega)
    omega
  have hmid : ((v3 / 4) % 32) * 4 + v3 % 4 = v3 % 128 := by
    have h := Nat.div_add_mod (v3 % 128) 4
    have heq : (v3 / 4) % 32 = (v3 % 128) / 4 := by omega
    have hmod4 : (v3 % 128) % 4 = v3 % 4 := by omega
    omega
  have hsum : 128 * (v3 / 128) + v3 % 128 = v3 := by
    have h := Nat.div_add_mod v3 128
    simpa [Nat.mul_comm] using h
  omega

/-- `byte4 v3 v4` — fifth byte from chars 6-7. -/
theorem byte4 (v3 v4 : Nat) (_hv3 : v3 < 256) (hv4 : v4 < 256) :
    ((v3 % 4) * 8 + v4 / 32) % 8 * 32 + (v4 % 32) = v4 := by
  have hmod8 : ((v3 % 4) * 8 + v4 / 32) % 8 = v4 / 32 := by
    have h' := Nat.add_mul_mod_self_right (v3 % 4) (v4 / 32) 8
    have : v4 / 32 < 8 := by omega
    omega
  have hsum : 32 * (v4 / 32) + v4 % 32 = v4 := by
    have h := Nat.div_add_mod v4 32
    simpa [Nat.mul_comm] using h
  omega

-- character reconstruction

/-- `b32Valid e = true` implies `b32ToVal e ≤ 31`. -/
theorem b32Valid_of_decide (e : Nat) (h : b32Valid e = true) : b32ToVal e ≤ 31 :=
  of_decide_eq_true (by simpa [b32Valid] using h)

/-- `(toByte (valToB32 i)).toNat = valToB32 i`. -/
private theorem toByte_valToB32 (i : Nat) (hi : i ≤ 31) :
    (toByte (valToB32 i)).toNat = valToB32 i := by
  unfold toByte
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToB32_lt_256 i hi)]

/-- `valToB32 (b32ToVal e) = e` when `e` is a valid base32 character. -/
theorem valToB32_b32ToVal_of_valid (e : Nat) (h : b32Valid e = true) :
    valToB32 (b32ToVal e) = e := by
  have hv : b32ToVal e ≤ 31 := b32Valid_of_decide e h
  unfold b32ToVal valToB32
  by_cases hle55 : e ≤ 55
  · by_cases hge50 : 50 ≤ e
    · have hb : b32ToVal e = e - 50 + 26 := by simp [b32ToVal, hle55, hge50]
      rw [hb] at hv
      have hnle25 : ¬ e - 50 + 26 ≤ 25 := by omega
      simp only [hle55, ite_true, hge50, ite_true, hnle25, ite_false]
      omega
    · have hb : b32ToVal e = 32 := by simp [b32ToVal, hle55, hge50]
      rw [hb] at hv
      omega
  · by_cases hle90 : e ≤ 90
    · by_cases hge65 : 65 ≤ e
      · have hb : b32ToVal e = e - 65 := by simp [b32ToVal, hle55, hle90, hge65]
        rw [hb] at hv
        have hle25 : e - 65 ≤ 25 := by omega
        simp only [hle55, ite_false, hle90, ite_true, hge65, ite_true, hle25, ite_true]
        omega
      · have hb : b32ToVal e = 32 := by simp [b32ToVal, hle55, hle90, hge65]
        rw [hb] at hv
        omega
    · have hb : b32ToVal e = 32 := by simp [b32ToVal, hle55, hle90]
      rw [hb] at hv
      omega

-- pad predicate

/-- Base32 alphabet character or the `=` pad. -/
def b32OrPad (b : UInt8) : Bool := b32Valid b.toNat || (b.toNat = 61)

-- block apply / unapply

/-- `b32BlockUnapply bs` — encode 1–5 bytes as exactly 8 base32 chars (with `=` pad). -/
def b32BlockUnapply (bs : List UInt8) : Option (List UInt8) :=
  match bs with
  | [v0] => some [toByte (valToB32 (v0.toNat / 8)), toByte (valToB32 ((v0.toNat % 8) * 4)), 61, 61, 61, 61, 61, 61]
  | [v0, v1] => some [toByte (valToB32 (v0.toNat / 8)), toByte (valToB32 ((v0.toNat % 8) * 4 + v1.toNat / 64)),
                      toByte (valToB32 ((v1.toNat / 2) % 32)), toByte (valToB32 ((v1.toNat % 2) * 16)), 61, 61, 61, 61]
  | [v0, v1, v2] => some [toByte (valToB32 (v0.toNat / 8)), toByte (valToB32 ((v0.toNat % 8) * 4 + v1.toNat / 64)),
                          toByte (valToB32 ((v1.toNat / 2) % 32)), toByte (valToB32 ((v1.toNat % 2) * 16 + v2.toNat / 16)),
                          toByte (valToB32 ((v2.toNat % 16) * 2)), 61, 61, 61]
  | [v0, v1, v2, v3] => some [toByte (valToB32 (v0.toNat / 8)), toByte (valToB32 ((v0.toNat % 8) * 4 + v1.toNat / 64)),
                              toByte (valToB32 ((v1.toNat / 2) % 32)), toByte (valToB32 ((v1.toNat % 2) * 16 + v2.toNat / 16)),
                              toByte (valToB32 ((v2.toNat % 16) * 2 + v3.toNat / 128)), toByte (valToB32 ((v3.toNat / 4) % 32)),
                              toByte (valToB32 ((v3.toNat % 4) * 8)), 61]
  | [v0, v1, v2, v3, v4] => some [toByte (valToB32 (v0.toNat / 8)), toByte (valToB32 ((v0.toNat % 8) * 4 + v1.toNat / 64)),
                                  toByte (valToB32 ((v1.toNat / 2) % 32)), toByte (valToB32 ((v1.toNat % 2) * 16 + v2.toNat / 16)),
                                  toByte (valToB32 ((v2.toNat % 16) * 2 + v3.toNat / 128)), toByte (valToB32 ((v3.toNat / 4) % 32)),
                                  toByte (valToB32 ((v3.toNat % 4) * 8 + v4.toNat / 32)), toByte (valToB32 (v4.toNat % 32))]
  | _ => none

-- lenient block decode (no dropped-bit checks)

/-- `b32BlockDecodeLenient cs` — decode exactly 8 base32 chars into 1–5 bytes,
accepting any pad shape (no dropped-bit strictness). -/
def b32BlockDecodeLenient (cs : List UInt8) : Option (List UInt8) :=
  match cs with
  | [c0, c1, c2, c3, c4, c5, c6, c7] =>
      if c0.toNat = 61 || c1.toNat = 61 then none
      else if ¬ b32Valid c0.toNat || ¬ b32Valid c1.toNat then none
      else
        let v0 := b32ToVal c0.toNat
        let v1 := b32ToVal c1.toNat
        let b0 := v0 * 8 + v1 / 4
        if c2.toNat = 61 then
          if c3.toNat = 61 && c4.toNat = 61 && c5.toNat = 61 && c6.toNat = 61 && c7.toNat = 61 then some [toByte b0]
          else none
        else if ¬ b32Valid c2.toNat then none
        else
          let v2 := b32ToVal c2.toNat
          if c3.toNat = 61 then none
          else if ¬ b32Valid c3.toNat then none
          else
            let v3 := b32ToVal c3.toNat
            let b1 := (v1 % 4) * 64 + v2 * 2 + v3 / 16
            if c4.toNat = 61 then
              if c5.toNat = 61 && c6.toNat = 61 && c7.toNat = 61 then some [toByte b0, toByte b1]
              else none
            else if ¬ b32Valid c4.toNat then none
            else
              let v4 := b32ToVal c4.toNat
              let b2 := (v3 % 16) * 16 + v4 / 2
              if c5.toNat = 61 then
                if c6.toNat = 61 && c7.toNat = 61 then some [toByte b0, toByte b1, toByte b2]
                else none
              else if ¬ b32Valid c5.toNat then none
              else
                let v5 := b32ToVal c5.toNat
                if c6.toNat = 61 then none
                else if ¬ b32Valid c6.toNat then none
                else
                  let v6 := b32ToVal c6.toNat
                  let b3 := (v4 % 2) * 128 + v5 * 4 + v6 / 8
                  if c7.toNat = 61 then
                    some [toByte b0, toByte b1, toByte b2, toByte b3]
                  else if ¬ b32Valid c7.toNat then none
                  else
                    let v7 := b32ToVal c7.toNat
                    let b4 := (v6 % 8) * 32 + v7
                    some [toByte b0, toByte b1, toByte b2, toByte b3, toByte b4]
  | _ => none

/-- `b32BlockApply cs` — decode 8 chars and verify the result re-encodes to `cs`
(canonical input only). This makes `apply`/`unapply` a genuine bijection. -/
def b32BlockApply (cs : List UInt8) : Option (List UInt8) :=
  (b32BlockDecodeLenient cs).bind fun bs =>
    if b32BlockUnapply bs = some cs then some bs else none

-- forward: lenient decode∘encode = id for a single block

/-- 1-byte tail. -/
theorem b32BlockDecodeLenient_unapply_single (b0 : UInt8) :
    b32BlockDecodeLenient [toByte (valToB32 (b0.toNat / 8)), toByte (valToB32 ((b0.toNat % 8) * 4)), 61, 61, 61, 61, 61, 61] = some [b0] := by
  have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
  have h0 : b0.toNat / 8 ≤ 31 := by omega
  have h1 : (b0.toNat % 8) * 4 ≤ 31 := by omega
  rw [b32BlockDecodeLenient]
  rw [toByte_valToB32 (b0.toNat / 8) h0, toByte_valToB32 ((b0.toNat % 8) * 4) h1]
  have hnp0 : valToB32 (b0.toNat / 8) ≠ 61 := valToB32_not_pad (b0.toNat / 8) h0
  have hnp1 : valToB32 ((b0.toNat % 8) * 4) ≠ 61 := valToB32_not_pad ((b0.toNat % 8) * 4) h1
  have hvd0 : b32Valid (valToB32 (b0.toNat / 8)) = true := valToB32_valid (b0.toNat / 8) h0
  have hvd1 : b32Valid (valToB32 ((b0.toNat % 8) * 4)) = true := valToB32_valid ((b0.toNat % 8) * 4) h1
  rw [hvd0, hvd1]
  rw [b32ToVal_valToB32 (b0.toNat / 8) h0, b32ToVal_valToB32 ((b0.toNat % 8) * 4) h1]
  simp only [hnp0, hnp1]
  have hb0v : (b0.toNat / 8) * 8 + (((b0.toNat % 8) * 4) / 4) = b0.toNat :=
    byte0 b0.toNat 0 hb0 (by decide)
  rw [hb0v]
  simp [toByte, UInt8.ofNat_toNat]

/-- 2-byte tail. -/
theorem b32BlockDecodeLenient_unapply_pair (b0 b1 : UInt8) :
    b32BlockDecodeLenient [toByte (valToB32 (b0.toNat / 8)), toByte (valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)),
                           toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16)), 61, 61, 61, 61] = some [b0, b1] := by
  have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
  have hb1 : b1.toNat < 256 := UInt8.toNat_lt b1
  have h0 : b0.toNat / 8 ≤ 31 := by omega
  have h1 : (b0.toNat % 8) * 4 + b1.toNat / 64 ≤ 31 := by omega
  have h2 : (b1.toNat / 2) % 32 ≤ 31 := by omega
  have h3 : (b1.toNat % 2) * 16 ≤ 31 := by omega
  rw [b32BlockDecodeLenient]
  rw [toByte_valToB32 (b0.toNat / 8) h0, toByte_valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64) h1,
      toByte_valToB32 ((b1.toNat / 2) % 32) h2, toByte_valToB32 ((b1.toNat % 2) * 16) h3]
  have hnp0 : valToB32 (b0.toNat / 8) ≠ 61 := valToB32_not_pad _ h0
  have hnp1 : valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64) ≠ 61 := valToB32_not_pad _ h1
  have hnp2 : valToB32 ((b1.toNat / 2) % 32) ≠ 61 := valToB32_not_pad _ h2
  have hnp3 : valToB32 ((b1.toNat % 2) * 16) ≠ 61 := valToB32_not_pad _ h3
  have hvd0 : b32Valid (valToB32 (b0.toNat / 8)) = true := valToB32_valid _ h0
  have hvd1 : b32Valid (valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)) = true := valToB32_valid _ h1
  have hvd2 : b32Valid (valToB32 ((b1.toNat / 2) % 32)) = true := valToB32_valid _ h2
  have hvd3 : b32Valid (valToB32 ((b1.toNat % 2) * 16)) = true := valToB32_valid _ h3
  rw [hvd0, hvd1]
  rw [b32ToVal_valToB32 (b0.toNat / 8) h0, b32ToVal_valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64) h1]
  simp only [hnp0, hnp1]
  have hb0v : (b0.toNat / 8) * 8 + (((b0.toNat % 8) * 4 + b1.toNat / 64) / 4) = b0.toNat := byte0 b0.toNat b1.toNat hb0 hb1
  rw [hb0v]
  rw [hvd2, hvd3]
  rw [b32ToVal_valToB32 ((b1.toNat / 2) % 32) h2, b32ToVal_valToB32 ((b1.toNat % 2) * 16) h3]
  simp only [hnp2, hnp3]
  have hb1v : (((b0.toNat % 8) * 4 + b1.toNat / 64) % 4) * 64 + (((b1.toNat / 2) % 32) * 2) + (((b1.toNat % 2) * 16) / 16) = b1.toNat := by
    have h := byte1 b0.toNat b1.toNat 0 hb0 hb1 (by decide)
    simpa using h
  rw [hb1v]
  simp [toByte, UInt8.ofNat_toNat]

/-- 3-byte tail. -/
theorem b32BlockDecodeLenient_unapply_triple (b0 b1 b2 : UInt8) :
    b32BlockDecodeLenient [toByte (valToB32 (b0.toNat / 8)), toByte (valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)),
                           toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)),
                           toByte (valToB32 ((b2.toNat % 16) * 2)), 61, 61, 61] = some [b0, b1, b2] := by
  have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
  have hb1 : b1.toNat < 256 := UInt8.toNat_lt b1
  have hb2 : b2.toNat < 256 := UInt8.toNat_lt b2
  have h0 : b0.toNat / 8 ≤ 31 := by omega
  have h1 : (b0.toNat % 8) * 4 + b1.toNat / 64 ≤ 31 := by omega
  have h2 : (b1.toNat / 2) % 32 ≤ 31 := by omega
  have h3 : (b1.toNat % 2) * 16 + b2.toNat / 16 ≤ 31 := by omega
  have h4 : (b2.toNat % 16) * 2 ≤ 31 := by omega
  rw [b32BlockDecodeLenient]
  rw [toByte_valToB32 (b0.toNat / 8) h0, toByte_valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64) h1,
      toByte_valToB32 ((b1.toNat / 2) % 32) h2, toByte_valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) h3,
      toByte_valToB32 ((b2.toNat % 16) * 2) h4]
  have hnp0 : valToB32 (b0.toNat / 8) ≠ 61 := valToB32_not_pad _ h0
  have hnp1 : valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64) ≠ 61 := valToB32_not_pad _ h1
  have hnp2 : valToB32 ((b1.toNat / 2) % 32) ≠ 61 := valToB32_not_pad _ h2
  have hnp3 : valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) ≠ 61 := valToB32_not_pad _ h3
  have hnp4 : valToB32 ((b2.toNat % 16) * 2) ≠ 61 := valToB32_not_pad _ h4
  have hvd0 : b32Valid (valToB32 (b0.toNat / 8)) = true := valToB32_valid _ h0
  have hvd1 : b32Valid (valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)) = true := valToB32_valid _ h1
  have hvd2 : b32Valid (valToB32 ((b1.toNat / 2) % 32)) = true := valToB32_valid _ h2
  have hvd3 : b32Valid (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)) = true := valToB32_valid _ h3
  have hvd4 : b32Valid (valToB32 ((b2.toNat % 16) * 2)) = true := valToB32_valid _ h4
  rw [hvd0, hvd1]
  rw [b32ToVal_valToB32 (b0.toNat / 8) h0, b32ToVal_valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64) h1]
  simp only [hnp0, hnp1]
  have hb0v : (b0.toNat / 8) * 8 + (((b0.toNat % 8) * 4 + b1.toNat / 64) / 4) = b0.toNat := byte0 b0.toNat b1.toNat hb0 hb1
  rw [hb0v]
  rw [hvd2, hvd3]
  rw [b32ToVal_valToB32 ((b1.toNat / 2) % 32) h2, b32ToVal_valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) h3]
  simp only [hnp2, hnp3]
  have hb1v : (((b0.toNat % 8) * 4 + b1.toNat / 64) % 4) * 64 + (((b1.toNat / 2) % 32) * 2) + (((b1.toNat % 2) * 16 + b2.toNat / 16) / 16) = b1.toNat := byte1 b0.toNat b1.toNat b2.toNat hb0 hb1 hb2
  rw [hb1v]
  rw [hvd4]
  rw [b32ToVal_valToB32 ((b2.toNat % 16) * 2) h4]
  simp only [hnp4]
  have hb2v : (((b1.toNat % 2) * 16 + b2.toNat / 16) % 16) * 16 + (((b2.toNat % 16) * 2) / 2) = b2.toNat := by
    have h := byte2 b1.toNat b2.toNat 0 hb1 hb2 (by decide)
    simpa using h
  rw [hb2v]
  simp [toByte, UInt8.ofNat_toNat]

/-- 4-byte tail. -/
theorem b32BlockDecodeLenient_unapply_quad (b0 b1 b2 b3 : UInt8) :
    b32BlockDecodeLenient [toByte (valToB32 (b0.toNat / 8)), toByte (valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)),
                           toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)),
                           toByte (valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128)), toByte (valToB32 ((b3.toNat / 4) % 32)),
                           toByte (valToB32 ((b3.toNat % 4) * 8)), 61] = some [b0, b1, b2, b3] := by
  have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
  have hb1 : b1.toNat < 256 := UInt8.toNat_lt b1
  have hb2 : b2.toNat < 256 := UInt8.toNat_lt b2
  have hb3 : b3.toNat < 256 := UInt8.toNat_lt b3
  have h0 : b0.toNat / 8 ≤ 31 := by omega
  have h1 : (b0.toNat % 8) * 4 + b1.toNat / 64 ≤ 31 := by omega
  have h2 : (b1.toNat / 2) % 32 ≤ 31 := by omega
  have h3 : (b1.toNat % 2) * 16 + b2.toNat / 16 ≤ 31 := by omega
  have h4 : (b2.toNat % 16) * 2 + b3.toNat / 128 ≤ 31 := by omega
  have h5 : (b3.toNat / 4) % 32 ≤ 31 := by omega
  have h6 : (b3.toNat % 4) * 8 ≤ 31 := by omega
  rw [b32BlockDecodeLenient]
  rw [toByte_valToB32 (b0.toNat / 8) h0, toByte_valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64) h1,
      toByte_valToB32 ((b1.toNat / 2) % 32) h2, toByte_valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) h3,
      toByte_valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128) h4, toByte_valToB32 ((b3.toNat / 4) % 32) h5,
      toByte_valToB32 ((b3.toNat % 4) * 8) h6]
  have hnp0 : valToB32 (b0.toNat / 8) ≠ 61 := valToB32_not_pad _ h0
  have hnp1 : valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64) ≠ 61 := valToB32_not_pad _ h1
  have hnp2 : valToB32 ((b1.toNat / 2) % 32) ≠ 61 := valToB32_not_pad _ h2
  have hnp3 : valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) ≠ 61 := valToB32_not_pad _ h3
  have hnp4 : valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128) ≠ 61 := valToB32_not_pad _ h4
  have hnp5 : valToB32 ((b3.toNat / 4) % 32) ≠ 61 := valToB32_not_pad _ h5
  have hnp6 : valToB32 ((b3.toNat % 4) * 8) ≠ 61 := valToB32_not_pad _ h6
  have hvd0 : b32Valid (valToB32 (b0.toNat / 8)) = true := valToB32_valid _ h0
  have hvd1 : b32Valid (valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)) = true := valToB32_valid _ h1
  have hvd2 : b32Valid (valToB32 ((b1.toNat / 2) % 32)) = true := valToB32_valid _ h2
  have hvd3 : b32Valid (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)) = true := valToB32_valid _ h3
  have hvd4 : b32Valid (valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128)) = true := valToB32_valid _ h4
  have hvd5 : b32Valid (valToB32 ((b3.toNat / 4) % 32)) = true := valToB32_valid _ h5
  have hvd6 : b32Valid (valToB32 ((b3.toNat % 4) * 8)) = true := valToB32_valid _ h6
  rw [hvd0, hvd1]
  rw [b32ToVal_valToB32 (b0.toNat / 8) h0, b32ToVal_valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64) h1]
  simp only [hnp0, hnp1]
  have hb0v : (b0.toNat / 8) * 8 + (((b0.toNat % 8) * 4 + b1.toNat / 64) / 4) = b0.toNat := byte0 b0.toNat b1.toNat hb0 hb1
  rw [hb0v]
  rw [hvd2, hvd3]
  rw [b32ToVal_valToB32 ((b1.toNat / 2) % 32) h2, b32ToVal_valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) h3]
  simp only [hnp2, hnp3]
  have hb1v : (((b0.toNat % 8) * 4 + b1.toNat / 64) % 4) * 64 + (((b1.toNat / 2) % 32) * 2) + (((b1.toNat % 2) * 16 + b2.toNat / 16) / 16) = b1.toNat := byte1 b0.toNat b1.toNat b2.toNat hb0 hb1 hb2
  rw [hb1v]
  rw [hvd4]
  rw [b32ToVal_valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128) h4]
  simp only [hnp4]
  have hb2v : (((b1.toNat % 2) * 16 + b2.toNat / 16) % 16) * 16 + (((b2.toNat % 16) * 2 + b3.toNat / 128) / 2) = b2.toNat := byte2 b1.toNat b2.toNat b3.toNat hb1 hb2 hb3
  rw [hb2v]
  rw [hvd5, hvd6]
  rw [b32ToVal_valToB32 ((b3.toNat / 4) % 32) h5, b32ToVal_valToB32 ((b3.toNat % 4) * 8) h6]
  simp only [hnp5, hnp6]
  have hb3v : (((b2.toNat % 16) * 2 + b3.toNat / 128) % 2) * 128 + (((b3.toNat / 4) % 32) * 4) + (((b3.toNat % 4) * 8) / 8) = b3.toNat := by
    have h := byte3 b2.toNat b3.toNat 0 hb2 hb3 (by decide)
    simpa using h
  rw [hb3v]
  simp [toByte, UInt8.ofNat_toNat]

/-- 5-byte block. -/
theorem b32BlockDecodeLenient_unapply_quintet (b0 b1 b2 b3 b4 : UInt8) :
    b32BlockDecodeLenient [toByte (valToB32 (b0.toNat / 8)), toByte (valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)),
                           toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)),
                           toByte (valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128)), toByte (valToB32 ((b3.toNat / 4) % 32)),
                           toByte (valToB32 ((b3.toNat % 4) * 8 + b4.toNat / 32)), toByte (valToB32 (b4.toNat % 32))] = some [b0, b1, b2, b3, b4] := by
  have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
  have hb1 : b1.toNat < 256 := UInt8.toNat_lt b1
  have hb2 : b2.toNat < 256 := UInt8.toNat_lt b2
  have hb3 : b3.toNat < 256 := UInt8.toNat_lt b3
  have hb4 : b4.toNat < 256 := UInt8.toNat_lt b4
  have h0 : b0.toNat / 8 ≤ 31 := by omega
  have h1 : (b0.toNat % 8) * 4 + b1.toNat / 64 ≤ 31 := by omega
  have h2 : (b1.toNat / 2) % 32 ≤ 31 := by omega
  have h3 : (b1.toNat % 2) * 16 + b2.toNat / 16 ≤ 31 := by omega
  have h4 : (b2.toNat % 16) * 2 + b3.toNat / 128 ≤ 31 := by omega
  have h5 : (b3.toNat / 4) % 32 ≤ 31 := by omega
  have h6 : (b3.toNat % 4) * 8 + b4.toNat / 32 ≤ 31 := by omega
  have h7 : b4.toNat % 32 ≤ 31 := by omega
  rw [b32BlockDecodeLenient]
  rw [toByte_valToB32 (b0.toNat / 8) h0, toByte_valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64) h1,
      toByte_valToB32 ((b1.toNat / 2) % 32) h2, toByte_valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) h3,
      toByte_valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128) h4, toByte_valToB32 ((b3.toNat / 4) % 32) h5,
      toByte_valToB32 ((b3.toNat % 4) * 8 + b4.toNat / 32) h6, toByte_valToB32 (b4.toNat % 32) h7]
  have hnp0 : valToB32 (b0.toNat / 8) ≠ 61 := valToB32_not_pad _ h0
  have hnp1 : valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64) ≠ 61 := valToB32_not_pad _ h1
  have hnp2 : valToB32 ((b1.toNat / 2) % 32) ≠ 61 := valToB32_not_pad _ h2
  have hnp3 : valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) ≠ 61 := valToB32_not_pad _ h3
  have hnp4 : valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128) ≠ 61 := valToB32_not_pad _ h4
  have hnp5 : valToB32 ((b3.toNat / 4) % 32) ≠ 61 := valToB32_not_pad _ h5
  have hnp6 : valToB32 ((b3.toNat % 4) * 8 + b4.toNat / 32) ≠ 61 := valToB32_not_pad _ h6
  have hnp7 : valToB32 (b4.toNat % 32) ≠ 61 := valToB32_not_pad _ h7
  have hvd0 : b32Valid (valToB32 (b0.toNat / 8)) = true := valToB32_valid _ h0
  have hvd1 : b32Valid (valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)) = true := valToB32_valid _ h1
  have hvd2 : b32Valid (valToB32 ((b1.toNat / 2) % 32)) = true := valToB32_valid _ h2
  have hvd3 : b32Valid (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)) = true := valToB32_valid _ h3
  have hvd4 : b32Valid (valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128)) = true := valToB32_valid _ h4
  have hvd5 : b32Valid (valToB32 ((b3.toNat / 4) % 32)) = true := valToB32_valid _ h5
  have hvd6 : b32Valid (valToB32 ((b3.toNat % 4) * 8 + b4.toNat / 32)) = true := valToB32_valid _ h6
  have hvd7 : b32Valid (valToB32 (b4.toNat % 32)) = true := valToB32_valid _ h7
  rw [hvd0, hvd1]
  rw [b32ToVal_valToB32 (b0.toNat / 8) h0, b32ToVal_valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64) h1]
  simp only [hnp0, hnp1]
  have hb0v : (b0.toNat / 8) * 8 + (((b0.toNat % 8) * 4 + b1.toNat / 64) / 4) = b0.toNat := byte0 b0.toNat b1.toNat hb0 hb1
  rw [hb0v]
  rw [hvd2, hvd3]
  rw [b32ToVal_valToB32 ((b1.toNat / 2) % 32) h2, b32ToVal_valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) h3]
  simp only [hnp2, hnp3]
  have hb1v : (((b0.toNat % 8) * 4 + b1.toNat / 64) % 4) * 64 + (((b1.toNat / 2) % 32) * 2) + (((b1.toNat % 2) * 16 + b2.toNat / 16) / 16) = b1.toNat := byte1 b0.toNat b1.toNat b2.toNat hb0 hb1 hb2
  rw [hb1v]
  rw [hvd4]
  rw [b32ToVal_valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128) h4]
  simp only [hnp4]
  have hb2v : (((b1.toNat % 2) * 16 + b2.toNat / 16) % 16) * 16 + (((b2.toNat % 16) * 2 + b3.toNat / 128) / 2) = b2.toNat := byte2 b1.toNat b2.toNat b3.toNat hb1 hb2 hb3
  rw [hb2v]
  rw [hvd5]
  rw [b32ToVal_valToB32 ((b3.toNat / 4) % 32) h5]
  simp only [hnp5]
  simp only [hnp6]
  rw [hvd6]
  rw [b32ToVal_valToB32 ((b3.toNat % 4) * 8 + b4.toNat / 32) h6]
  have hb3v : (((b2.toNat % 16) * 2 + b3.toNat / 128) % 2) * 128 + (((b3.toNat / 4) % 32) * 4) + (((b3.toNat % 4) * 8 + b4.toNat / 32) / 8) = b3.toNat := byte3 b2.toNat b3.toNat b4.toNat hb2 hb3 hb4
  rw [hb3v]
  simp only [hnp7]
  rw [hvd7]
  rw [b32ToVal_valToB32 (b4.toNat % 32) h7]
  have hb4v : (((b3.toNat % 4) * 8 + b4.toNat / 32) % 8) * 32 + (b4.toNat % 32) = b4.toNat := byte4 b3.toNat b4.toNat hb3 hb4
  rw [hb4v]
  simp [toByte, UInt8.ofNat_toNat]

/-- The inverse law: `apply` and `unapply` are mutual inverses. -/
theorem b32BlockIso_law (cs bs : List UInt8) :
    b32BlockApply cs = some bs ↔ b32BlockUnapply bs = some cs := by
  constructor
  · -- backward: apply cs = some bs → unapply bs = some cs
    intro h
    rw [b32BlockApply] at h
    rcases (Iso.bind_eq_some (b32BlockDecodeLenient cs) (fun bs' => if b32BlockUnapply bs' = some cs then some bs' else none) bs).1 h with
      ⟨bs', hdec, hcheck⟩
    have hun : b32BlockUnapply bs' = some cs := by
      by_cases hbs : b32BlockUnapply bs' = some cs
      · exact hbs
      · simp [hbs] at hcheck
    have hbs' : bs' = bs := by
      by_cases hbs : b32BlockUnapply bs' = some cs
      · simpa [hbs] using hcheck
      · simp [hbs] at hcheck
    rw [← hbs']
    exact hun
  · -- forward: unapply bs = some cs → apply cs = some bs
    intro h
    cases bs with
    | nil => simp [b32BlockUnapply] at h
    | cons b0 t0 =>
      cases t0 with
      | nil =>
          have h' : cs = [toByte (valToB32 (b0.toNat / 8)), toByte (valToB32 ((b0.toNat % 8) * 4)), 61, 61, 61, 61, 61, 61] := by
            simpa [b32BlockUnapply] using h.symm
          subst h'
          rw [b32BlockApply, b32BlockDecodeLenient_unapply_single b0]
          simp [b32BlockUnapply]
      | cons b1 t1 =>
        cases t1 with
        | nil =>
            have h' : cs = [toByte (valToB32 (b0.toNat / 8)), toByte (valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)),
                            toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16)), 61, 61, 61, 61] := by
              simpa [b32BlockUnapply] using h.symm
            subst h'
            rw [b32BlockApply, b32BlockDecodeLenient_unapply_pair b0 b1]
            simp [b32BlockUnapply]
        | cons b2 t2 =>
          cases t2 with
          | nil =>
              have h' : cs = [toByte (valToB32 (b0.toNat / 8)), toByte (valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)),
                              toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)),
                              toByte (valToB32 ((b2.toNat % 16) * 2)), 61, 61, 61] := by
                simpa [b32BlockUnapply] using h.symm
              subst h'
              rw [b32BlockApply, b32BlockDecodeLenient_unapply_triple b0 b1 b2]
              simp [b32BlockUnapply]
          | cons b3 t3 =>
            cases t3 with
            | nil =>
                have h' : cs = [toByte (valToB32 (b0.toNat / 8)), toByte (valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)),
                                toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)),
                                toByte (valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128)), toByte (valToB32 ((b3.toNat / 4) % 32)),
                                toByte (valToB32 ((b3.toNat % 4) * 8)), 61] := by
                  simpa [b32BlockUnapply] using h.symm
                subst h'
                rw [b32BlockApply, b32BlockDecodeLenient_unapply_quad b0 b1 b2 b3]
                simp [b32BlockUnapply]
            | cons b4 t4 =>
              cases t4 with
              | nil =>
                  have h' : cs = [toByte (valToB32 (b0.toNat / 8)), toByte (valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)),
                                  toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)),
                                  toByte (valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128)), toByte (valToB32 ((b3.toNat / 4) % 32)),
                                  toByte (valToB32 ((b3.toNat % 4) * 8 + b4.toNat / 32)), toByte (valToB32 (b4.toNat % 32))] := by
                    simpa [b32BlockUnapply] using h.symm
                  subst h'
                  rw [b32BlockApply, b32BlockDecodeLenient_unapply_quintet b0 b1 b2 b3 b4]
                  simp [b32BlockUnapply]
              | cons _ _ => simp [b32BlockUnapply] at h
def b32BlockIso : Iso (List UInt8) (List UInt8) :=
  { apply := b32BlockApply, unapply := b32BlockUnapply, law := b32BlockIso_law }

/-- The base32 element: 8 base32 (or pad) chars grouped into 1–5 bytes. -/
def b32Elem : Codec (List UInt8) := Codec.iso b32BlockIso (count 8 (Codec.satisfy b32OrPad))

/-- `b32Elem` is productive. -/
theorem b32ConsumesByte : ConsumesByte b32Elem := by
  unfold b32Elem
  rw [← productive_iff_consumesByte (Codec.iso b32BlockIso (count 8 (Codec.satisfy b32OrPad)))]
  apply Productive_iso b32BlockIso (count 8 (Codec.satisfy b32OrPad))
  rw [show 8 = 7 + 1 by rfl]
  exact Productive_count_satisfy_succ b32OrPad 7

/-- The base32 decoder (run of blocks). -/
def decodeB32 {n : Nat} (s : Bytes n) : List (List (List UInt8) × Suffix n) :=
  decodeRepeat b32Elem b32ConsumesByte n s

/-- The base32 encoder (run of blocks). -/
def encodeB32 (bs : List (List UInt8)) : Option (Sigma fun n => Bytes n) :=
  encodeRepeat b32Elem bs

/-- The base32 relation. -/
def relB32 : List (List UInt8) → (n : Nat) → Bytes n → Prop :=
  relRepeat (Rel b32Elem)

/-! ## Unambiguity and the inherited roundtrip law -/

/-- `b32Elem` is unambiguous. -/
theorem b32Elem_unambiguous : Unambiguous b32Elem := by
  unfold b32Elem
  apply Unambiguous_iso b32BlockIso (count 8 (Codec.satisfy b32OrPad))
  exact count_satisfy_unambiguous b32OrPad 8

/-- `Rel b32Elem x s` pins the byte length: `n = 8`. -/
theorem Rel_b32Elem_len (x : List UInt8) {n : Nat} (s : Bytes n) :
    Rel b32Elem x s → n = 8 := by
  intro h
  unfold b32Elem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, _, hc⟩
  exact Rel_count_satisfy_len b32OrPad 8 a s hc

/-- The base32 relation is unambiguous. -/
theorem relB32_unambiguous : relUnambiguous relB32 := by
  intro a b n s ha hb
  dsimp [relB32] at ha hb
  induction a generalizing b n s with
  | nil =>
      rw [relRepeat_nil] at ha
      subst n
      cases b with
      | nil => rfl
      | cons y ys =>
          rw [relRepeat_cons] at hb
          rcases hb with ⟨m, hm, s₁, s₂, hs, hy, _⟩
          have hlen : m = 8 := Rel_b32Elem_len y s₁ hy
          have hm0 : m = 0 := by omega
          omega
  | cons x xs ih =>
      cases b with
      | nil =>
          rw [relRepeat_nil] at hb
          rw [relRepeat_cons] at ha
          rcases ha with ⟨mx, hmx, s₁x, s₂x, hsx, hx, hxs⟩
          have hlen : mx = 8 := Rel_b32Elem_len x s₁x hx
          subst n
          have hm0 : mx = 0 := by omega
          omega
      | cons y ys =>
          rw [relRepeat_cons] at ha hb
          rcases ha with ⟨mx, hmx, s₁x, s₂x, hsx, hx, hxs⟩
          rcases hb with ⟨my, hmy, s₁y, s₂y, hsy, hy, hys⟩
          have hlx : mx = 8 := Rel_b32Elem_len x s₁x hx
          have hly : my = 8 := Rel_b32Elem_len y s₁y hy
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
            exact b32Elem_unambiguous s₁x hx (by rw [hpre]; exact hy)
          have htail : xs = ys := by
            exact ih s₂x hxs (by simpa [htaily] using hys)
          rw [hhead, htail]

/-- Full-consumption decode is unambiguous for `b32Elem`. -/
theorem b32DecodeFull_unambiguous {x y : List (List UInt8)} {n : Nat} (s : Bytes n) :
    (x, Suffix.empty n) ∈ decodeRepeat b32Elem b32ConsumesByte n s →
    (y, Suffix.empty n) ∈ decodeRepeat b32Elem b32ConsumesByte n s → x = y := by
  intro hx hy
  rcases (decodeRepeat_spec b32Elem b32ConsumesByte x n s (Suffix.empty n)).1 hx with ⟨s₀x, hsx, hrx⟩
  rcases (decodeRepeat_spec b32Elem b32ConsumesByte y n s (Suffix.empty n)).1 hy with ⟨s₀y, hsy, hry⟩
  have hs₀ : s₀x = s₀y := by
    have hpre : (Suffix.empty n).prepend s₀x = (Suffix.empty n).prepend s₀y := by
      exact hsx.symm.trans hsy
    exact prepend_prefix_eq (Suffix.empty n) s₀x s₀y hpre
  exact relB32_unambiguous s₀x hrx (by rw [hs₀]; exact hry)

/-- The base32 roundtrip law. `[propext, Quot.sound]`-only. -/
theorem roundtrip (bs : List (List UInt8)) {n : Nat} {s : Bytes n} :
    encodeB32 bs = some ⟨n, s⟩ → decodeFull b32Elem b32ConsumesByte n s = some bs := by
  intro he
  have hrel : relRepeat (Rel b32Elem) bs n s := encodeRepeat_rel b32Elem bs he
  have hmem : (bs, Suffix.empty n) ∈ decodeRepeat b32Elem b32ConsumesByte n s := by
    refine (decodeRepeat_spec b32Elem b32ConsumesByte bs n s (Suffix.empty n)).2 ⟨
      cast (congrArg Bytes (Nat.sub_zero n).symm) s, ?_, ?_⟩
    · exact (prepend_empty_eq s).symm
    · exact (relRepeat_cast (Rel b32Elem) bs (Nat.sub_zero n).symm s).2 hrel
  exact (decodeFull_spec b32Elem b32ConsumesByte (fun {x y} {m} (t : Bytes m) =>
    b32DecodeFull_unambiguous (s := t)) s bs).2 hmem

end BaseN.Base32
