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

/-- `b32OrPad` holds of a valid alphabet char. -/
theorem b32OrPad_of_valid {c : UInt8} (h : b32Valid c.toNat = true) : b32OrPad c = true := by
  unfold b32OrPad
  rw [h]
  simp

/-- The pad byte satisfies `b32OrPad`. -/
theorem b32OrPad_pad : b32OrPad 61 = true := by
  unfold b32OrPad
  simp

/-- `b32OrPad (toByte (valToB32 i))` for `i <= 31`: an alphabet char, not the pad. -/
theorem b32OrPad_toByte_valToB32 (i : Nat) (hi : i ≤ 31) :
    b32OrPad (toByte (valToB32 i)) = true := by
  unfold b32OrPad
  rw [toByte_valToB32 i hi, valToB32_valid i hi]
  simp

/-- `b32BlockUnapply` is total on its 1-5-byte domain. -/
theorem b32BlockUnapply_total (bs : List UInt8) (hlen : 1 ≤ bs.length) (hlen5 : bs.length ≤ 5) :
    ∃ cs, b32BlockUnapply bs = some cs := by
  match bs, hlen, hlen5 with
  | [_], _, _ => exact ⟨_, rfl⟩
  | [_, _], _, _ => exact ⟨_, rfl⟩
  | [_, _, _], _, _ => exact ⟨_, rfl⟩
  | [_, _, _, _], _, _ => exact ⟨_, rfl⟩
  | [_, _, _, _, _], _, _ => exact ⟨_, rfl⟩
  | [], h1, _ => simp at h1
  | _ :: _ :: _ :: _ :: _ :: _ :: _, _, h5 => simp at h5

/-- `b32BlockUnapply` always emits exactly 8 chars. -/
theorem b32BlockUnapply_len8 (bs : List UInt8) {cs : List UInt8}
    (h : b32BlockUnapply bs = some cs) : cs.length = 8 := by
  match bs, h with
  | [_], h => simp [b32BlockUnapply] at h; subst h; rfl
  | [_, _], h => simp [b32BlockUnapply] at h; subst h; rfl
  | [_, _, _], h => simp [b32BlockUnapply] at h; subst h; rfl
  | [_, _, _, _], h => simp [b32BlockUnapply] at h; subst h; rfl
  | [_, _, _, _, _], h => simp [b32BlockUnapply] at h; subst h; rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _, h => simp [b32BlockUnapply] at h

/-- Every char emitted by `b32BlockUnapply` is a `b32Valid` alphabet char or the
`=` pad, whatever the block length (1-5). This one fact serves both the block and
the tail totality. -/
theorem b32BlockUnapply_chars {bs cs : List UInt8} (h : b32BlockUnapply bs = some cs) :
    ∀ c ∈ cs, b32OrPad c = true := by
  match bs, h with
  | [v0], h =>
      simp only [b32BlockUnapply, Option.some.injEq] at h
      subst h
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with h | h | h | h | h | h | h | h <;> subst h
      · exact b32OrPad_toByte_valToB32 _ (by have := UInt8.toNat_lt v0; omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_pad
      · exact b32OrPad_pad
      · exact b32OrPad_pad
      · exact b32OrPad_pad
      · exact b32OrPad_pad
      · exact b32OrPad_pad
  | [v0, v1], h =>
      simp only [b32BlockUnapply, Option.some.injEq] at h
      subst h
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      have hb1 : v1.toNat < 256 := UInt8.toNat_lt v1
      rcases hc with h | h | h | h | h | h | h | h <;> subst h
      · exact b32OrPad_toByte_valToB32 _ (by have := UInt8.toNat_lt v0; omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_pad
      · exact b32OrPad_pad
      · exact b32OrPad_pad
      · exact b32OrPad_pad
  | [v0, v1, v2], h =>
      simp only [b32BlockUnapply, Option.some.injEq] at h
      subst h
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      have hb1 : v1.toNat < 256 := UInt8.toNat_lt v1
      have hb2 : v2.toNat < 256 := UInt8.toNat_lt v2
      rcases hc with h | h | h | h | h | h | h | h <;> subst h
      · exact b32OrPad_toByte_valToB32 _ (by have := UInt8.toNat_lt v0; omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_pad
      · exact b32OrPad_pad
      · exact b32OrPad_pad
  | [v0, v1, v2, v3], h =>
      simp only [b32BlockUnapply, Option.some.injEq] at h
      subst h
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      have hb1 : v1.toNat < 256 := UInt8.toNat_lt v1
      have hb2 : v2.toNat < 256 := UInt8.toNat_lt v2
      have hb3 : v3.toNat < 256 := UInt8.toNat_lt v3
      rcases hc with h | h | h | h | h | h | h | h <;> subst h
      · exact b32OrPad_toByte_valToB32 _ (by have := UInt8.toNat_lt v0; omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_pad
  | [v0, v1, v2, v3, v4], h =>
      simp only [b32BlockUnapply, Option.some.injEq] at h
      subst h
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      have hb1 : v1.toNat < 256 := UInt8.toNat_lt v1
      have hb2 : v2.toNat < 256 := UInt8.toNat_lt v2
      have hb3 : v3.toNat < 256 := UInt8.toNat_lt v3
      have hb4 : v4.toNat < 256 := UInt8.toNat_lt v4
      rcases hc with h | h | h | h | h | h | h | h <;> subst h
      · exact b32OrPad_toByte_valToB32 _ (by have := UInt8.toNat_lt v0; omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
      · exact b32OrPad_toByte_valToB32 _ (by omega)
  | _ :: _ :: _ :: _ :: _ :: _ :: _, h => simp [b32BlockUnapply] at h

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

/-! ## The strict value type and the run triple

`B32` is the canonical base32 block/tail spine: full 5-byte blocks, then at most
one terminal tail of 1–4 bytes.  Tail constructors are terminal, so the split is
well-scoped; the *rejection* of data after a pad is the `decodeFullB32 = none`
inequation over the composition, not a type-level fact. -/

/-- The canonical base32 value. -/
inductive B32 where
  | nil
  | full (b0 b1 b2 b3 b4 : UInt8) (rest : B32)
  | tail1 (b0 : UInt8)
  | tail2 (b0 b1 : UInt8)
  | tail3 (b0 b1 b2 : UInt8)
  | tail4 (b0 b1 b2 b3 : UInt8)

/-! ## The `B32` ↔ `List UInt8` canonical block/tail spine -/

/-- The decoded byte list of a `B32` value (full 5-byte blocks, then at most one
1–4-byte terminal tail). -/
def b32BytesOf : B32 → List UInt8
  | B32.nil => []
  | B32.full b0 b1 b2 b3 b4 rest => [b0, b1, b2, b3, b4] ++ b32BytesOf rest
  | B32.tail1 b0 => [b0]
  | B32.tail2 b0 b1 => [b0, b1]
  | B32.tail3 b0 b1 b2 => [b0, b1, b2]
  | B32.tail4 b0 b1 b2 b3 => [b0, b1, b2, b3]

/-- Total split of a byte list into full 5-byte blocks plus a terminal 1–4-byte
tail.  The reverse of `b32BytesOf`. -/
def b32OfBytes : List UInt8 → B32
  | [] => B32.nil
  | [b0] => B32.tail1 b0
  | [b0, b1] => B32.tail2 b0 b1
  | [b0, b1, b2] => B32.tail3 b0 b1 b2
  | [b0, b1, b2, b3] => B32.tail4 b0 b1 b2 b3
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => B32.full b0 b1 b2 b3 b4 (b32OfBytes rest)

/-- `b32BytesOf (b32OfBytes bs) = bs`. -/
theorem b32BytesOf_ofBytes (bs : List UInt8) : b32BytesOf (b32OfBytes bs) = bs := by
  exact go bs
where
  go : (l : List UInt8) → b32BytesOf (b32OfBytes l) = l
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | [_, _, _, _] => rfl
  | b0 :: b1 :: b2 :: b3 :: b4 :: t => by
      unfold b32OfBytes b32BytesOf
      rw [go t]
      rfl
  termination_by l => l.length
  decreasing_by simp +arith

/-- `b32OfBytes (b32BytesOf v) = v`. -/
theorem b32OfBytes_bytesOf (v : B32) : b32OfBytes (b32BytesOf v) = v := by
  induction v with
  | nil => rfl
  | full b0 b1 b2 b3 b4 rest ih =>
      change b32OfBytes ([b0, b1, b2, b3, b4] ++ b32BytesOf rest) = B32.full b0 b1 b2 b3 b4 rest
      have hcons : [b0, b1, b2, b3, b4] ++ b32BytesOf rest = b0 :: b1 :: b2 :: b3 :: b4 :: b32BytesOf rest := rfl
      rw [hcons]
      unfold b32OfBytes
      rw [ih]
  | tail1 b0 => rfl
  | tail2 b0 b1 => rfl
  | tail3 b0 b1 b2 => rfl
  | tail4 b0 b1 b2 b3 => rfl

/-! ## The `Codec`-value full-block element

The full block is the `Run`'s repetition step: `count 8 (satisfy b32Char)` reads
eight alphabet characters (no `=`; a pad-block is the terminal tail and is handled
separately), and `b32BlockIso` maps them to the five recovered bytes. -/

/-- Base32 alphabet character (no `=` pad). -/
def b32Char (b : UInt8) : Bool := b32Valid b.toNat

/-- The full-block element: 8 alphabet chars → 5 bytes (no padding). -/
def b32BlockElem : Codec (List UInt8) :=
  iso b32BlockIso (count 8 (Codec.satisfy b32Char))

/-- `b32BlockElem` consumes 8 bytes per block. -/
theorem b32BlockConsumesByte : ConsumesByte b32BlockElem := by
  rw [← productive_iff_consumesByte, b32BlockElem]
  exact Productive_iso b32BlockIso (count 8 (Codec.satisfy b32Char))
    (Productive_count_satisfy_succ b32Char 7)

/-- `b32BlockElem` is functional (a block relates to a unique byte string). -/
theorem b32BlockElem_functional : Functional b32BlockElem := by
  unfold b32BlockElem
  exact Functional_iso b32BlockIso (count 8 (Codec.satisfy b32Char))
    (Functional_count_satisfy b32Char 8)

/-- Every byte of a `b32BlockElem`-related string is a base32 alphabet character. -/
theorem Rel_b32BlockElem_canonical {x : List UInt8} {m : Nat} {t : Bytes m} :
    Rel b32BlockElem x t → ∀ i : Fin m, b32Char (t i) = true := by
  intro ht
  unfold b32BlockElem at ht
  rw [Rel_iso] at ht
  rcases ht with ⟨a, _, hc⟩
  exact Rel_count_satisfy_forall b32Char 8 a t hc

/-- `b32BlockElem` is unambiguous. -/
theorem b32BlockElem_unambiguous : Unambiguous b32BlockElem := by
  unfold b32BlockElem
  exact Unambiguous_iso b32BlockIso (count 8 (Codec.satisfy b32Char))
    (count_satisfy_unambiguous b32Char 8)

/-- `Rel b32BlockElem bl s` pins the byte length: `n = 8`. -/
theorem Rel_b32BlockElem_len (bl : List UInt8) {n : Nat} (s : Bytes n) :
    Rel b32BlockElem bl s → n = 8 := by
  intro h
  unfold b32BlockElem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, _, hc⟩
  exact Rel_count_satisfy_len b32Char 8 a s hc

/-- The full-block relation is unambiguous (element-level lifts to `relRepeat`). -/
theorem relB32Block_unambiguous : relUnambiguous (relRepeat (Rel b32BlockElem)) := by
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
          have hlen : m = 8 := Rel_b32BlockElem_len y s₁ hy
          have hm0 : m = 0 := by omega
          omega
  | cons x xs ih =>
      cases b with
      | nil =>
          rw [relRepeat_nil] at hb
          rw [relRepeat_cons] at ha
          rcases ha with ⟨mx, hmx, s₁x, s₂x, _, hx, _⟩
          have hlen : mx = 8 := Rel_b32BlockElem_len x s₁x hx
          subst n
          have hm0 : mx = 0 := by omega
          omega
      | cons y ys =>
          rw [relRepeat_cons] at ha hb
          rcases ha with ⟨mx, hmx, s₁x, s₂x, hsx, hx, hxs⟩
          rcases hb with ⟨my, hmy, s₁y, s₂y, hsy, hy, hys⟩
          have hlx : mx = 8 := Rel_b32BlockElem_len x s₁x hx
          have hly : my = 8 := Rel_b32BlockElem_len y s₁y hy
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
            exact b32BlockElem_unambiguous s₁x hx (by rw [hpre]; exact hy)
          have htail : xs = ys := by
            exact ih s₂x hxs (by simpa [htaily] using hys)
          rw [hhead, htail]

/-- Full-consumption decode is unambiguous for `b32BlockElem`. -/
theorem b32BlockDecodeFull_unambiguous {x y : List (List UInt8)} {n : Nat} (s : Bytes n) :
    (x, Suffix.empty n) ∈ decodeRepeat b32BlockElem b32BlockConsumesByte n s →
    (y, Suffix.empty n) ∈ decodeRepeat b32BlockElem b32BlockConsumesByte n s → x = y := by
  intro hx hy
  rcases (decodeRepeat_spec b32BlockElem b32BlockConsumesByte x n s (Suffix.empty n)).1 hx with ⟨s₀x, hsx, hrx⟩
  rcases (decodeRepeat_spec b32BlockElem b32BlockConsumesByte y n s (Suffix.empty n)).1 hy with ⟨s₀y, hsy, hry⟩
  have hs₀ : s₀x = s₀y := by
    have hpre : (Suffix.empty n).prepend s₀x = (Suffix.empty n).prepend s₀y := by
      exact hsx.symm.trans hsy
    exact prepend_prefix_eq (Suffix.empty n) s₀x s₀y hpre
  exact relB32Block_unambiguous s₀x hrx (by rw [hs₀]; exact hry)

/-! ## The terminal-tail element

The terminal tail is a single *padded* block (2/4/5/7 chars + `=`), or the empty
string.  It is decoded *after* the full-block run.  A 5-byte output is a full
block and is rejected by `b32TailIso` (only 1–4-byte outputs), and the recursive
full-block repetition never produces a pad. -/

/-- `b32BlockUnapply` on a 5-byte block emits exactly 8 alphabet chars (no pad). -/
theorem b32BlockUnapply_len5 (bs : List UInt8) (hlen : bs.length = 5) :
    ∃ cs, b32BlockUnapply bs = some cs ∧ cs.length = 8 ∧ ∀ c ∈ cs, b32Char c = true := by
  match bs, hlen with
  | [v0, v1, v2, v3, v4], _ =>
      refine ⟨[toByte (valToB32 (v0.toNat / 8)),
               toByte (valToB32 ((v0.toNat % 8) * 4 + v1.toNat / 64)),
               toByte (valToB32 ((v1.toNat / 2) % 32)),
               toByte (valToB32 ((v1.toNat % 2) * 16 + v2.toNat / 16)),
               toByte (valToB32 ((v2.toNat % 16) * 2 + v3.toNat / 128)),
               toByte (valToB32 ((v3.toNat / 4) % 32)),
               toByte (valToB32 ((v3.toNat % 4) * 8 + v4.toNat / 32)),
               toByte (valToB32 (v4.toNat % 32))], rfl, rfl, ?_⟩
      have hb0 : v0.toNat < 256 := UInt8.toNat_lt v0
      have hb1 : v1.toNat < 256 := UInt8.toNat_lt v1
      have hb2 : v2.toNat < 256 := UInt8.toNat_lt v2
      have hb3 : v3.toNat < 256 := UInt8.toNat_lt v3
      have hb4 : v4.toNat < 256 := UInt8.toNat_lt v4
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with h | h | h | h | h | h | h | h <;> subst h <;> unfold b32Char
      · rw [toByte_valToB32 _ (by omega)]; exact valToB32_valid _ (by omega)
      · rw [toByte_valToB32 _ (by omega)]; exact valToB32_valid _ (by omega)
      · rw [toByte_valToB32 _ (by omega)]; exact valToB32_valid _ (by omega)
      · rw [toByte_valToB32 _ (by omega)]; exact valToB32_valid _ (by omega)
      · rw [toByte_valToB32 _ (by omega)]; exact valToB32_valid _ (by omega)
      · rw [toByte_valToB32 _ (by omega)]; exact valToB32_valid _ (by omega)
      · rw [toByte_valToB32 _ (by omega)]; exact valToB32_valid _ (by omega)
      · rw [toByte_valToB32 _ (by omega)]; exact valToB32_valid _ (by omega)
  | [], h => simp at h
  | [_], h => simp at h
  | [_, _], h => simp at h
  | [_, _, _], h => simp at h
  | [_, _, _, _], h => simp at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _, h => simp at h

/-- Every 5-byte block encodes through `b32BlockElem`: the block element encoder is
total on its domain. -/
theorem b32BlockElem_encode_ne_none (bs : List UInt8) (hlen : bs.length = 5) :
    Codec.encode b32BlockElem bs ≠ none := by
  obtain ⟨cs, hcs, hclen, hcv⟩ := b32BlockUnapply_len5 bs hlen
  unfold b32BlockElem
  simp only [Codec.encode, b32BlockIso, hcs, Option.bind]
  rw [← hclen]
  exact BaseN.Common.count_satisfy_encode_ne_none b32Char cs hcv

/-- `b32TailApply cs` — decode 8 chars to 1–4 bytes only (padded blocks). -/
def b32TailApply (cs : List UInt8) : Option (List UInt8) :=
  match b32BlockApply cs with
  | some [b0] => some [b0]
  | some [b0, b1] => some [b0, b1]
  | some [b0, b1, b2] => some [b0, b1, b2]
  | some [b0, b1, b2, b3] => some [b0, b1, b2, b3]
  | _ => none

/-- `b32TailUnapply bs` — encode 1–4 bytes as a padded 8-char block. -/
def b32TailUnapply (bs : List UInt8) : Option (List UInt8) :=
  match bs with
  | [b0] => b32BlockUnapply [b0]
  | [b0, b1] => b32BlockUnapply [b0, b1]
  | [b0, b1, b2] => b32BlockUnapply [b0, b1, b2]
  | [b0, b1, b2, b3] => b32BlockUnapply [b0, b1, b2, b3]
  | _ => none

/-- `b32TailUnapply` is total on 1-4-byte lists and emits 8 chars, each alphabet or
pad (the pads being exactly the RFC §3.2 terminal padding). -/
theorem b32TailUnapply_len14 (bs : List UInt8)
    (hlen : 1 ≤ bs.length) (hlen4 : bs.length ≤ 4) :
    ∃ cs, b32TailUnapply bs = some cs ∧ cs.length = 8 ∧ ∀ c ∈ cs, b32OrPad c = true := by
  have hblock : ∃ cs, b32BlockUnapply bs = some cs := b32BlockUnapply_total bs hlen (by omega)
  obtain ⟨cs, hcs⟩ := hblock
  refine ⟨cs, ?_, b32BlockUnapply_len8 bs hcs, b32BlockUnapply_chars hcs⟩
  match bs, hlen, hlen4, hcs with
  | [_], _, _, hcs => simp [b32TailUnapply]; exact hcs
  | [_, _], _, _, hcs => simp [b32TailUnapply]; exact hcs
  | [_, _, _], _, _, hcs => simp [b32TailUnapply]; exact hcs
  | [_, _, _, _], _, _, hcs => simp [b32TailUnapply]; exact hcs
  | [], h1, _, _ => simp at h1
  | _ :: _ :: _ :: _ :: _ :: _, _, h4, _ => simp at h4

/-- `b32TailApply` and `b32TailUnapply` are mutual inverses. -/
theorem b32TailIso_law (cs bs : List UInt8) :
    b32TailApply cs = some bs ↔ b32TailUnapply bs = some cs := by
  constructor
  · intro h
    cases hc : b32BlockApply cs with
    | none => simp [b32TailApply, hc] at h
    | some b =>
        cases b with
        | nil => simp [b32TailApply, hc] at h
        | cons b0 t =>
          cases t with
          | nil =>
              simp [b32TailApply, hc] at h
              subst bs
              simp [b32TailUnapply]
              exact (b32BlockIso_law cs [b0]).1 (by simp [hc])
          | cons b1 t2 =>
            cases t2 with
            | nil =>
                simp [b32TailApply, hc] at h
                subst bs
                simp [b32TailUnapply]
                exact (b32BlockIso_law cs [b0, b1]).1 (by simp [hc])
            | cons b2 t3 =>
              cases t3 with
              | nil =>
                  simp [b32TailApply, hc] at h
                  subst bs
                  simp [b32TailUnapply]
                  exact (b32BlockIso_law cs [b0, b1, b2]).1 (by simp [hc])
              | cons b3 t4 =>
                cases t4 with
                | nil =>
                    simp [b32TailApply, hc] at h
                    subst bs
                    simp [b32TailUnapply]
                    exact (b32BlockIso_law cs [b0, b1, b2, b3]).1 (by simp [hc])
                | cons _ _ => simp [b32TailApply, hc] at h
  · intro h
    cases bs with
    | nil => simp [b32TailUnapply] at h
    | cons b0 t =>
      cases t with
      | nil =>
          simp [b32TailUnapply] at h
          have hb : b32BlockUnapply [b0] = some cs := by simpa using h
          have ha : b32BlockApply cs = some [b0] := (b32BlockIso_law cs [b0]).2 hb
          simp [b32TailApply, ha]
      | cons b1 t2 =>
        cases t2 with
        | nil =>
            simp [b32TailUnapply] at h
            have hb : b32BlockUnapply [b0, b1] = some cs := by simpa using h
            have ha : b32BlockApply cs = some [b0, b1] := (b32BlockIso_law cs [b0, b1]).2 hb
            simp [b32TailApply, ha]
        | cons b2 t3 =>
          cases t3 with
          | nil =>
              simp [b32TailUnapply] at h
              have hb : b32BlockUnapply [b0, b1, b2] = some cs := by simpa using h
              have ha : b32BlockApply cs = some [b0, b1, b2] := (b32BlockIso_law cs [b0, b1, b2]).2 hb
              simp [b32TailApply, ha]
          | cons b3 t4 =>
            cases t4 with
            | nil =>
                simp [b32TailUnapply] at h
                have hb : b32BlockUnapply [b0, b1, b2, b3] = some cs := by simpa using h
                have ha : b32BlockApply cs = some [b0, b1, b2, b3] := (b32BlockIso_law cs [b0, b1, b2, b3]).2 hb
                simp [b32TailApply, ha]
            | cons _ _ => simp [b32TailUnapply] at h

/-- The terminal-tail block isomorphism (1–4 bytes ↔ padded 8-char block). -/
def b32TailIso : Iso (List UInt8) (List UInt8) :=
  { apply := b32TailApply, unapply := b32TailUnapply, law := b32TailIso_law }

/-- The terminal-tail element (padded block → 1–4 bytes). -/
def b32TailElem : Codec (List UInt8) :=
  iso b32TailIso (count 8 (Codec.satisfy b32OrPad))

/-- Every 1-4-byte tail encodes through `b32TailElem`: the tail element encoder is
total on its domain. -/
theorem b32TailElem_encode_ne_none (bs : List UInt8)
    (hlen : 1 ≤ bs.length) (hlen4 : bs.length ≤ 4) : Codec.encode b32TailElem bs ≠ none := by
  obtain ⟨cs, hcs, hclen, hcv⟩ := b32TailUnapply_len14 bs hlen hlen4
  unfold b32TailElem
  simp only [Codec.encode, b32TailIso, hcs, Option.bind]
  rw [← hclen]
  exact BaseN.Common.count_satisfy_encode_ne_none b32OrPad cs hcv

/-- `b32TailElem` consumes 8 bytes per (padded) block. -/
theorem b32TailConsumesByte : ConsumesByte b32TailElem := by
  rw [← productive_iff_consumesByte, b32TailElem]
  exact Productive_iso b32TailIso (count 8 (Codec.satisfy b32OrPad))
    (Productive_count_satisfy_succ b32OrPad 7)

/-- `b32TailElem` is functional. -/
theorem b32TailElem_functional : Functional b32TailElem := by
  unfold b32TailElem
  exact Functional_iso b32TailIso (count 8 (Codec.satisfy b32OrPad))
    (Functional_count_satisfy b32OrPad 8)

/-- `b32TailElem` is unambiguous. -/
theorem b32TailElem_unambiguous : Unambiguous b32TailElem := by
  unfold b32TailElem
  exact Unambiguous_iso b32TailIso (count 8 (Codec.satisfy b32OrPad))
    (count_satisfy_unambiguous b32OrPad 8)

/-- `Rel b32TailElem t s` pins the byte length: `n = 8`. -/
theorem Rel_b32TailElem_len (t : List UInt8) {n : Nat} (s : Bytes n) :
    Rel b32TailElem t s → n = 8 := by
  intro h
  unfold b32TailElem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, _, hc⟩
  exact Rel_count_satisfy_len b32OrPad 8 a s hc

/-- The tail relation is unambiguous. -/
theorem relB32Tail_unambiguous : relUnambiguous (relRepeat (Rel b32TailElem)) := by
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
          have hlen : m = 8 := Rel_b32TailElem_len y s₁ hy
          have hm0 : m = 0 := by omega
          omega
  | cons x xs ih =>
      cases b with
      | nil =>
          rw [relRepeat_nil] at hb
          rw [relRepeat_cons] at ha
          rcases ha with ⟨mx, hmx, s₁x, s₂x, _, hx, _⟩
          have hlen : mx = 8 := Rel_b32TailElem_len x s₁x hx
          subst n
          have hm0 : mx = 0 := by omega
          omega
      | cons y ys =>
          rw [relRepeat_cons] at ha hb
          rcases ha with ⟨mx, hmx, s₁x, s₂x, hsx, hx, hxs⟩
          rcases hb with ⟨my, hmy, s₁y, s₂y, hsy, hy, hys⟩
          have hlx : mx = 8 := Rel_b32TailElem_len x s₁x hx
          have hly : my = 8 := Rel_b32TailElem_len y s₁y hy
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
            exact b32TailElem_unambiguous s₁x hx (by rw [hpre]; exact hy)
          have htail : xs = ys := by
            exact ih s₂x hxs (by simpa [htaily] using hys)
          rw [hhead, htail]

/-- Full-consumption decode is unambiguous for `b32TailElem`. -/
theorem b32TailDecodeFull_unambiguous {x y : List (List UInt8)} {n : Nat} (s : Bytes n) :
    (x, Suffix.empty n) ∈ decodeRepeat b32TailElem b32TailConsumesByte n s →
    (y, Suffix.empty n) ∈ decodeRepeat b32TailElem b32TailConsumesByte n s → x = y := by
  intro hx hy
  rcases (decodeRepeat_spec b32TailElem b32TailConsumesByte x n s (Suffix.empty n)).1 hx with ⟨s₀x, hsx, hrx⟩
  rcases (decodeRepeat_spec b32TailElem b32TailConsumesByte y n s (Suffix.empty n)).1 hy with ⟨s₀y, hsy, hry⟩
  have hs₀ : s₀x = s₀y := by
    have hpre : (Suffix.empty n).prepend s₀x = (Suffix.empty n).prepend s₀y := by
      exact hsx.symm.trans hsy
    exact prepend_prefix_eq (Suffix.empty n) s₀x s₀y hpre
  exact relB32Tail_unambiguous s₀x hrx (by rw [hs₀]; exact hry)

/-! ## The `Run` for base32 (full-block repetition) -/

/-- The base32 full-block run: value `List (List UInt8)`, one 5-byte block per step. -/
def b32Run : Run (List UInt8) :=
  { elem := b32BlockElem, step := b32BlockConsumesByte }

/-- The terminal-tail run's element is `b32TailElem` (bounded, one padded block). -/
def b32TailRun : Run (List UInt8) :=
  { elem := b32TailElem, step := b32TailConsumesByte }

/-! ## The uniform whole-input decoder/encoder

The whole base32 decoder is the *backtracking composition* of the full-block
run (`decodeRepeat b32BlockElem`) with the terminal tail (`decodeFull b32TailElem`)
— never a bespoke `parseB32`.  The encoder splits the byte list into full blocks +
a terminal tail and encodes each via the element encoders. -/

/-- The whole-input base32 decoder over a length-indexed byte string: the
full-block run followed by a single terminal tail (D8).  The committed tail is
at most one padded block — a *multi-block* tail (data after a terminal `=` that
is itself a valid padded block, e.g. `"MY======MY======"`) is rejected by the `≤ 1`
guard. -/
def decodeFullB32 {n : Nat} (s : Bytes n) : Option (List UInt8) :=
  List.head? ((decodeRepeat b32BlockElem b32BlockConsumesByte n s).filterMap fun ⟨blocks, t⟩ =>
    match decodeFull b32TailElem b32TailConsumesByte t.remaining t.bytes with
    | some tail =>
        if tail.length ≤ 1 then some (blocks.flatten ++ tail.flatten) else none
    | none => none)

/-- Split a byte list into full 5-byte blocks plus a terminal 0–4-byte tail. -/
def b32Split : List UInt8 → (List (List UInt8) × List UInt8)
  | [] => ([], [])
  | [b] => ([], [b])
  | [a, b] => ([], [a, b])
  | [a, b, c] => ([], [a, b, c])
  | [a, b, c, d] => ([], [a, b, c, d])
  | a :: b :: c :: d :: e :: rest =>
      let (blocks, tail) := b32Split rest
      ([a, b, c, d, e] :: blocks, tail)

/-- `b32Split` relabels the `B32` structure as a full-block list + terminal tail. -/
def b32Split_ofBytes (v : B32) : (List (List UInt8) × List UInt8) :=
  match v with
  | B32.nil => ([], [])
  | B32.tail1 b => ([], [b])
  | B32.tail2 a b => ([], [a, b])
  | B32.tail3 a b c => ([], [a, b, c])
  | B32.tail4 a b c d => ([], [a, b, c, d])
  | B32.full a b c d e rest =>
      let (blocks, tail) := b32Split_ofBytes rest
      ([a, b, c, d, e] :: blocks, tail)

/-- Encode a terminal tail (0–4 bytes); empty tail → empty bytes. -/
def encodeB32Tail (tail : List UInt8) : Option (Sigma fun m => Bytes m) :=
  match tail with
  | [] => some ⟨0, Codec.emptyBytes⟩
  | [b] => Codec.encode b32TailElem [b]
  | [a, b] => Codec.encode b32TailElem [a, b]
  | [a, b, c] => Codec.encode b32TailElem [a, b, c]
  | [a, b, c, d] => Codec.encode b32TailElem [a, b, c, d]
  | _ => none

/-- `b32Split_ofBytes` of a value gives blocks whose flatten, plus the tail, is
exactly the byte list. -/
private theorem b32Split_ofBytes_shape (v : B32) :
    (b32Split_ofBytes v).1.flatten ++ (b32Split_ofBytes v).2 = b32BytesOf v := by
  induction v with
  | nil => rfl
  | tail1 b => rfl
  | tail2 a b => rfl
  | tail3 a b c => rfl
  | tail4 a b c d => rfl
  | full a b c d e rest ih =>
      simp [b32Split_ofBytes, b32BytesOf]
      rw [ih]

/-- Encode the full blocks + terminal tail: `encodeRepeat` over the block element
and the bounded tail element, concatenated into one byte string. -/
def encodeB32' (blocks : List (List UInt8)) (tail : List UInt8) : Option (Sigma fun n => Bytes n) :=
  match encodeRepeat b32BlockElem blocks, encodeB32Tail tail with
  | some b, some t => some ⟨b.1 + t.1, Codec.concat b.2 t.2⟩
  | _, _ => none

/-- The whole-input base32 encoder (over the byte list). -/
def encodeB32 (bs : List UInt8) : Option (Sigma fun n => Bytes n) :=
  let p := b32Split_ofBytes (b32OfBytes bs)
  encodeB32' p.1 p.2

/-- `concat s emptyBytes` is `s` up to the `n + 0 = n` length cast. -/
private theorem concat_empty_eq {n : Nat} (s : Bytes n) :
    Codec.concat s (Codec.emptyBytes : Bytes 0) = cast (congrArg Bytes (Nat.add_zero n)) s := by
  apply Bytes.ext
  intro i
  unfold Codec.concat
  have hi : i.val < n := i.isLt
  simp [hi]

/-- Decoding an encoded tail with `decodeFull b32TailElem` recovers exactly one
tail block (or none, for the empty tail). -/
theorem decodeFull_b32Tail_of_encode (tail : List UInt8) {q : Nat} {st : Bytes q}
    (ht : encodeB32Tail tail = some ⟨q, st⟩) :
    decodeFull b32TailElem b32TailConsumesByte q st = (match tail with | [] => some [] | _ => some [tail]) := by
  cases tail with
  | nil =>
      have hs : (⟨0, (Codec.emptyBytes : Bytes 0)⟩ : Sigma fun k => Bytes k) = ⟨q, st⟩ := by
        simpa [encodeB32Tail] using ht
      cases hs
      exact decodeFull_zero b32TailElem b32TailConsumesByte Codec.emptyBytes
  | cons b t =>
    cases t with
    | nil =>
        have he : Codec.encode b32TailElem [b] = some ⟨q, st⟩ := by
          simpa [encodeB32Tail] using ht
        have hrep : encodeRepeat b32TailElem [[b]] = some ⟨q + 0, Codec.concat st (Codec.emptyBytes : Bytes 0)⟩ := by
          simp [encodeRepeat, he]
        have hrel2 : relRepeat (Rel b32TailElem) [[b]] (q + 0) (Codec.concat st (Codec.emptyBytes : Bytes 0)) :=
          encodeRepeat_rel b32TailElem [[b]] hrep
        have hc : Codec.concat st (Codec.emptyBytes : Bytes 0) = cast (congrArg Bytes (Nat.add_zero q)) st :=
          concat_empty_eq st
        have hrel : relRepeat (Rel b32TailElem) [[b]] q st := by
          rw [hc] at hrel2
          exact (relRepeat_cast (Rel b32TailElem) [[b]] (Nat.add_zero q) st).1 hrel2
        have hmem : ([[b]], Suffix.empty q) ∈ decodeRepeat b32TailElem b32TailConsumesByte q st := by
          refine (decodeRepeat_spec b32TailElem b32TailConsumesByte [[b]] q st (Suffix.empty q)).2 ⟨
            cast (congrArg Bytes (Nat.sub_zero q).symm) st, ?_, ?_⟩
          · exact (prepend_empty_eq st).symm
          · exact (relRepeat_cast (Rel b32TailElem) [[b]] (Nat.sub_zero q).symm st).2 hrel
        exact (decodeFull_spec b32TailElem b32TailConsumesByte
          (fun {x y} {m} (tx : Bytes m) => b32TailDecodeFull_unambiguous (s := tx)) st [[b]]).2 hmem
    | cons a t2 =>
      cases t2 with
      | nil =>
          have he : Codec.encode b32TailElem [b, a] = some ⟨q, st⟩ := by
            simpa [encodeB32Tail] using ht
          have hrep : encodeRepeat b32TailElem [[b, a]] = some ⟨q + 0, Codec.concat st (Codec.emptyBytes : Bytes 0)⟩ := by
            simp [encodeRepeat, he]
          have hrel2 : relRepeat (Rel b32TailElem) [[b, a]] (q + 0) (Codec.concat st (Codec.emptyBytes : Bytes 0)) :=
            encodeRepeat_rel b32TailElem [[b, a]] hrep
          have hc : Codec.concat st (Codec.emptyBytes : Bytes 0) = cast (congrArg Bytes (Nat.add_zero q)) st :=
            concat_empty_eq st
          have hrel : relRepeat (Rel b32TailElem) [[b, a]] q st := by
            rw [hc] at hrel2
            exact (relRepeat_cast (Rel b32TailElem) [[b, a]] (Nat.add_zero q) st).1 hrel2
          have hmem : ([[b, a]], Suffix.empty q) ∈ decodeRepeat b32TailElem b32TailConsumesByte q st := by
            refine (decodeRepeat_spec b32TailElem b32TailConsumesByte [[b, a]] q st (Suffix.empty q)).2 ⟨
              cast (congrArg Bytes (Nat.sub_zero q).symm) st, ?_, ?_⟩
            · exact (prepend_empty_eq st).symm
            · exact (relRepeat_cast (Rel b32TailElem) [[b, a]] (Nat.sub_zero q).symm st).2 hrel
          exact (decodeFull_spec b32TailElem b32TailConsumesByte
            (fun {x y} {m} (tx : Bytes m) => b32TailDecodeFull_unambiguous (s := tx)) st [[b, a]]).2 hmem
      | cons c t3 =>
        cases t3 with
        | nil =>
            have he : Codec.encode b32TailElem [b, a, c] = some ⟨q, st⟩ := by
              simpa [encodeB32Tail] using ht
            have hrep : encodeRepeat b32TailElem [[b, a, c]] = some ⟨q + 0, Codec.concat st (Codec.emptyBytes : Bytes 0)⟩ := by
              simp [encodeRepeat, he]
            have hrel2 : relRepeat (Rel b32TailElem) [[b, a, c]] (q + 0) (Codec.concat st (Codec.emptyBytes : Bytes 0)) :=
              encodeRepeat_rel b32TailElem [[b, a, c]] hrep
            have hc : Codec.concat st (Codec.emptyBytes : Bytes 0) = cast (congrArg Bytes (Nat.add_zero q)) st :=
              concat_empty_eq st
            have hrel : relRepeat (Rel b32TailElem) [[b, a, c]] q st := by
              rw [hc] at hrel2
              exact (relRepeat_cast (Rel b32TailElem) [[b, a, c]] (Nat.add_zero q) st).1 hrel2
            have hmem : ([[b, a, c]], Suffix.empty q) ∈ decodeRepeat b32TailElem b32TailConsumesByte q st := by
              refine (decodeRepeat_spec b32TailElem b32TailConsumesByte [[b, a, c]] q st (Suffix.empty q)).2 ⟨
                cast (congrArg Bytes (Nat.sub_zero q).symm) st, ?_, ?_⟩
              · exact (prepend_empty_eq st).symm
              · exact (relRepeat_cast (Rel b32TailElem) [[b, a, c]] (Nat.sub_zero q).symm st).2 hrel
            exact (decodeFull_spec b32TailElem b32TailConsumesByte
              (fun {x y} {m} (tx : Bytes m) => b32TailDecodeFull_unambiguous (s := tx)) st [[b, a, c]]).2 hmem
        | cons d t4 =>
          cases t4 with
          | nil =>
              have he : Codec.encode b32TailElem [b, a, c, d] = some ⟨q, st⟩ := by
                simpa [encodeB32Tail] using ht
              have hrep : encodeRepeat b32TailElem [[b, a, c, d]] = some ⟨q + 0, Codec.concat st (Codec.emptyBytes : Bytes 0)⟩ := by
                simp [encodeRepeat, he]
              have hrel2 : relRepeat (Rel b32TailElem) [[b, a, c, d]] (q + 0) (Codec.concat st (Codec.emptyBytes : Bytes 0)) :=
                encodeRepeat_rel b32TailElem [[b, a, c, d]] hrep
              have hc : Codec.concat st (Codec.emptyBytes : Bytes 0) = cast (congrArg Bytes (Nat.add_zero q)) st :=
                concat_empty_eq st
              have hrel : relRepeat (Rel b32TailElem) [[b, a, c, d]] q st := by
                rw [hc] at hrel2
                exact (relRepeat_cast (Rel b32TailElem) [[b, a, c, d]] (Nat.add_zero q) st).1 hrel2
              have hmem : ([[b, a, c, d]], Suffix.empty q) ∈ decodeRepeat b32TailElem b32TailConsumesByte q st := by
                refine (decodeRepeat_spec b32TailElem b32TailConsumesByte [[b, a, c, d]] q st (Suffix.empty q)).2 ⟨
                  cast (congrArg Bytes (Nat.sub_zero q).symm) st, ?_, ?_⟩
                · exact (prepend_empty_eq st).symm
                · exact (relRepeat_cast (Rel b32TailElem) [[b, a, c, d]] (Nat.sub_zero q).symm st).2 hrel
              exact (decodeFull_spec b32TailElem b32TailConsumesByte
                (fun {x y} {m} (tx : Bytes m) => b32TailDecodeFull_unambiguous (s := tx)) st [[b, a, c, d]]).2 hmem
          | cons _ _ => simp [encodeB32Tail] at ht

/-! ## Whole-input roundtrip transport: prefix/suffix extraction (base32 mirror)

The whole-input roundtrip `decodeFullB32 (encodeB32 bs) = some bs` composes the
full-block run with the terminal tail.  The block/tail *split-uniqueness* lemma
needs the same pad-dichotomy and transport family base64 landed.
`[propext, Quot.sound]`-only. -/

/-- `decodeFull` is insensitive to a length cast of its byte argument. -/
theorem decodeFull_cast {α : Type} (p : Codec α) (h : ConsumesByte p) :
    ∀ {n m : Nat} (e : n = m) (s : Bytes n),
      decodeFull p h m (cast (congrArg Bytes e) s) = decodeFull p h n s := by
  intro n m e s
  subst e
  rfl

/-- Splitting a byte list into full 5-byte blocks + a terminal tail reassembles it. -/
theorem b32Split_shape (bs : List UInt8) :
    (b32Split bs).1.flatten ++ (b32Split bs).2 = bs := by
  exact go bs
where
  go : (l : List UInt8) → (b32Split l).1.flatten ++ (b32Split l).2 = l
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | [_, _, _, _] => rfl
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => by
      simp [b32Split, go rest]

/-- `b32Split_ofBytes (b32OfBytes bs)` is the direct `b32Split bs`. -/
theorem b32Split_ofBytes_ofBytes (bs : List UInt8) :
    b32Split_ofBytes (b32OfBytes bs) = b32Split bs := by
  exact go bs
where
  go : (l : List UInt8) → b32Split_ofBytes (b32OfBytes l) = b32Split l
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | [_, _, _, _] => rfl
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => by
      simp [b32OfBytes, b32Split_ofBytes, b32Split, go rest]

/-- Decoding an encoded *empty* tail over a dropped suffix is `some []`. -/
theorem decodeFull_b32Tail_suffix_nil {q m : Nat} {st : Bytes q} (sb : Bytes m)
    (ht : encodeB32Tail [] = some ⟨q, st⟩) :
    decodeFull b32TailElem b32TailConsumesByte (Suffix.drop m (concat sb st)).remaining (Suffix.drop m (concat sb st)).bytes
      = some [] := by
  unfold Suffix.drop
  simp only []
  rw [bdrop_concat sb st]
  change decodeFull b32TailElem b32TailConsumesByte (m + q - m)
      (cast (congrArg Bytes (Nat.add_sub_cancel_left m q).symm) st) = some []
  rw [decodeFull_cast b32TailElem b32TailConsumesByte (Nat.add_sub_cancel_left m q).symm st]
  simpa using decodeFull_b32Tail_of_encode [] ht

/-- Decoding an encoded *non-empty* tail over a dropped suffix is `some [tail]`. -/
theorem decodeFull_b32Tail_suffix_cons (tail : List UInt8) {q m : Nat} {st : Bytes q} (sb : Bytes m)
    (ht : encodeB32Tail tail = some ⟨q, st⟩) (hne : tail ≠ []) :
    decodeFull b32TailElem b32TailConsumesByte (Suffix.drop m (concat sb st)).remaining (Suffix.drop m (concat sb st)).bytes
      = some [tail] := by
  unfold Suffix.drop
  simp only []
  rw [bdrop_concat sb st]
  change decodeFull b32TailElem b32TailConsumesByte (m + q - m)
      (cast (congrArg Bytes (Nat.add_sub_cancel_left m q).symm) st) = some [tail]
  rw [decodeFull_cast b32TailElem b32TailConsumesByte (Nat.add_sub_cancel_left m q).symm st]
  have h := decodeFull_b32Tail_of_encode tail ht
  cases tail with
  | nil => exact False.elim (hne rfl)
  | cons x t =>
      cases t with
      | nil => simpa using h
      | cons y t2 =>
          cases t2 with
          | nil => simpa using h
          | cons z t3 =>
              cases t3 with
              | nil => simpa using h
              | cons w t4 =>
                  cases t4 with
                  | nil => simpa using h
                  | cons _ _ => simp [encodeB32Tail] at ht

/-- A pad byte is not a base32 alphabet character. -/
theorem b32Char_pad_false : b32Char (UInt8.ofNat 61) = false := by
  unfold b32Char b32Valid b32ToVal
  decide

/-- A block element never relates to a byte string containing a pad byte. -/
theorem not_rel_b32BlockElem_of_pad (x : List UInt8) {m : Nat} (s : Bytes m) :
    (∃ i : Fin m, (s i).toNat = 61) → ¬ Rel b32BlockElem x s := by
  intro hpad hrel
  rcases hpad with ⟨i, hi⟩
  have hcanon : b32Char (s i) = true := Rel_b32BlockElem_canonical hrel i
  unfold b32Char at hcanon
  rw [hi] at hcanon
  have hfalse : b32Valid 61 = false := by decide
  rw [hfalse] at hcanon
  exact Bool.false_ne_true hcanon

/-- A `Rel b32BlockElem` value is a 5-byte list (a full alphabet block). -/
theorem Rel_b32BlockElem_size (x : List UInt8) {n : Nat} (s : Bytes n) :
    Rel b32BlockElem x s → x.length = 5 := by
  intro h
  unfold b32BlockElem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, ha, hr⟩
  have hofn : List.ofFn s = a := Rel_count_satisfy_ofFn b32Char 8 a s hr
  have hnopad : ∀ c ∈ a, c.toNat ≠ 61 := by
    intro c hc
    have hmem : c ∈ List.ofFn s := by rwa [hofn]
    rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, hi'⟩
    have hc_eq : c = s ⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩ := hi'.symm.trans (List.getElem_ofFn hi)
    have hbc : b32Char c = true := by
      rw [hc_eq]
      exact Rel_count_satisfy_forall b32Char 8 a s hr ⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩
    unfold b32Char at hbc
    intro heq
    rw [heq] at hbc
    have hpf : b32Valid 61 = false := by decide
    rw [hpf] at hbc
    exact Bool.false_ne_true hbc
  have hun : b32BlockUnapply x = some a := (b32BlockIso_law a x).1 ha
  cases x with
  | nil => simp [b32BlockUnapply] at hun
  | cons x0 xs =>
      cases xs with
      | nil =>
          simp [b32BlockUnapply] at hun
          have hmem : (UInt8.ofNat 61) ∈ a := by rw [← hun]; simp
          exact False.elim (hnopad (UInt8.ofNat 61) hmem rfl)
      | cons x1 xs1 =>
          cases xs1 with
          | nil =>
              simp [b32BlockUnapply] at hun
              have hmem : (UInt8.ofNat 61) ∈ a := by rw [← hun]; simp
              exact False.elim (hnopad (UInt8.ofNat 61) hmem rfl)
          | cons x2 xs2 =>
              cases xs2 with
              | nil =>
                  simp [b32BlockUnapply] at hun
                  have hmem : (UInt8.ofNat 61) ∈ a := by rw [← hun]; simp
                  exact False.elim (hnopad (UInt8.ofNat 61) hmem rfl)
              | cons x3 xs3 =>
                  cases xs3 with
                  | nil =>
                      simp [b32BlockUnapply] at hun
                      have hmem : (UInt8.ofNat 61) ∈ a := by rw [← hun]; simp
                      exact False.elim (hnopad (UInt8.ofNat 61) hmem rfl)
                  | cons x4 xs4 =>
                      cases xs4 with
                      | nil => rfl
                      | cons _ _ => simp [b32BlockUnapply] at hun

/-- A `Rel b32TailElem` value is a 1- to 4-byte list (a padded block). -/
theorem Rel_b32TailElem_size (x : List UInt8) {n : Nat} (s : Bytes n) :
    Rel b32TailElem x s → x.length = 1 ∨ x.length = 2 ∨ x.length = 3 ∨ x.length = 4 := by
  intro h
  unfold b32TailElem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, ha, _⟩
  unfold b32TailIso at ha
  change b32TailApply a = some x at ha
  unfold b32TailApply at ha
  cases hb : b32BlockApply a with
  | none => simp [hb] at ha
  | some bl =>
      cases bl with
      | nil => simp [hb] at ha
      | cons b0 t =>
          cases t with
          | nil => simp [hb] at ha; cases ha; left; rfl
          | cons b1 t2 =>
              cases t2 with
              | nil => simp [hb] at ha; cases ha; right; left; rfl
              | cons b2 t3 =>
                  cases t3 with
                  | nil => simp [hb] at ha; cases ha; right; right; left; rfl
                  | cons b3 t4 =>
                      cases t4 with
                      | nil => simp [hb] at ha; cases ha; right; right; right; rfl
                      | cons _ _ => simp [hb] at ha

/-- The pad-dichotomy rejection: a value cannot be both a full block (5 bytes,
no pad) and a terminal tail (1–4 bytes, padded). -/
theorem Rel_b32BlockElem_not_tail (x : List UInt8) {n m : Nat} (s : Bytes n) (t : Bytes m) :
    Rel b32BlockElem x s → Rel b32TailElem x t → False := by
  intro hb ht
  have h5 : x.length = 5 := Rel_b32BlockElem_size x s hb
  have h14 := Rel_b32TailElem_size x t ht
  rcases h14 with h1 | h2 | h3 | h4 <;> omega

/-- A `Rel b32TailElem`-related string contains a `=` pad byte. -/
theorem Rel_b32TailElem_has_pad (x : List UInt8) {n : Nat} (s : Bytes n) :
    Rel b32TailElem x s → (∃ i : Fin n, (s i).toNat = 61) := by
  intro h
  unfold b32TailElem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, ha, hr⟩
  have hofn : List.ofFn s = a := Rel_count_satisfy_ofFn b32OrPad 8 a s hr
  unfold b32TailIso at ha
  change b32TailApply a = some x at ha
  unfold b32TailApply at ha
  cases hb : b32BlockApply a with
  | none => simp [hb] at ha
  | some bl =>
      cases bl with
      | nil => simp [hb] at ha
      | cons b0 bl1 =>
        cases bl1 with
        | nil =>
            have hun : b32BlockUnapply [b0] = some a := (b32BlockIso_law a [b0]).1 (by simpa using hb)
            simp [b32BlockUnapply] at hun
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
            have hun : b32BlockUnapply [b0, b1] = some a := (b32BlockIso_law a [b0, b1]).1 (by simpa using hb)
            simp [b32BlockUnapply] at hun
            have hmem : (UInt8.ofNat 61) ∈ a := by rw [← hun]; simp
            rw [← hofn] at hmem
            rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, hi'⟩
            refine ⟨⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩, ?_⟩
            have hbyte : s ⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩ = (UInt8.ofNat 61) := by
              exact (List.getElem_ofFn hi).symm.trans hi'
            have hval : (s ⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩).toNat = 61 := by
              simpa using congrArg UInt8.toNat hbyte
            exact hval
          | cons b2 bl3 =>
            cases bl3 with
            | nil =>
              have hun : b32BlockUnapply [b0, b1, b2] = some a := (b32BlockIso_law a [b0, b1, b2]).1 (by simpa using hb)
              simp [b32BlockUnapply] at hun
              have hmem : (UInt8.ofNat 61) ∈ a := by rw [← hun]; simp
              rw [← hofn] at hmem
              rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, hi'⟩
              refine ⟨⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩, ?_⟩
              have hbyte : s ⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩ = (UInt8.ofNat 61) := by
                exact (List.getElem_ofFn hi).symm.trans hi'
              have hval : (s ⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩).toNat = 61 := by
                simpa using congrArg UInt8.toNat hbyte
              exact hval
            | cons b3 bl4 =>
              cases bl4 with
              | nil =>
                have hun : b32BlockUnapply [b0, b1, b2, b3] = some a := (b32BlockIso_law a [b0, b1, b2, b3]).1 (by simpa using hb)
                simp [b32BlockUnapply] at hun
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
                -- 5 bytes: b32TailApply rejects (returns none)
                simp [hb] at ha

/-! ## Whole-input roundtrip (base32 mirror)

`decodeFullB32 (encodeB32 bs) = some bs`.  `[propext, Quot.sound]`-only. -/

/-- A `relRepeat (Rel b32BlockElem)` consumes `8 · length` bytes (each block is an
8-char element). -/
theorem relB32Block_len {xs : List (List UInt8)} {n : Nat} (s : Bytes n) :
    relRepeat (Rel b32BlockElem) xs n s → n = 8 * xs.length := by
  intro h
  induction xs generalizing n with
  | nil =>
      rw [relRepeat_nil] at h
      subst n
      rfl
  | cons x rest ih =>
      rw [relRepeat_cons] at h
      rcases h with ⟨m, _hm, s₁, s₂, _hs, hrel₁, hrelRest⟩
      have h8 : m = 8 := Rel_b32BlockElem_len x s₁ hrel₁
      subst m
      have hrest : n - 8 = 8 * rest.length := ih s₂ hrelRest
      rw [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- A `relRepeat (Rel b32TailElem)` consumes `8 · length` bytes. -/
theorem relB32Tail_len {xs : List (List UInt8)} {n : Nat} (s : Bytes n) :
    relRepeat (Rel b32TailElem) xs n s → n = 8 * xs.length := by
  intro h
  induction xs generalizing n with
  | nil =>
      rw [relRepeat_nil] at h
      subst n
      rfl
  | cons x rest ih =>
      rw [relRepeat_cons] at h
      rcases h with ⟨m, _hm, s₁, s₂, _hs, hrel₁, hrelRest⟩
      have h8 : m = 8 := Rel_b32TailElem_len x s₁ hrel₁
      subst m
      have hrest : n - 8 = 8 * rest.length := ih s₂ hrelRest
      rw [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-! ## Encoded-output structure (inputs to the boundary-pin)

`encodeRepeat b32BlockElem blocks` produces alphabet-only (no-pad) bytes, and a
non-empty `encodeB32Tail` produces a padded block containing `=`. -/

/-- The full-block encoding is alphabet-only. -/
theorem encodeB32Block_nopad (blocks : List (List UInt8)) {n : Nat} {s : Bytes n}
    (he : encodeRepeat b32BlockElem blocks = some ⟨n, s⟩) :
    ∀ i : Fin n, b32Char (s i) = true := by
  have hrel : relRepeat (Rel b32BlockElem) blocks n s := encodeRepeat_rel b32BlockElem blocks he
  exact relRepeat_forall b32Char (fun x {m} t ht => Rel_b32BlockElem_canonical (t := t) ht) blocks n s hrel

/-- A non-empty terminal-tail encoding contains a `=` pad byte. -/
theorem encodeB32Tail_has_pad (tail : List UInt8) {n : Nat} {s : Bytes n}
    (hne : tail ≠ []) (he : encodeB32Tail tail = some ⟨n, s⟩) :
    ∃ i : Fin n, (s i).toNat = 61 := by
  cases tail with
  | nil => exact False.elim (hne rfl)
  | cons b t =>
      cases t with
      | nil =>
          have henc : Codec.encode b32TailElem [b] = some ⟨n, s⟩ := by simpa [encodeB32Tail] using he
          have hrel : Rel b32TailElem [b] s := encode_rel b32TailElem [b] henc
          exact Rel_b32TailElem_has_pad [b] s hrel
      | cons b1 t1 =>
          cases t1 with
          | nil =>
              have henc : Codec.encode b32TailElem [b, b1] = some ⟨n, s⟩ := by simpa [encodeB32Tail] using he
              have hrel : Rel b32TailElem [b, b1] s := encode_rel b32TailElem [b, b1] henc
              exact Rel_b32TailElem_has_pad [b, b1] s hrel
          | cons b2 t2 =>
              cases t2 with
              | nil =>
                  have henc : Codec.encode b32TailElem [b, b1, b2] = some ⟨n, s⟩ := by simpa [encodeB32Tail] using he
                  have hrel : Rel b32TailElem [b, b1, b2] s := encode_rel b32TailElem [b, b1, b2] henc
                  exact Rel_b32TailElem_has_pad [b, b1, b2] s hrel
              | cons b3 t3 =>
                  cases t3 with
                  | nil =>
                      have henc : Codec.encode b32TailElem [b, b1, b2, b3] = some ⟨n, s⟩ := by simpa [encodeB32Tail] using he
                      have hrel : Rel b32TailElem [b, b1, b2, b3] s := encode_rel b32TailElem [b, b1, b2, b3] henc
                      exact Rel_b32TailElem_has_pad [b, b1, b2, b3] s hrel
                  | cons _ _ => simp [encodeB32Tail] at he

/-- `encodeB32Tail tail = some ⟨n, s⟩` pins the encoded length to `0` (empty
tail) or `8` (one padded block). -/
theorem encodeB32Tail_len (tail : List UInt8) {n : Nat} {s : Bytes n}
    (he : encodeB32Tail tail = some ⟨n, s⟩) :
    n = 0 ∨ n = 8 := by
  cases tail with
  | nil =>
      have hs : (⟨0, (Codec.emptyBytes : Bytes 0)⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by
        simpa [encodeB32Tail] using he
      cases hs
      left; rfl
  | cons b t =>
      cases t with
      | nil =>
          have henc : Codec.encode b32TailElem [b] = some ⟨n, s⟩ := by simpa [encodeB32Tail] using he
          have hrel : Rel b32TailElem [b] s := encode_rel b32TailElem [b] henc
          have hlen : n = 8 := Rel_b32TailElem_len [b] s hrel
          right; exact hlen
      | cons b1 t1 =>
          cases t1 with
          | nil =>
              have henc : Codec.encode b32TailElem [b, b1] = some ⟨n, s⟩ := by simpa [encodeB32Tail] using he
              have hrel : Rel b32TailElem [b, b1] s := encode_rel b32TailElem [b, b1] henc
              have hlen : n = 8 := Rel_b32TailElem_len [b, b1] s hrel
              right; exact hlen
          | cons b2 t2 =>
              cases t2 with
              | nil =>
                  have henc : Codec.encode b32TailElem [b, b1, b2] = some ⟨n, s⟩ := by simpa [encodeB32Tail] using he
                  have hrel : Rel b32TailElem [b, b1, b2] s := encode_rel b32TailElem [b, b1, b2] henc
                  have hlen : n = 8 := Rel_b32TailElem_len [b, b1, b2] s hrel
                  right; exact hlen
              | cons b3 t3 =>
                  cases t3 with
                  | nil =>
                      have henc : Codec.encode b32TailElem [b, b1, b2, b3] = some ⟨n, s⟩ := by simpa [encodeB32Tail] using he
                      have hrel : Rel b32TailElem [b, b1, b2, b3] s := encode_rel b32TailElem [b, b1, b2, b3] henc
                      have hlen : n = 8 := Rel_b32TailElem_len [b, b1, b2, b3] s hrel
                      right; exact hlen
                  | cons _ _ => simp [encodeB32Tail] at he

/-! ## Whole-input roundtrip transport: prefix/suffix extraction (base32 mirror)

The block/tail split-uniqueness lemma's boundary pin rests on extracting the
decoded consumed-prefix / remaining bytes back to the committed block/tail.
`[propext, Quot.sound]`-only. -/

/-- From `t'.prepend s₀ = concat a b` and `m₁ + m₂ - t'.remaining = m₁`, the
consumed prefix `s₀` is exactly `a`. -/
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

/-- From `t'.prepend s₀ = concat a b` and `t'.remaining = m₂`, the remaining
suffix `t'.bytes` is exactly `b` (up to the length cast). -/
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
the full-block run and the terminal tail.  `[propext, Quot.sound]`-only. -/

/-- Reading the consumed prefix of a `prepend`-reassembly. -/
private theorem prepend_prefix_read {m₁ m₂ : Nat} (t' : Suffix (m₁ + m₂))
    (s₀ : Bytes (m₁ + m₂ - t'.remaining)) (i : Fin (m₁ + m₂ - t'.remaining)) :
    s₀ i = (t'.prepend s₀) ⟨i.val, (by omega : i.val < m₁ + m₂)⟩ := by
  rw [prepend_apply]
  unfold concat
  rw [cast_fin_symm]
  · simp [i.isLt]
  · omega

/-- Reading the remaining suffix of a `prepend`-reassembly against the committed
`concat`. -/
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
region: its first 8 bytes are `blkBytes`-region bytes (no `=`), but a tail block
always contains a `=` pad byte. -/
private theorem b32_first_tail_block_not_alphabet
    {m₁ m₂ : Nat} (blkBytes : Bytes m₁) (tailBytes : Bytes m₂)
    (t : List UInt8) (rest : List (List UInt8))
    (t' : Suffix (m₁ + m₂)) (s₀ : Bytes (m₁ + m₂ - t'.remaining))
    (htail : relRepeat (Rel b32TailElem) (t :: rest) t'.remaining t'.bytes)
    (h : t'.prepend s₀ = concat blkBytes tailBytes)
    (hblk : ∀ i : Fin m₁, b32Char (blkBytes i) = true)
    (hL8 : (m₁ + m₂ - t'.remaining) + 8 ≤ m₁) :
    False := by
  rw [relRepeat_cons] at htail
  rcases htail with ⟨m, hm, s₁, s₂, hs, ht₁, _⟩
  have hm8 : m = 8 := Rel_b32TailElem_len t s₁ ht₁
  have hpad₁ : ∃ i : Fin m, (s₁ i).toNat = 61 := Rel_b32TailElem_has_pad t s₁ ht₁
  rcases hpad₁ with ⟨i, hi⟩
  have hi_lt_m : i.val < m := i.isLt
  have hi_lt_t' : i.val < t'.remaining := by omega
  have hs₁read : s₁ i = t'.bytes ⟨i.val, hi_lt_t'⟩ := by
    rw [hs]
    simpa using (splice_prefix_read hm s₁ s₂ ⟨i.val, hi_lt_t'⟩ hi_lt_m).symm
  have ht'pad : (t'.bytes ⟨i.val, hi_lt_t'⟩).toNat = 61 := by
    rw [← hs₁read]
    exact hi
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
    have hi8 : i.val < 8 := by omega
    have hlt : i.val + (m₁ + m₂ - t'.remaining) < m₁ := by omega
    simp [hlt]
  have hblkpad : (blkBytes ⟨i.val + (m₁ + m₂ - t'.remaining), (by omega : i.val + (m₁ + m₂ - t'.remaining) < m₁)⟩).toNat = 61 := by
    rw [← hconcat_read]
    exact hconcatpad
  have hcanon := hblk ⟨i.val + (m₁ + m₂ - t'.remaining), (by omega : i.val + (m₁ + m₂ - t'.remaining) < m₁)⟩
  unfold b32Char at hcanon
  rw [hblkpad] at hcanon
  have hfalse : b32Valid 61 = false := by decide
  rw [hfalse] at hcanon
  exact Bool.false_ne_true hcanon

/-- `8 * a < 8 * b → a < b`. -/
private theorem eight_mul_lt_of_lt {a b : Nat} (h : 8 * a < 8 * b) : a < b := by
  omega

/-- The block/tail boundary pin: the full-block run of a padded base consumes
exactly `m₁` bytes, leaving exactly the terminal tail `m₂`. -/
theorem b32_boundary_pin
    {m₁ m₂ : Nat} (blkBytes : Bytes m₁) (tailBytes : Bytes m₂)
    (blocks blocks' : List (List UInt8)) (tail'' : List (List UInt8))
    (t' : Suffix (m₁ + m₂)) (s₀ : Bytes (m₁ + m₂ - t'.remaining))
    (henc : relRepeat (Rel b32BlockElem) blocks m₁ blkBytes)
    (hblock : relRepeat (Rel b32BlockElem) blocks' (m₁ + m₂ - t'.remaining) s₀)
    (htail : relRepeat (Rel b32TailElem) tail'' t'.remaining t'.bytes)
    (h : t'.prepend s₀ = concat blkBytes tailBytes)
    (hm₂ : m₂ = 0 ∨ m₂ = 8)
    (hpad : m₂ ≠ 0 → ∃ i : Fin m₂, (tailBytes i).toNat = 61) :
    t'.remaining = m₂ := by
  have hs₀ : ∀ i : Fin (m₁ + m₂ - t'.remaining), b32Char (s₀ i) = true :=
    relRepeat_forall b32Char (fun x {m} t ht => Rel_b32BlockElem_canonical (t := t) ht) blocks' (m₁ + m₂ - t'.remaining) s₀ hblock
  have hblk : ∀ i : Fin m₁, b32Char (blkBytes i) = true :=
    relRepeat_forall b32Char (fun x {m} t ht => Rel_b32BlockElem_canonical (t := t) ht) blocks m₁ blkBytes henc
  have hL : m₁ + m₂ - t'.remaining = 8 * blocks'.length := relB32Block_len s₀ hblock
  have hm₁len : m₁ = 8 * blocks.length := relB32Block_len blkBytes henc
  have ht' : t'.remaining = 8 * tail''.length := relB32Tail_len t'.bytes htail
  rcases hm₂ with hm₂0 | hm₂8
  · -- m₂ = 0 (empty tail): the block run must consume everything
    cases tail'' with
    | nil =>
        have ht'0 : t'.remaining = 0 := by simpa using ht'
        omega
    | cons t rest =>
        have ht'pos : 8 ≤ t'.remaining := by
          rw [ht']
          simp only [List.length_cons]
          omega
        have hL8 : (m₁ + m₂ - t'.remaining) + 8 ≤ m₁ := by
          have ht'le : t'.remaining ≤ m₁ := by simpa [hm₂0] using t'.hle
          omega
        exact False.elim (b32_first_tail_block_not_alphabet blkBytes tailBytes t rest t' s₀ htail h hblk hL8)
  · -- m₂ = 8 (padded tail): the block run must stop exactly at m₁
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
      unfold b32Char at hcanon
      rw [hs₀pad] at hcanon
      have hfalse : b32Valid 61 = false := by decide
      rw [hfalse] at hcanon
      exact Bool.false_ne_true hcanon
    have hL_le_j : m₁ + m₂ - t'.remaining ≤ m₁ + ip.val := Nat.le_of_not_gt hnot
    have hL_le_m₁7 : m₁ + m₂ - t'.remaining ≤ m₁ + 7 := by omega
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
            have h1 : 8 * blocks'.length < 8 * blocks.length := by
              rw [← hL, ← hm₁len]
              exact hL_lt
            exact eight_mul_lt_of_lt h1
          have hL8 : (m₁ + m₂ - t'.remaining) + 8 ≤ m₁ := by
            have hlen_succ : blocks'.length + 1 ≤ blocks.length := Nat.succ_le_of_lt hlen_lt
            have h8 : 8 * blocks'.length + 8 ≤ 8 * blocks.length := by
              have h := Nat.mul_le_mul_left 8 hlen_succ
              simpa [Nat.mul_add] using h
            omega
          exact False.elim (b32_first_tail_block_not_alphabet blkBytes tailBytes t rest t' s₀ htail h hblk hL8)

/-- The block run extracted by the whole-input decoder is the committed block
run: once the boundary pin fixes `t'.remaining = m₂`, the decoded block prefix
`s₀` is exactly `blkBytes`, and `relB32Block_unambiguous` pins `blocks' = blocks`. -/
theorem b32_block_run_of_boundary
    {m₁ m₂ : Nat} (blkBytes : Bytes m₁) (tailBytes : Bytes m₂)
    (blocks blocks' : List (List UInt8))
    (t' : Suffix (m₁ + m₂)) (s₀ : Bytes (m₁ + m₂ - t'.remaining))
    (henc : relRepeat (Rel b32BlockElem) blocks m₁ blkBytes)
    (hblock : relRepeat (Rel b32BlockElem) blocks' (m₁ + m₂ - t'.remaining) s₀)
    (h : t'.prepend s₀ = concat blkBytes tailBytes)
    (hrem : t'.remaining = m₂) :
    blocks' = blocks := by
  have he : m₁ + m₂ - t'.remaining = m₁ := by omega
  have hblock' : relRepeat (Rel b32BlockElem) blocks' m₁ (cast (congrArg Bytes he) s₀) :=
    (relRepeat_cast (Rel b32BlockElem) blocks' he s₀).2 hblock
  have hs₀ : cast (congrArg Bytes he) s₀ = blkBytes :=
    prepend_concat_prefix_cast blkBytes tailBytes t' s₀ he h
  rw [hs₀] at hblock'
  exact relB32Block_unambiguous blkBytes hblock' henc

/-! ## Whole-input roundtrip assembly (base32 mirror)

The roundtrip `decodeFullB32 (encodeB32 bs) = some bs`.  `[propext, Quot.sound]`-only. -/

/-- The committed encode of `bs` produces a `decodeFullB32`-candidate. -/
theorem decodeFullB32_mem_encode (bs : List UInt8) {n : Nat} {s : Bytes n}
    (he : encodeB32 bs = some ⟨n, s⟩) :
    bs ∈ (decodeRepeat b32BlockElem b32BlockConsumesByte n s).filterMap
      (fun ⟨blocks, t⟩ =>
        match decodeFull b32TailElem b32TailConsumesByte t.remaining t.bytes with
        | some tail => if tail.length ≤ 1 then some (blocks.flatten ++ tail.flatten) else none
        | none => none) := by
  let blocks := (b32Split_ofBytes (b32OfBytes bs)).1
  let tail := (b32Split_ofBytes (b32OfBytes bs)).2
  cases heb : encodeRepeat b32BlockElem blocks with
  | none =>
      unfold encodeB32 encodeB32' at he
      simp [blocks, heb] at he
  | some b =>
      cases het : encodeB32Tail tail with
      | none =>
          unfold encodeB32 encodeB32' at he
          simp [blocks, tail, heb, het] at he
      | some t =>
          rcases b with ⟨m₁, blkBytes⟩
          rcases t with ⟨m₂, tailBytes⟩
          have hpair : (⟨m₁ + m₂, Codec.concat blkBytes tailBytes⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by
            have he' : some (⟨m₁ + m₂, Codec.concat blkBytes tailBytes⟩ : Sigma fun k => Bytes k) = some ⟨n, s⟩ := by
              unfold encodeB32 encodeB32' at he
              simpa [blocks, tail, heb, het] using he
            exact Option.some.inj he'
          cases hpair
          have hblkmem : (blocks, Suffix.empty m₁) ∈ decodeRepeat b32BlockElem b32BlockConsumesByte m₁ blkBytes :=
            (decodeRepeat_spec b32BlockElem b32BlockConsumesByte blocks m₁ blkBytes (Suffix.empty m₁)).2
              ⟨cast (congrArg Bytes (Nat.sub_zero m₁).symm) blkBytes, (prepend_empty_eq blkBytes).symm,
                (relRepeat_cast (Rel b32BlockElem) blocks (Nat.sub_zero m₁).symm blkBytes).2
                  (encodeRepeat_rel b32BlockElem blocks heb)⟩
          have hblkpre : (blocks, Suffix.drop m₁ (Codec.concat blkBytes tailBytes)) ∈
              decodeRepeat b32BlockElem b32BlockConsumesByte (m₁ + m₂) (Codec.concat blkBytes tailBytes) :=
            decodeRepeat_prefix_concat b32BlockElem b32BlockConsumesByte blocks blkBytes tailBytes hblkmem
          have hflat : blocks.flatten ++ tail = bs := by
            dsimp [blocks, tail]
            rw [b32Split_ofBytes_shape (b32OfBytes bs), b32BytesOf_ofBytes bs]
          rw [List.mem_filterMap]
          refine ⟨(blocks, Suffix.drop m₁ (Codec.concat blkBytes tailBytes)), hblkpre, ?_⟩
          by_cases hne : tail = []
          · -- empty tail: `tail = []`
            rw [hne] at het
            have ht : decodeFull b32TailElem b32TailConsumesByte
                (Suffix.drop m₁ (Codec.concat blkBytes tailBytes)).remaining
                (Suffix.drop m₁ (Codec.concat blkBytes tailBytes)).bytes = some [] :=
              decodeFull_b32Tail_suffix_nil (sb := blkBytes) (st := tailBytes) het
            simp [ht]
            rw [hne] at hflat
            simpa using hflat
          · -- non-empty tail
            have ht : decodeFull b32TailElem b32TailConsumesByte
                (Suffix.drop m₁ (Codec.concat blkBytes tailBytes)).remaining
                (Suffix.drop m₁ (Codec.concat blkBytes tailBytes)).bytes = some [tail] :=
              decodeFull_b32Tail_suffix_cons tail (sb := blkBytes) (st := tailBytes) het hne
            simp [ht]
            rw [hflat]

/-- The whole-input roundtrip: `decodeFullB32 (encodeB32 bs) = some bs`. -/
theorem decodeFullB32_roundtrip (bs : List UInt8) {n : Nat} {s : Bytes n}
    (he : encodeB32 bs = some ⟨n, s⟩) :
    decodeFullB32 s = some bs := by
  unfold decodeFullB32
  apply head?_eq_some_of_mem_eq bs
  · exact decodeFullB32_mem_encode bs he
  · intro x hx
    rw [List.mem_filterMap] at hx
    rcases hx with ⟨pr, hmem, hfx⟩
    rcases pr with ⟨blocks', t'⟩
    cases htaildec : decodeFull b32TailElem b32TailConsumesByte t'.remaining t'.bytes with
    | none =>
        simp [htaildec] at hfx
    | some tail' =>
        let blocks := (b32Split_ofBytes (b32OfBytes bs)).1
        let tail := (b32Split_ofBytes (b32OfBytes bs)).2
        cases heb : encodeRepeat b32BlockElem blocks with
        | none =>
            unfold encodeB32 encodeB32' at he
            simp [blocks, heb] at he
        | some b =>
            cases het : encodeB32Tail tail with
            | none =>
                unfold encodeB32 encodeB32' at he
                simp [blocks, tail, heb, het] at he
            | some t =>
                rcases b with ⟨m₁, blkBytes⟩
                rcases t with ⟨m₂, tailBytes⟩
                have hpair : (⟨m₁ + m₂, Codec.concat blkBytes tailBytes⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by
                  have he' : some (⟨m₁ + m₂, Codec.concat blkBytes tailBytes⟩ : Sigma fun k => Bytes k) = some ⟨n, s⟩ := by
                    unfold encodeB32 encodeB32' at he
                    simpa [blocks, tail, heb, het] using he
                  exact Option.some.inj he'
                cases hpair
                have hflat : blocks.flatten ++ tail = bs := by
                  dsimp [blocks, tail]
                  rw [b32Split_ofBytes_shape (b32OfBytes bs), b32BytesOf_ofBytes bs]
                rcases (decodeRepeat_spec b32BlockElem b32BlockConsumesByte blocks'
                    (m₁ + m₂) (Codec.concat blkBytes tailBytes) t').1 hmem with ⟨s₀, hs, hblocks'⟩
                have htailmem : (tail', Suffix.empty t'.remaining) ∈
                    decodeRepeat b32TailElem b32TailConsumesByte t'.remaining t'.bytes :=
                  decodeFull_some b32TailElem b32TailConsumesByte t'.bytes tail' htaildec
                rcases (decodeRepeat_spec b32TailElem b32TailConsumesByte tail'
                    t'.remaining t'.bytes (Suffix.empty t'.remaining)).1 htailmem with ⟨s₀t, htbs, htail⟩
                have htailn : relRepeat (Rel b32TailElem) tail' t'.remaining t'.bytes := by
                  have hs₀t : cast (congrArg Bytes (Nat.sub_zero t'.remaining)) s₀t = t'.bytes := by
                    rw [prepend_empty s₀t] at htbs
                    exact htbs.symm
                  have htailcast : relRepeat (Rel b32TailElem) tail' t'.remaining
                      (cast (congrArg Bytes (Nat.sub_zero t'.remaining)) s₀t) :=
                    (relRepeat_cast (Rel b32TailElem) tail' (Nat.sub_zero t'.remaining) s₀t).2 htail
                  rw [hs₀t] at htailcast
                  exact htailcast
                have henc : relRepeat (Rel b32BlockElem) blocks m₁ blkBytes :=
                  encodeRepeat_rel b32BlockElem blocks heb
                have hm₂ : m₂ = 0 ∨ m₂ = 8 := encodeB32Tail_len tail het
                have htail_ne_of_m₂ : m₂ ≠ 0 → tail ≠ [] := by
                  intro hm₂ne htnil
                  rw [htnil] at het
                  have hge := Option.some.inj het
                  have hm₂zero : m₂ = 0 := (congrArg Sigma.fst hge).symm
                  exact hm₂ne hm₂zero
                have hpad : m₂ ≠ 0 → ∃ i : Fin m₂, (tailBytes i).toNat = 61 := by
                  intro hm₂ne
                  exact encodeB32Tail_has_pad tail (htail_ne_of_m₂ hm₂ne) het
                have hbnd : t'.remaining = m₂ :=
                  b32_boundary_pin blkBytes tailBytes blocks blocks' tail' t' s₀ henc hblocks' htailn
                    hs.symm hm₂ hpad
                have hblocks_eq : blocks' = blocks :=
                  b32_block_run_of_boundary blkBytes tailBytes blocks blocks' t' s₀ henc hblocks'
                    hs.symm hbnd
                have hx : x = blocks'.flatten ++ tail'.flatten := by
                  simp [htaildec] at hfx
                  exact hfx.2.symm
                rw [hblocks_eq] at hx
                have htailflat : tail'.flatten = tail := by
                  have hbytescast : cast (congrArg Bytes hbnd) t'.bytes = tailBytes := by
                    apply Bytes.ext
                    intro i
                    rw [cast_bytes_val' (e := hbnd)]
                    have hread := prepend_suffix_read blkBytes tailBytes t' s₀ hs.symm
                        ⟨i.val, Nat.lt_of_lt_of_eq i.isLt hbnd.symm⟩
                    rw [hread]
                    have hk : m₁ + m₂ - t'.remaining = m₁ := by rw [hbnd]; omega
                    simpa [hk, Nat.add_comm, Nat.add_left_comm] using (concat_tail_read blkBytes tailBytes i)
                  have htaildec' : decodeFull b32TailElem b32TailConsumesByte m₂
                      (cast (congrArg Bytes hbnd) t'.bytes) = some tail' := by
                    have hc := decodeFull_cast b32TailElem b32TailConsumesByte hbnd t'.bytes
                    rw [← hc] at htaildec
                    exact htaildec
                  have htaildec'' : decodeFull b32TailElem b32TailConsumesByte m₂ tailBytes = some tail' := by
                    rw [hbytescast] at htaildec'
                    exact htaildec'
                  cases htailc : tail with
                  | nil =>
                      have het' : encodeB32Tail [] = some ⟨m₂, tailBytes⟩ := by
                        simpa [htailc] using het
                      have htail_enc' : decodeFull b32TailElem b32TailConsumesByte m₂ tailBytes = some [] := by
                        simpa using (decodeFull_b32Tail_of_encode [] het')
                      have htail' : tail' = [] := (Option.some.inj (htail_enc'.symm.trans htaildec'')).symm
                      rw [htail']
                      rfl
                  | cons b rest =>
                      have het' : encodeB32Tail (b :: rest) = some ⟨m₂, tailBytes⟩ := by
                        simpa [htailc] using het
                      have htail_enc' : decodeFull b32TailElem b32TailConsumesByte m₂ tailBytes = some [b :: rest] := by
                        simpa using (decodeFull_b32Tail_of_encode (b :: rest) het')
                      have htail' : tail' = [b :: rest] := (Option.some.inj (htail_enc'.symm.trans htaildec'')).symm
                      rw [htail']
                      simp
                rw [hx, htailflat]
                exact hflat

/-! ## Rejection family (task 3.2)

The RFC 4648 §6 malformed-input rejection vectors, re-expressed over the
uniform `decodeFullB32`.  Each is `decodeFullB32 s = none`, proved as an
inequation over the block-run + terminal-tail composition. -/

/-- `nat_lt_eight k hk` — a `Fin 8` index is one of `0..7`. -/
private theorem nat_lt_eight (k : Nat) (hk : k < 8) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by
  omega

/-- A successful `decodeFullB32 s = some v` decomposes into a full-block run
prefix `blocks` and a terminal tail `tails` that decode, with `v` their flatten.
This is the contrapositive bridge: to show `= none`, assume `= some v`, reach a
length/\alphabet contradiction from this decomposition. -/
theorem decodeFullB32_some {n : Nat} (s : Bytes n) (v : List UInt8)
    (h : decodeFullB32 s = some v) :
    ∃ (blocks : List (List UInt8)) (t : Suffix n) (tails : List (List UInt8)),
      (blocks, t) ∈ decodeRepeat b32BlockElem b32BlockConsumesByte n s ∧
      decodeFull b32TailElem b32TailConsumesByte t.remaining t.bytes = some tails ∧
      tails.length ≤ 1 ∧
      blocks.flatten ++ tails.flatten = v := by
  unfold decodeFullB32 at h
  have hmem : v ∈ (decodeRepeat b32BlockElem b32BlockConsumesByte n s).filterMap
      (fun ⟨blocks, t⟩ =>
        match decodeFull b32TailElem b32TailConsumesByte t.remaining t.bytes with
        | some tail => if tail.length ≤ 1 then some (blocks.flatten ++ tail.flatten) else none
        | none => none) := by
    rcases List.head?_eq_some_iff.mp h with ⟨ys, hys⟩
    rw [hys]
    simp
  rw [List.mem_filterMap] at hmem
  rcases hmem with ⟨pr, hmemp, hfx⟩
  rcases pr with ⟨blocks, t⟩
  cases hd : decodeFull b32TailElem b32TailConsumesByte t.remaining t.bytes with
  | none => simp [hd] at hfx
  | some tail =>
      have hlen : tail.length ≤ 1 := by
        by_cases hlen : tail.length ≤ 1
        · exact hlen
        · simp [hd, hlen] at hfx
      refine ⟨blocks, t, tail, hmemp, hd, hlen, ?_⟩
      simpa [hd, hlen] using hfx

/-- The `MY======AAAAAAAA` byte vector (the flagship rejection input). -/
def myAAAA : Bytes 16 := fun i : Fin 16 =>
  [0x4D, 0x59, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41][i]

/-- Rejection: trailing data after a terminal `=` (`MY======AAAAAAAA`) is `none`.  The
full-block run cannot consume an 8-char block containing `=` (its element is
alphabet-only), so it consumes nothing; the terminal tail must then consume the
whole input as two 8-char blocks, whose second block (`AAAAAAAA`) has no `=` pad —
but a tail block always contains `=` (`Rel_b32TailElem_has_pad`).  Contradiction. -/
theorem decodeFullB32_reject_MYAAAA :
    decodeFullB32 myAAAA = none := by
  let s₀ : Bytes 16 := myAAAA
  change decodeFullB32 s₀ = none
  cases h : decodeFullB32 s₀ with
  | none => rfl
  | some v =>
      rcases decodeFullB32_some s₀ v h with ⟨blocks, t, tails, hmem, htail, _, _⟩
      rcases (decodeRepeat_spec b32BlockElem b32BlockConsumesByte blocks 16 s₀ t).1 hmem with ⟨s₁, hs, hrel⟩
      have hcanon : ∀ i : Fin (16 - t.remaining), b32Char (s₁ i) = true :=
        relRepeat_forall b32Char (fun x {m} tt ht => Rel_b32BlockElem_canonical (t := tt) ht) blocks (16 - t.remaining) s₁ hrel
      -- s₀ 2 = 61: a block prefix reaching index 2 would read that pad as an alphabet byte
      have hblock_stop : ¬ (2 < 16 - t.remaining) := by
        intro hi2
        have hs₁2 : s₁ ⟨2, hi2⟩ = s₀ ⟨2, by decide⟩ := by
          rw [hs]
          exact (Codec.prepend_prefix_read t s₁ ⟨2, by decide⟩ hi2).symm
        have hs₁2pad : (s₁ ⟨2, hi2⟩).toNat = 61 := by
          rw [hs₁2]
          rfl
        have hch := hcanon ⟨2, hi2⟩
        unfold b32Char at hch
        rw [hs₁2pad] at hch
        have hfalse : b32Valid 61 = false := by rfl
        rw [hfalse] at hch
        exact Bool.false_ne_true hch
      -- the block run is empty or consumes an 8-char block; both contradict s₀ 2 = 61
      cases blocks with
      | cons b bs =>
          rw [relRepeat_cons] at hrel
          rcases hrel with ⟨m, hm, sb, srest, hsplice, hb, _⟩
          have hm8 : m = 8 := Rel_b32BlockElem_len b sb hb
          have h8le : 8 ≤ 16 - t.remaining := by
            simpa [hm8] using hm
          have hle2 : 16 - t.remaining ≤ 2 := Nat.le_of_not_gt hblock_stop
          have h82 : 8 ≤ 2 := Nat.le_trans h8le hle2
          exact False.elim ((by omega : ¬ (8 : Nat) ≤ 2) h82)
      | nil =>
          rw [relRepeat_nil] at hrel
          have hrem16 : t.remaining = 16 := by
            have hz : 16 - t.remaining = 0 := hrel
            have htle : t.remaining ≤ 16 := t.hle
            have hle16 : 16 ≤ t.remaining := by
              exact (Nat.sub_eq_zero_iff_le.mp hz)
            exact Nat.le_antisymm htle hle16
          have htail_mem : (tails, Suffix.empty t.remaining) ∈ decodeRepeat b32TailElem b32TailConsumesByte t.remaining t.bytes :=
            decodeFull_some b32TailElem b32TailConsumesByte t.bytes tails htail
          rcases (decodeRepeat_spec b32TailElem b32TailConsumesByte tails t.remaining t.bytes (Suffix.empty t.remaining)).1 htail_mem with ⟨s₂, hs₂, htailrel⟩
          have htailrel' : relRepeat (Rel b32TailElem) tails t.remaining t.bytes := by
            have hne : t.bytes = cast (congrArg Bytes (Nat.sub_zero t.remaining)) s₂ := by
              rw [hs₂]
              exact prepend_empty_eq s₂
            rw [hne]
            exact (relRepeat_cast (Rel b32TailElem) tails (Nat.sub_zero t.remaining) s₂).1 htailrel
          have ht_sid : t = Suffix.id 16 s₀ :=
            decodeRepeat_nil_mem_eq_id b32BlockElem b32BlockConsumesByte s₀ t hmem
          subst t
          dsimp [Suffix.id] at htailrel'
          cases tails with
          | nil =>
              rw [relRepeat_nil] at htailrel'
              exact False.elim ((by omega : ¬ (16 : Nat) = 0) htailrel')
          | cons x xs =>
              rw [relRepeat_cons] at htailrel'
              rcases htailrel' with ⟨m₁, hm₁, sb₁, srest, hsplice1, hx, hrest⟩
              have hm₁8 : m₁ = 8 := Rel_b32TailElem_len x sb₁ hx
              subst m₁
              cases xs with
              | nil =>
                  rw [relRepeat_nil] at hrest
                  exact False.elim ((by omega : ¬ (8 : Nat) = 0) hrest)
              | cons y ys =>
                  rw [relRepeat_cons] at hrest
                  rcases hrest with ⟨m₂, hm₂, sb₂, srest2, hsplice2, hy, _⟩
                  have hm₂8 : m₂ = 8 := Rel_b32TailElem_len y sb₂ hy
                  subst m₂
                  have hpad₂ : ∃ i : Fin 8, (sb₂ i).toNat = 61 := Rel_b32TailElem_has_pad y sb₂ hy
                  have hall : ∀ i : Fin 8, (sb₂ i).toNat = 65 := by
                    intro i
                    dsimp [Suffix.id] at hsplice1 hsplice2 hm₁ hm₂
                    have hb8 : bdrop 8 s₀ = srest := by
                      rw [hsplice1]
                      exact bdrop_splice hm₁ sb₁ srest
                    have hb8' : bdrop 8 s₀ = splice hm₂ sb₂ srest2 := by
                      rw [hb8, hsplice2]
                    have hsbread : sb₂ i = (bdrop 8 s₀) ⟨i.val, show i.val < 8 by exact i.isLt⟩ := by
                      rw [hb8']
                      exact (Codec.splice_prefix_read hm₂ sb₂ srest2 ⟨i.val, show i.val < 8 by exact i.isLt⟩ i.isLt).symm
                    rw [hsbread]
                    dsimp [bdrop]
                    rcases i with ⟨k, hk⟩
                    rcases nat_lt_eight k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
                  rcases hpad₂ with ⟨i, hpad⟩
                  exact False.elim (by
                    have h65 : (sb₂ i).toNat = 65 := hall i
                    have hbot : (61 : Nat) = 65 := hpad.symm.trans h65
                    have hbad : (61 : Nat) ≠ 65 := by intro h; cases h
                    exact hbad hbot)

/-- A `b32TailElem`-related string's first byte is a valid alphabet character
(never `=` and never invalid).  `b32BlockApply` (hence `b32TailApply`) recovers the
tail value via `b32BlockUnapply`, whose first char is `valToB32 (v0 / 8)` — a valid,
non-pad alphabet byte (`valToB32_valid`).  With `a = List.ofFn s` that pins
`s ⟨0, ·⟩`. -/
theorem Rel_b32TailElem_first_char (x : List UInt8) {n : Nat} (s : Bytes n)
    (h : Rel b32TailElem x s) :
    b32Valid (s ⟨0, by
      have hn8 : n = 8 := Rel_b32TailElem_len x s h
      omega⟩).toNat = true := by
  unfold b32TailElem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, ha, hr⟩
  have hofn : List.ofFn s = a := Rel_count_satisfy_ofFn b32OrPad 8 a s hr
  have hn8 : n = 8 := Rel_count_satisfy_len b32OrPad 8 a s hr
  subst n
  unfold b32TailIso at ha
  change b32TailApply a = some x at ha
  unfold b32TailApply at ha
  cases hb : b32BlockApply a with
  | none => simp [hb] at ha
  | some bl =>
    cases bl with
    | nil => simp [hb] at ha
    | cons b0 bl1 =>
      cases bl1 with
      | nil =>
        have hun : b32BlockUnapply [b0] = some a := (b32BlockIso_law a [b0]).1 (by simpa using hb)
        have htail : a = [toByte (valToB32 (b0.toNat / 8)), toByte (valToB32 ((b0.toNat % 8) * 4)), toByte 61, toByte 61, toByte 61, toByte 61, toByte 61, toByte 61] := by
          simp [b32BlockUnapply] at hun
          exact hun.symm
        rw [← hofn] at htail
        have hc0 : s ⟨0, by decide⟩ = toByte (valToB32 (b0.toNat / 8)) := by
          have hsucc : List.ofFn s = s ⟨0, by decide⟩ :: List.ofFn (fun i : Fin 7 => s i.succ) := List.ofFn_succ
          have hcons : s ⟨0, by decide⟩ :: List.ofFn (fun i : Fin 7 => s i.succ) = [toByte (valToB32 (b0.toNat / 8)), toByte (valToB32 ((b0.toNat % 8) * 4)), toByte 61, toByte 61, toByte 61, toByte 61, toByte 61, toByte 61] := by
            rw [← hsucc, htail]
          have hhead := congrArg (fun l : List UInt8 => l.head!) hcons
          simp [List.head!] at hhead
          exact hhead
        have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
        have hc0v : b32Valid (valToB32 (b0.toNat / 8)) = true :=
          valToB32_valid (b0.toNat / 8) (by omega)
        rw [hc0, toByte_valToB32 (b0.toNat / 8) (by omega)]
        exact hc0v
      | cons b1 bl2 =>
        cases bl2 with
        | nil =>
          have hun : b32BlockUnapply [b0, b1] = some a := (b32BlockIso_law a [b0, b1]).1 (by simpa using hb)
          have htail : a = [toByte (valToB32 (b0.toNat / 8)), toByte (valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)), toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16)), toByte 61, toByte 61, toByte 61, toByte 61] := by
            simp [b32BlockUnapply] at hun
            exact hun.symm
          rw [← hofn] at htail
          have hc0 : s ⟨0, by decide⟩ = toByte (valToB32 (b0.toNat / 8)) := by
            have hsucc : List.ofFn s = s ⟨0, by decide⟩ :: List.ofFn (fun i : Fin 7 => s i.succ) := List.ofFn_succ
            have hcons : s ⟨0, by decide⟩ :: List.ofFn (fun i : Fin 7 => s i.succ) = [toByte (valToB32 (b0.toNat / 8)), toByte (valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)), toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16)), toByte 61, toByte 61, toByte 61, toByte 61] := by
              rw [← hsucc, htail]
            have hhead := congrArg (fun l : List UInt8 => l.head!) hcons
            simp [List.head!] at hhead
            exact hhead
          have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
          have hc0v : b32Valid (valToB32 (b0.toNat / 8)) = true :=
            valToB32_valid (b0.toNat / 8) (by omega)
          rw [hc0, toByte_valToB32 (b0.toNat / 8) (by omega)]
          exact hc0v
        | cons b2 bl3 =>
          cases bl3 with
          | nil =>
            have hun : b32BlockUnapply [b0, b1, b2] = some a := (b32BlockIso_law a [b0, b1, b2]).1 (by simpa using hb)
            have htail : a = [toByte (valToB32 (b0.toNat / 8)), toByte (valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)), toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)), toByte (valToB32 ((b2.toNat % 16) * 2)), toByte 61, toByte 61, toByte 61] := by
              simp [b32BlockUnapply] at hun
              exact hun.symm
            rw [← hofn] at htail
            have hc0 : s ⟨0, by decide⟩ = toByte (valToB32 (b0.toNat / 8)) := by
              have hsucc : List.ofFn s = s ⟨0, by decide⟩ :: List.ofFn (fun i : Fin 7 => s i.succ) := List.ofFn_succ
              have hcons : s ⟨0, by decide⟩ :: List.ofFn (fun i : Fin 7 => s i.succ) = [toByte (valToB32 (b0.toNat / 8)), toByte (valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)), toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)), toByte (valToB32 ((b2.toNat % 16) * 2)), toByte 61, toByte 61, toByte 61] := by
                rw [← hsucc, htail]
              have hhead := congrArg (fun l : List UInt8 => l.head!) hcons
              simp [List.head!] at hhead
              exact hhead
            have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
            have hc0v : b32Valid (valToB32 (b0.toNat / 8)) = true :=
              valToB32_valid (b0.toNat / 8) (by omega)
            rw [hc0, toByte_valToB32 (b0.toNat / 8) (by omega)]
            exact hc0v
          | cons b3 bl4 =>
            cases bl4 with
            | nil =>
              have hun : b32BlockUnapply [b0, b1, b2, b3] = some a := (b32BlockIso_law a [b0, b1, b2, b3]).1 (by simpa using hb)
              have htail : a = [toByte (valToB32 (b0.toNat / 8)), toByte (valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)), toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)), toByte (valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128)), toByte (valToB32 ((b3.toNat / 4) % 32)), toByte (valToB32 ((b3.toNat % 4) * 8)), toByte 61] := by
                simp [b32BlockUnapply] at hun
                exact hun.symm
              rw [← hofn] at htail
              have hc0 : s ⟨0, by decide⟩ = toByte (valToB32 (b0.toNat / 8)) := by
                have hsucc : List.ofFn s = s ⟨0, by decide⟩ :: List.ofFn (fun i : Fin 7 => s i.succ) := List.ofFn_succ
                have hcons : s ⟨0, by decide⟩ :: List.ofFn (fun i : Fin 7 => s i.succ) = [toByte (valToB32 (b0.toNat / 8)), toByte (valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)), toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)), toByte (valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128)), toByte (valToB32 ((b3.toNat / 4) % 32)), toByte (valToB32 ((b3.toNat % 4) * 8)), toByte 61] := by
                  rw [← hsucc, htail]
                have hhead := congrArg (fun l : List UInt8 => l.head!) hcons
                simp [List.head!] at hhead
                exact hhead
              have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
              have hc0v : b32Valid (valToB32 (b0.toNat / 8)) = true :=
                valToB32_valid (b0.toNat / 8) (by omega)
              rw [hc0, toByte_valToB32 (b0.toNat / 8) (by omega)]
              exact hc0v
            | cons _ _ => simp [hb] at ha

theorem decodeFullB32_reject_first_invalid (s : Bytes 8)
    (hbad : b32Valid (s ⟨0, by decide⟩).toNat = false) :
    decodeFullB32 s = none := by
  cases h : decodeFullB32 s with
  | none => rfl
  | some v =>
      rcases decodeFullB32_some s v h with ⟨blocks, t, tails, hmem, htail, _, _⟩
      rcases (decodeRepeat_spec b32BlockElem b32BlockConsumesByte blocks 8 s t).1 hmem with ⟨s₁, hs, hrel⟩
      have hcanon : ∀ i : Fin (8 - t.remaining), b32Char (s₁ i) = true :=
        relRepeat_forall b32Char (fun x {m} tt ht => Rel_b32BlockElem_canonical ht) blocks (8 - t.remaining) s₁ hrel
      cases blocks with
      | cons b bs =>
          rw [relRepeat_cons] at hrel
          rcases hrel with ⟨m, hm, sb, srest, hsplice, hb, _⟩
          have hm8 : m = 8 := Rel_b32BlockElem_len b sb hb
          subst m
          have hfirst : b32Valid (s ⟨0, by decide⟩).toNat = true := by
            have hge : 0 < 8 - t.remaining := by omega
            have hsread : s ⟨0, by decide⟩ = s₁ ⟨0, hge⟩ := by
              rw [hs]
              exact (Codec.prepend_prefix_read t s₁ ⟨0, by decide⟩ hge)
            have hc : b32Char (s₁ ⟨0, hge⟩) = true := hcanon ⟨0, hge⟩
            rw [hsread]
            exact hc
          have hfalse : b32Valid (s ⟨0, by decide⟩).toNat = false := hbad
          rw [hfirst] at hfalse
          exact False.elim (Bool.false_ne_true hfalse.symm)
      | nil =>
          have ht : t = Suffix.id 8 s := decodeRepeat_nil_mem_eq_id b32BlockElem b32BlockConsumesByte s t hmem
          subst t
          have htail_mem : (tails, Suffix.empty 8) ∈ decodeRepeat b32TailElem b32TailConsumesByte 8 s := by
            simpa using (decodeFull_some b32TailElem b32TailConsumesByte s tails htail)
          rcases (decodeRepeat_spec b32TailElem b32TailConsumesByte tails 8 s (Suffix.empty 8)).1 htail_mem with ⟨s₂, hs₂, htailrel⟩
          have htailrel' : relRepeat (Rel b32TailElem) tails 8 s := by
            have hne : s = cast (congrArg Bytes (Nat.sub_zero 8)) s₂ := by
              rw [hs₂]
              exact prepend_empty_eq s₂
            rw [hne]
            exact (relRepeat_cast (Rel b32TailElem) tails (Nat.sub_zero 8) s₂).1 htailrel
          cases tails with
          | nil => rw [relRepeat_nil] at htailrel'; omega
          | cons x xs =>
              rw [relRepeat_cons] at htailrel'
              rcases htailrel' with ⟨m, hm, sb, srest, hsplice, hx, _⟩
              have hm8 : m = 8 := Rel_b32TailElem_len x sb hx
              subst m
              have hfirst : b32Valid (s ⟨0, by decide⟩).toNat = true := by
                have hf_sb : b32Valid (sb ⟨0, by decide⟩).toNat = true :=
                  Rel_b32TailElem_first_char x sb hx
                have hsread : s ⟨0, by decide⟩ = sb ⟨0, by decide⟩ := by
                  rw [hsplice]
                  exact (Codec.splice_prefix_read hm sb srest ⟨0, by decide⟩ (by decide)).symm
                rw [hsread]
                exact hf_sb
              have hfalse : b32Valid (s ⟨0, by decide⟩).toNat = false := hbad
              rw [hfirst] at hfalse
              exact False.elim (Bool.false_ne_true hfalse.symm)

/-- Invalid base32 character `!` (0x21) is rejected. -/
def bangAAAAA : Bytes 8 := fun i => [0x21, 0x59, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D][i]

/-- `=` in the first position (illegal padding) is rejected. -/
def eqYEqEq : Bytes 8 := fun i => [0x3D, 0x59, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D, 0x3D][i]

/-- Two-char input (wrong arity) is rejected. -/
def myTwo : Bytes 2 := fun i => [0x4D, 0x59][i]

theorem decodeFullB32_reject_invalid_char : decodeFullB32 bangAAAAA = none := by
  exact decodeFullB32_reject_first_invalid bangAAAAA (by decide)

theorem decodeFullB32_reject_pad_first : decodeFullB32 eqYEqEq = none := by
  exact decodeFullB32_reject_first_invalid eqYEqEq (by decide)

/-- Wrong-arity input `MY` (2 base32 chars) is rejected: neither an 8-char block
nor an 8-char padded tail can be formed from 2 bytes. -/
theorem decodeFullB32_reject_bad_length : decodeFullB32 myTwo = none := by
  cases h : decodeFullB32 myTwo with
  | none => rfl
  | some v =>
      rcases decodeFullB32_some myTwo v h with ⟨blocks, t, tails, hmem, htail, _, _⟩
      rcases (decodeRepeat_spec b32BlockElem b32BlockConsumesByte blocks 2 myTwo t).1 hmem with ⟨s₁, hs, hrel⟩
      cases blocks with
      | nil =>
          have ht : t = Suffix.id 2 myTwo := decodeRepeat_nil_mem_eq_id b32BlockElem b32BlockConsumesByte myTwo t hmem
          subst t
          have htail_mem : (tails, Suffix.empty 2) ∈ decodeRepeat b32TailElem b32TailConsumesByte 2 myTwo := by
            simpa using (decodeFull_some b32TailElem b32TailConsumesByte myTwo tails htail)
          rcases (decodeRepeat_spec b32TailElem b32TailConsumesByte tails 2 myTwo (Suffix.empty 2)).1 htail_mem with ⟨s₂, hs₂, htailrel⟩
          have htailrel' : relRepeat (Rel b32TailElem) tails 2 myTwo := by
            have hne : myTwo = cast (congrArg Bytes (Nat.sub_zero 2)) s₂ := by
              rw [hs₂]
              exact prepend_empty_eq s₂
            rw [hne]
            exact (relRepeat_cast (Rel b32TailElem) tails (Nat.sub_zero 2) s₂).1 htailrel
          cases tails with
          | nil => rw [relRepeat_nil] at htailrel'; omega
          | cons x xs =>
              rw [relRepeat_cons] at htailrel'
              rcases htailrel' with ⟨m, hm, sb, srest, hsplice, hx, _⟩
              have hm8 : m = 8 := Rel_b32TailElem_len x sb hx
              subst m
              omega
      | cons b bs =>
          rw [relRepeat_cons] at hrel
          rcases hrel with ⟨m, hm, sb, srest, hsplice, hb, _⟩
          have hm8 : m = 8 := Rel_b32BlockElem_len b sb hb
          subst m
          omega

/-! ## Conformance: canonical encoding (task 4.2, base32)

The whole-input `encodeB32` output is canonical: alphabet-only full blocks
followed by a single RFC-arity padded tail (base32 1/2/3/4-byte tails → 6/4/3/1
`=` pads).  Stated as a decomposition over `List.ofFn`; `[propext,
Quot.sound]`-only. -/

/-- `b32TailApply a = some ys` forces `b32BlockApply a = some ys` (the tail
apply is the block apply restricted to 1–4-byte results).  Proved by fully
casing the block result length. -/
private theorem b32TailApply_block {a ys : List UInt8}
    (h : b32TailApply a = some ys) : b32BlockApply a = some ys := by
  cases hb : b32BlockApply a with
  | none => simp [b32TailApply, hb] at h
  | some bl =>
    cases bl with
    | nil => simp [b32TailApply, hb] at h
    | cons x bl1 =>
    cases bl1 with
    | nil => simpa [b32TailApply, hb] using h
    | cons y bl2 =>
    cases bl2 with
    | nil => simpa [b32TailApply, hb] using h
    | cons z bl3 =>
    cases bl3 with
    | nil => simpa [b32TailApply, hb] using h
    | cons w bl4 =>
    cases bl4 with
    | nil => simpa [b32TailApply, hb] using h
    | cons _ _ => simp [b32TailApply, hb] at h

/-- A tail encoding is either empty (length 0) or a single 8-byte padded block
whose pad bytes are exactly the RFC tail (1→6, 2→4, 3→3, 4→1). -/
theorem b32TailBlock_canonical (tail : List UInt8) {m : Nat} {t : Bytes m}
    (he : encodeB32Tail tail = some ⟨m, t⟩) :
    (tail = [] ∧ m = 0) ∨
    (∃ b, tail = [b] ∧ m = 8 ∧ ∃ c0 c1 : UInt8,
      List.ofFn t = [c0, c1, toByte 61, toByte 61, toByte 61, toByte 61, toByte 61, toByte 61] ∧
      b32Valid c0.toNat = true ∧ b32Valid c1.toNat = true) ∨
    (∃ b0 b1, tail = [b0, b1] ∧ m = 8 ∧ ∃ c0 c1 c2 c3 : UInt8,
      List.ofFn t = [c0, c1, c2, c3, toByte 61, toByte 61, toByte 61, toByte 61] ∧
      b32Valid c0.toNat = true ∧ b32Valid c1.toNat = true ∧ b32Valid c2.toNat = true ∧ b32Valid c3.toNat = true) ∨
    (∃ b0 b1 b2, tail = [b0, b1, b2] ∧ m = 8 ∧ ∃ c0 c1 c2 c3 c4 : UInt8,
      List.ofFn t = [c0, c1, c2, c3, c4, toByte 61, toByte 61, toByte 61] ∧
      b32Valid c0.toNat = true ∧ b32Valid c1.toNat = true ∧ b32Valid c2.toNat = true ∧ b32Valid c3.toNat = true ∧ b32Valid c4.toNat = true) ∨
    (∃ b0 b1 b2 b3, tail = [b0, b1, b2, b3] ∧ m = 8 ∧ ∃ c0 c1 c2 c3 c4 c5 c6 : UInt8,
      List.ofFn t = [c0, c1, c2, c3, c4, c5, c6, toByte 61] ∧
      b32Valid c0.toNat = true ∧ b32Valid c1.toNat = true ∧ b32Valid c2.toNat = true ∧ b32Valid c3.toNat = true ∧ b32Valid c4.toNat = true ∧ b32Valid c5.toNat = true ∧ b32Valid c6.toNat = true) := by
  cases tail with
  | nil =>
      have hs : (⟨0, (Codec.emptyBytes : Bytes 0)⟩ : Sigma fun k => Bytes k) = ⟨m, t⟩ := by
        simpa [encodeB32Tail] using he
      cases hs
      left
      simp
  | cons b t1 =>
      cases t1 with
      | nil =>
          have henc : Codec.encode b32TailElem [b] = some ⟨m, t⟩ := by simpa [encodeB32Tail] using he
          have hrel : Rel b32TailElem [b] t := encode_rel b32TailElem [b] henc
          have hm8 : m = 8 := Rel_b32TailElem_len [b] t hrel
          subst m
          right; left
          refine ⟨b, rfl, rfl, ?_⟩
          unfold b32TailElem at hrel
          rw [Rel_iso] at hrel
          rcases hrel with ⟨a, ha, hr⟩
          have hofn : List.ofFn t = a := Rel_count_satisfy_ofFn b32OrPad 8 a t hr
          unfold b32TailIso at ha
          change b32TailApply a = some [b] at ha
          have hblk : b32BlockApply a = some [b] := b32TailApply_block ha
          have hun : b32BlockUnapply [b] = some a := (b32BlockIso_law a [b]).1 hblk
          simp [b32BlockUnapply] at hun
          have ha' : a = [toByte (valToB32 (b.toNat / 8)), toByte (valToB32 ((b.toNat % 8) * 4)), toByte 61, toByte 61, toByte 61, toByte 61, toByte 61, toByte 61] := hun.symm
          have hb : b.toNat < 256 := UInt8.toNat_lt b
          refine ⟨toByte (valToB32 (b.toNat / 8)), toByte (valToB32 ((b.toNat % 8) * 4)), ?_, ?_, ?_⟩
          · rw [hofn]; exact ha'
          · rw [toByte_valToB32 (b.toNat / 8) (by omega)]
            exact valToB32_valid (b.toNat / 8) (by omega)
          · rw [toByte_valToB32 ((b.toNat % 8) * 4) (by omega)]
            exact valToB32_valid ((b.toNat % 8) * 4) (by omega)
      | cons b1 t2 =>
        cases t2 with
        | nil =>
          have henc : Codec.encode b32TailElem [b, b1] = some ⟨m, t⟩ := by simpa [encodeB32Tail] using he
          have hrel : Rel b32TailElem [b, b1] t := encode_rel b32TailElem [b, b1] henc
          have hm8 : m = 8 := Rel_b32TailElem_len [b, b1] t hrel
          subst m
          right; right; left
          refine ⟨b, b1, rfl, rfl, ?_⟩
          unfold b32TailElem at hrel
          rw [Rel_iso] at hrel
          rcases hrel with ⟨a, ha, hr⟩
          have hofn : List.ofFn t = a := Rel_count_satisfy_ofFn b32OrPad 8 a t hr
          unfold b32TailIso at ha
          change b32TailApply a = some [b, b1] at ha
          have hblk : b32BlockApply a = some [b, b1] := b32TailApply_block ha
          have hun : b32BlockUnapply [b, b1] = some a := (b32BlockIso_law a [b, b1]).1 hblk
          simp [b32BlockUnapply] at hun
          have ha' : a = [toByte (valToB32 (b.toNat / 8)), toByte (valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64)), toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16)), toByte 61, toByte 61, toByte 61, toByte 61] := hun.symm
          have hb : b.toNat < 256 := UInt8.toNat_lt b
          have hb1 : b1.toNat < 256 := UInt8.toNat_lt b1
          refine ⟨toByte (valToB32 (b.toNat / 8)), toByte (valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64)), toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16)), ?_, ?_, ?_, ?_, ?_⟩
          · rw [hofn]; exact ha'
          · rw [toByte_valToB32 (b.toNat / 8) (by omega)]
            exact valToB32_valid (b.toNat / 8) (by omega)
          · rw [toByte_valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64) (by omega)]
            exact valToB32_valid ((b.toNat % 8) * 4 + b1.toNat / 64) (by omega)
          · rw [toByte_valToB32 ((b1.toNat / 2) % 32) (by omega)]
            exact valToB32_valid ((b1.toNat / 2) % 32) (by omega)
          · rw [toByte_valToB32 ((b1.toNat % 2) * 16) (by omega)]
            exact valToB32_valid ((b1.toNat % 2) * 16) (by omega)
        | cons b2 t3 =>
          cases t3 with
          | nil =>
            have henc : Codec.encode b32TailElem [b, b1, b2] = some ⟨m, t⟩ := by simpa [encodeB32Tail] using he
            have hrel : Rel b32TailElem [b, b1, b2] t := encode_rel b32TailElem [b, b1, b2] henc
            have hm8 : m = 8 := Rel_b32TailElem_len [b, b1, b2] t hrel
            subst m
            right; right; right; left
            refine ⟨b, b1, b2, rfl, rfl, ?_⟩
            unfold b32TailElem at hrel
            rw [Rel_iso] at hrel
            rcases hrel with ⟨a, ha, hr⟩
            have hofn : List.ofFn t = a := Rel_count_satisfy_ofFn b32OrPad 8 a t hr
            unfold b32TailIso at ha
            change b32TailApply a = some [b, b1, b2] at ha
            have hblk : b32BlockApply a = some [b, b1, b2] := b32TailApply_block ha
            have hun : b32BlockUnapply [b, b1, b2] = some a := (b32BlockIso_law a [b, b1, b2]).1 hblk
            simp [b32BlockUnapply] at hun
            have ha' : a = [toByte (valToB32 (b.toNat / 8)), toByte (valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64)), toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)), toByte (valToB32 ((b2.toNat % 16) * 2)), toByte 61, toByte 61, toByte 61] := hun.symm
            have hb : b.toNat < 256 := UInt8.toNat_lt b
            have hb1 : b1.toNat < 256 := UInt8.toNat_lt b1
            have hb2 : b2.toNat < 256 := UInt8.toNat_lt b2
            refine ⟨toByte (valToB32 (b.toNat / 8)), toByte (valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64)), toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)), toByte (valToB32 ((b2.toNat % 16) * 2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hofn]; exact ha'
            · rw [toByte_valToB32 (b.toNat / 8) (by omega)]
              exact valToB32_valid (b.toNat / 8) (by omega)
            · rw [toByte_valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64) (by omega)]
              exact valToB32_valid ((b.toNat % 8) * 4 + b1.toNat / 64) (by omega)
            · rw [toByte_valToB32 ((b1.toNat / 2) % 32) (by omega)]
              exact valToB32_valid ((b1.toNat / 2) % 32) (by omega)
            · rw [toByte_valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) (by omega)]
              exact valToB32_valid ((b1.toNat % 2) * 16 + b2.toNat / 16) (by omega)
            · rw [toByte_valToB32 ((b2.toNat % 16) * 2) (by omega)]
              exact valToB32_valid ((b2.toNat % 16) * 2) (by omega)
          | cons b3 t4 =>
            cases t4 with
            | nil =>
              have henc : Codec.encode b32TailElem [b, b1, b2, b3] = some ⟨m, t⟩ := by simpa [encodeB32Tail] using he
              have hrel : Rel b32TailElem [b, b1, b2, b3] t := encode_rel b32TailElem [b, b1, b2, b3] henc
              have hm8 : m = 8 := Rel_b32TailElem_len [b, b1, b2, b3] t hrel
              subst m
              right; right; right; right
              refine ⟨b, b1, b2, b3, rfl, rfl, ?_⟩
              unfold b32TailElem at hrel
              rw [Rel_iso] at hrel
              rcases hrel with ⟨a, ha, hr⟩
              have hofn : List.ofFn t = a := Rel_count_satisfy_ofFn b32OrPad 8 a t hr
              unfold b32TailIso at ha
              change b32TailApply a = some [b, b1, b2, b3] at ha
              have hblk : b32BlockApply a = some [b, b1, b2, b3] := b32TailApply_block ha
              have hun : b32BlockUnapply [b, b1, b2, b3] = some a := (b32BlockIso_law a [b, b1, b2, b3]).1 hblk
              simp [b32BlockUnapply] at hun
              have ha' : a = [toByte (valToB32 (b.toNat / 8)), toByte (valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64)), toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)), toByte (valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128)), toByte (valToB32 ((b3.toNat / 4) % 32)), toByte (valToB32 ((b3.toNat % 4) * 8)), toByte 61] := hun.symm
              have hb : b.toNat < 256 := UInt8.toNat_lt b
              have hb1 : b1.toNat < 256 := UInt8.toNat_lt b1
              have hb2 : b2.toNat < 256 := UInt8.toNat_lt b2
              have hb3 : b3.toNat < 256 := UInt8.toNat_lt b3
              refine ⟨toByte (valToB32 (b.toNat / 8)), toByte (valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64)), toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)), toByte (valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128)), toByte (valToB32 ((b3.toNat / 4) % 32)), toByte (valToB32 ((b3.toNat % 4) * 8)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hofn]; exact ha'
              · rw [toByte_valToB32 (b.toNat / 8) (by omega)]
                exact valToB32_valid (b.toNat / 8) (by omega)
              · rw [toByte_valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64) (by omega)]
                exact valToB32_valid ((b.toNat % 8) * 4 + b1.toNat / 64) (by omega)
              · rw [toByte_valToB32 ((b1.toNat / 2) % 32) (by omega)]
                exact valToB32_valid ((b1.toNat / 2) % 32) (by omega)
              · rw [toByte_valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) (by omega)]
                exact valToB32_valid ((b1.toNat % 2) * 16 + b2.toNat / 16) (by omega)
              · rw [toByte_valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128) (by omega)]
                exact valToB32_valid ((b2.toNat % 16) * 2 + b3.toNat / 128) (by omega)
              · rw [toByte_valToB32 ((b3.toNat / 4) % 32) (by omega)]
                exact valToB32_valid ((b3.toNat / 4) % 32) (by omega)
              · rw [toByte_valToB32 ((b3.toNat % 4) * 8) (by omega)]
                exact valToB32_valid ((b3.toNat % 4) * 8) (by omega)
            | cons _ _ => simp [encodeB32Tail] at he

/-- The whole-input `encodeB32` output decomposes into alphabet-only full
blocks plus a single RFC-arity padded tail.  `[propext, Quot.sound]`-only. -/
theorem encodeB32_canonical (bs : List UInt8) {n : Nat} {s : Bytes n}
    (he : encodeB32 bs = some ⟨n, s⟩) :
    ∃ (blocks : List (List UInt8)) (m₁ m₂ : Nat) (blkBytes : Bytes m₁) (tailBytes : Bytes m₂),
      encodeRepeat b32BlockElem blocks = some ⟨m₁, blkBytes⟩ ∧
      encodeB32Tail (b32Split_ofBytes (b32OfBytes bs)).2 = some ⟨m₂, tailBytes⟩ ∧
      List.ofFn s = List.ofFn blkBytes ++ List.ofFn tailBytes ∧
      (∀ b : UInt8, b ∈ List.ofFn blkBytes → b32Valid b.toNat = true) ∧
      (List.ofFn tailBytes = [] ∨
        (∃ c0 c1 : UInt8, List.ofFn tailBytes = [c0, c1, toByte 61, toByte 61, toByte 61, toByte 61, toByte 61, toByte 61] ∧ b32Valid c0.toNat = true ∧ b32Valid c1.toNat = true) ∨
        (∃ c0 c1 c2 c3 : UInt8, List.ofFn tailBytes = [c0, c1, c2, c3, toByte 61, toByte 61, toByte 61, toByte 61] ∧ b32Valid c0.toNat = true ∧ b32Valid c1.toNat = true ∧ b32Valid c2.toNat = true ∧ b32Valid c3.toNat = true) ∨
        (∃ c0 c1 c2 c3 c4 : UInt8, List.ofFn tailBytes = [c0, c1, c2, c3, c4, toByte 61, toByte 61, toByte 61] ∧ b32Valid c0.toNat = true ∧ b32Valid c1.toNat = true ∧ b32Valid c2.toNat = true ∧ b32Valid c3.toNat = true ∧ b32Valid c4.toNat = true) ∨
        (∃ c0 c1 c2 c3 c4 c5 c6 : UInt8, List.ofFn tailBytes = [c0, c1, c2, c3, c4, c5, c6, toByte 61] ∧ b32Valid c0.toNat = true ∧ b32Valid c1.toNat = true ∧ b32Valid c2.toNat = true ∧ b32Valid c3.toNat = true ∧ b32Valid c4.toNat = true ∧ b32Valid c5.toNat = true ∧ b32Valid c6.toNat = true)) := by
  let blocks := (b32Split_ofBytes (b32OfBytes bs)).1
  let tail := (b32Split_ofBytes (b32OfBytes bs)).2
  cases heb : encodeRepeat b32BlockElem blocks with
  | none => unfold encodeB32 encodeB32' at he; simp [blocks, heb] at he
  | some b =>
      cases het : encodeB32Tail tail with
      | none => unfold encodeB32 encodeB32' at he; simp [blocks, tail, heb, het] at he
      | some t =>
          rcases b with ⟨m₁, blkBytes⟩
          rcases t with ⟨m₂, tailBytes⟩
          have hpair : (⟨m₁ + m₂, Codec.concat blkBytes tailBytes⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by
            have he' : some (⟨m₁ + m₂, Codec.concat blkBytes tailBytes⟩ : Sigma fun k => Bytes k) = some ⟨n, s⟩ := by
              unfold encodeB32 encodeB32' at he
              simpa [blocks, tail, heb, het] using he
            exact Option.some.inj he'
          cases hpair
          refine ⟨blocks, m₁, m₂, blkBytes, tailBytes, ?_, ?_, ?_, ?_, ?_⟩
          · simpa using heb
          · rfl
          · exact Codec.ofFn_concat blkBytes tailBytes
          · intro b hb
            rcases List.mem_iff_getElem.mp hb with ⟨i, hi, hi'⟩
            have hchar : b32Char (blkBytes ⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩) = true :=
              encodeB32Block_nopad blocks (by simpa using heb) ⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩
            unfold b32Char at hchar
            have hb_eq : b = blkBytes ⟨i, Nat.lt_of_lt_of_eq hi List.length_ofFn⟩ := by
              exact ((List.getElem_ofFn hi).symm.trans hi').symm
            rw [hb_eq]
            exact hchar
          · rcases b32TailBlock_canonical tail (by simpa using het) with h0 | h1 | h2 | h3 | h4
            · left
              rcases h0 with ⟨_, hm0⟩
              subst m₂
              subst tail
              simp
            · right; left
              rcases h1 with ⟨b0, hb0, hm8, c0, c1, hofn, hc0, hc1⟩
              subst m₂
              refine ⟨c0, c1, ?_, ?_, ?_⟩
              · simpa [tail] using hofn
              · exact hc0
              · exact hc1
            · right; right; left
              rcases h2 with ⟨b0, b1, hb0, hm8, c0, c1, c2, c3, hofn, hc0, hc1, hc2, hc3⟩
              subst m₂
              refine ⟨c0, c1, c2, c3, ?_, ?_, ?_, ?_, ?_⟩
              · simpa [tail] using hofn
              · exact hc0
              · exact hc1
              · exact hc2
              · exact hc3
            · right; right; right; left
              rcases h3 with ⟨b0, b1, b2, hb0, hm8, c0, c1, c2, c3, c4, hofn, hc0, hc1, hc2, hc3, hc4⟩
              subst m₂
              refine ⟨c0, c1, c2, c3, c4, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simpa [tail] using hofn
              · exact hc0
              · exact hc1
              · exact hc2
              · exact hc3
              · exact hc4
            · right; right; right; right
              rcases h4 with ⟨b0, b1, b2, b3, hb0, hm8, c0, c1, c2, c3, c4, c5, c6, hofn, hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
              subst m₂
              refine ⟨c0, c1, c2, c3, c4, c5, c6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simpa [tail] using hofn
              · exact hc0
              · exact hc1
              · exact hc2
              · exact hc3
              · exact hc4
              · exact hc5
              · exact hc6


/-! ## Converse (task 4.3) and injectivity (task 4.4)

`decodeFullB32 s = some v → encodeB32 v = some ⟨n, s⟩` (the decode→encode
converse) and `encodeB32 v = encodeB32 v' = some ⟨n, s⟩ → v = v'`
(injectivity).  The base32 mirror of the base64 pair (5-byte blocks, 1–4-byte
tails).  Both `[propext, Quot.sound]`-only. -/

/-- A `b32BlockElem`-related value is a 5-byte list (`Rel_b32BlockElem_size`);
lifted to a `relRepeat`, every block of a block-run is exactly 5 bytes.  An
instantiation of the generic `Common.relRepeat_block_len`.  (`b32Split_blocks_tail`
below is **not** generic — it is a statement about `b32Split`'s own defining
equations — so it stays here, mirroring base64 with 5-byte blocks and a 4-byte
tail bound instead of 3 and 2.) -/
theorem relB32Block_len5 :
    ∀ {blocks : List (List UInt8)} {m : Nat} (s : Bytes m),
      relRepeat (Rel b32BlockElem) blocks m s → ∀ b ∈ blocks, b.length = 5 := by
  intro blocks m s hrel
  exact relRepeat_block_len (len := 5) (fun x _ sx hx => Rel_b32BlockElem_size x sx hx) blocks s hrel

/-- `b32Split` reconstructs a run of 5-byte blocks plus a ≤ 4-byte tail: given
`blocks` all length-5 and `tail.length ≤ 4`, splitting `blocks.flatten ++ tail`
recovers exactly `(blocks, tail)`. -/
theorem b32Split_blocks_tail (blocks : List (List UInt8)) (tail : List UInt8)
    (hblocks : ∀ b ∈ blocks, b.length = 5) (htail : tail.length ≤ 4) :
    b32Split (blocks.flatten ++ tail) = (blocks, tail) := by
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
                  cases t3 with
                  | nil => rfl
                  | cons d t4 =>
                      cases t4 with
                      | nil => rfl
                      | cons e t5 => simp at htail
  | cons b bs ih =>
      have hb : b.length = 5 := hblocks b (by simp)
      have hbs : ∀ b' ∈ bs, b'.length = 5 := by
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
                  | nil => simp at hb
                  | cons b3 t3 =>
                      cases t3 with
                      | nil => simp at hb
                      | cons b4 t4 =>
                          cases t4 with
                          | nil =>
                              show b32Split (b0 :: b1 :: b2 :: b3 :: b4 :: (bs.flatten ++ tail)) =
                                ([b0, b1, b2, b3, b4] :: bs, tail)
                              rw [b32Split.eq_6]
                              rw [ih tail hbs htail]
                          | cons c t5 => simp at hb

/-- A single decoded tail block re-encodes: from `relRepeat (Rel b32TailElem)
tails m st` with `tails.length ≤ 1`, `encodeB32Tail tails.flatten` reproduces
`⟨m, st⟩` (functionality of `b32TailElem` pins the bytes).
`[propext, Quot.sound]`-only. -/
theorem encodeB32Tail_of_rel (tails : List (List UInt8)) {m : Nat} (st : Bytes m)
    (hrel : relRepeat (Rel b32TailElem) tails m st) (hlen : tails.length ≤ 1) :
    encodeB32Tail tails.flatten = some ⟨m, st⟩ := by
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
          have hrelx : Rel b32TailElem x st := by
            rw [relRepeat_cons] at hrel
            rcases hrel with ⟨m₁, hm₁, s₁, s₂, hs, hx, hr⟩
            rw [relRepeat_nil] at hr
            have hm₁m : m₁ = m := by omega
            subst hm₁m
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
          have hxlen : x.length = 1 ∨ x.length = 2 ∨ x.length = 3 ∨ x.length = 4 :=
            Rel_b32TailElem_size x st hrelx
          have henc_ne : Codec.encode b32TailElem x ≠ none :=
            encode_ne_none b32TailElem x st hrelx
          cases he : Codec.encode b32TailElem x with
          | none => exact False.elim (henc_ne he)
          | some e =>
              rcases e with ⟨n₁, s₁⟩
              have hrel' : Rel b32TailElem x s₁ := encode_rel b32TailElem x he
              have hpin : (⟨n₁, s₁⟩ : Sigma fun k => Bytes k) = ⟨m, st⟩ :=
                b32TailElem_functional x s₁ st hrel' hrelx
              cases hpin
              rcases hxlen with h1 | h2 | h3 | h4
              · rcases x with _ | ⟨a, t⟩
                · simp only [List.length_nil] at h1; omega
                · cases t with
                    | nil => simp [encodeB32Tail]; exact he
                    | cons _ _ => simp only [List.length_cons] at h1; omega
              · rcases x with _ | ⟨a, t⟩
                · simp only [List.length_nil] at h2; omega
                · cases t with
                    | nil => simp only [List.length_cons, List.length_nil] at h2; omega
                    | cons b t2 =>
                        cases t2 with
                        | nil => simp [encodeB32Tail]; exact he
                        | cons _ _ => simp only [List.length_cons] at h2; omega
              · rcases x with _ | ⟨a, t⟩
                · simp only [List.length_nil] at h3; omega
                · cases t with
                    | nil => simp only [List.length_cons, List.length_nil] at h3; omega
                    | cons b t2 =>
                        cases t2 with
                        | nil => simp only [List.length_cons, List.length_nil] at h3; omega
                        | cons c t3 =>
                            cases t3 with
                            | nil => simp [encodeB32Tail]; exact he
                            | cons _ _ => simp only [List.length_cons] at h3; omega
              · rcases x with _ | ⟨a, t⟩
                · simp only [List.length_nil] at h4; omega
                · cases t with
                    | nil => simp only [List.length_cons, List.length_nil] at h4; omega
                    | cons b t2 =>
                        cases t2 with
                        | nil => simp only [List.length_cons, List.length_nil] at h4; omega
                        | cons c t3 =>
                            cases t3 with
                            | nil => simp only [List.length_cons, List.length_nil] at h4; omega
                            | cons d t4 =>
                                cases t4 with
                                | nil => simp [encodeB32Tail]; exact he
                                | cons _ _ => simp only [List.length_cons] at h4; omega
      | cons y ys =>
          have hnle : ¬ (x :: y :: ys).length ≤ 1 := by simp
          exact False.elim (hnle hlen)

/-- The converse (`decodeFullB32 s = some v → encodeB32 v = some ⟨n, s⟩`). -/
theorem decodeFullB32_conv {n : Nat} (s : Bytes n) (v : List UInt8)
    (h : decodeFullB32 s = some v) :
    encodeB32 v = some ⟨n, s⟩ := by
  rcases decodeFullB32_some s v h with ⟨blocks, t, tails, hmem, htail, hlen, hflat⟩
  rcases (decodeRepeat_spec b32BlockElem b32BlockConsumesByte blocks n s t).1 hmem with
    ⟨s₀, hs₀, hrel₀⟩
  have hblock5 : ∀ b ∈ blocks, b.length = 5 := relB32Block_len5 s₀ hrel₀
  have henc₀ : encodeRepeat b32BlockElem blocks = some ⟨n - t.remaining, s₀⟩ :=
    encodeRepeat_of_rel b32BlockElem b32BlockElem_functional blocks s₀ hrel₀
  -- re-encode the tail
  have hmemt : (tails, Suffix.empty t.remaining) ∈ decodeRepeat b32TailElem b32TailConsumesByte t.remaining t.bytes :=
    decodeFull_some b32TailElem b32TailConsumesByte t.bytes tails htail
  rcases (decodeRepeat_spec b32TailElem b32TailConsumesByte tails t.remaining t.bytes (Suffix.empty t.remaining)).1 hmemt with
    ⟨st, hst, hrelt⟩
  simp only [Suffix.empty, Nat.sub_zero] at st hrelt
  have henct : encodeB32Tail tails.flatten = some ⟨t.remaining, st⟩ :=
    encodeB32Tail_of_rel tails st hrelt hlen
  -- the flattened tail is at most 4 bytes
  have htail4 : tails.flatten.length ≤ 4 := by
    cases tails with
    | nil => simp
    | cons x txs =>
        cases txs with
        | nil =>
            have hxlen : x.length = 1 ∨ x.length = 2 ∨ x.length = 3 ∨ x.length = 4 := by
              rw [relRepeat_cons] at hrelt
              rcases hrelt with ⟨mh, hmh, sh, srest, hsp, hxr, _⟩
              exact Rel_b32TailElem_size x sh hxr
            simpa using hxlen.elim (fun h => (h ▸ (by decide : 1 ≤ 4)))
              (fun h => h.elim (fun h => (h ▸ (by decide : 2 ≤ 4)))
                (fun h => h.elim (fun h => (h ▸ (by decide : 3 ≤ 4))) (fun h => (h ▸ (by decide : 4 ≤ 4)))))
        | cons y ys =>
            have hnle : ¬ (x :: y :: ys).length ≤ 1 := by simp
            exact absurd hlen hnle
  have hsplit : b32Split (blocks.flatten ++ tails.flatten) = (blocks, tails.flatten) :=
    b32Split_blocks_tail blocks tails.flatten hblock5 htail4
  -- `st` is `t.bytes`
  have hst_eq : st = t.bytes := by
    have h1 : (Suffix.empty t.remaining).prepend st = t.bytes := hst.symm
    rw [Codec.prepend_empty] at h1
    apply Bytes.ext
    intro j
    have hj := congrFun h1 j
    rw [cast_bytes_val' (e := Nat.sub_zero t.remaining)] at hj
    exact hj
  subst hst_eq
  rw [encodeB32, b32Split_ofBytes_ofBytes v]
  rw [← hflat]
  rw [hsplit]
  rw [encodeB32']
  rw [henc₀, henct]
  -- unfold the `Option`/`Sigma` wrapper so the goal is stated over
  -- `(n - t.remaining) + t.remaining` and `concat s₀ t.bytes`
  dsimp only
  have hlen : n - t.remaining + t.remaining = n := Nat.sub_add_cancel t.hle
  have hbytes : Codec.concat s₀ t.bytes = cast (congrArg Bytes hlen.symm) s := by
    apply Bytes.ext
    intro j
    rw [cast_bytes_val' (e := hlen.symm)]
    unfold Codec.concat
    by_cases hj : j.val < n - t.remaining
    · simp [hj]
      have hread : s₀ ⟨j.val, hj⟩ = (t.prepend s₀) ⟨j.val, by omega⟩ :=
        (Codec.prepend_prefix_read t s₀ ⟨j.val, by omega⟩ hj).symm
      rw [hread]
      exact (congrFun hs₀ _).symm
    · have hidx : j.val - (n - t.remaining) < t.remaining := by
        have := t.hle
        omega
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
      simp only [hj]
      exact hread _
  have hsig : (⟨n - t.remaining + t.remaining, Codec.concat s₀ t.bytes⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ :=
    Sigma.ext hlen (by
      have h1 : HEq (Codec.concat s₀ t.bytes) (cast (congrArg Bytes hlen.symm) s) :=
        heq_of_eq hbytes
      exact h1.trans (cast_heq (congrArg Bytes hlen.symm) s))
  rw [hsig]

/-! ## Totality of the encoder (task 6.2)

Mirror of the base64 section: the spec's injectivity Scenario is the plain
`Option`-equality law `encodeB32 v = encodeB32 v' → v = v'`, which needs
`encodeB32`'s **totality** so the `none` branches of that equation are refuted.

`encodeB32` splits along the `B32` spine (`b32Split_ofBytes`) into 5-byte full
blocks and a 0-4-byte tail, then `encodeB32'` runs `encodeRepeat b32BlockElem`
over the blocks and `encodeB32Tail` over the tail. Both are total on those
domains: `b32BlockUnapply` is total on 5-byte lists and emits alphabet chars
(`b32BlockUnapply_len5`), and `b32TailUnapply` is total on 1-4-byte lists and
emits alphabet-or-pad chars (`b32TailUnapply_len14`).
`[propext, Quot.sound]`-only. -/

/-- `encodeB32Tail` is total on the tails the `B32` spine can produce (0-4 bytes). -/
theorem encodeB32Tail_ne_none (tail : List UInt8) (hlen : tail.length ≤ 4) :
    encodeB32Tail tail ≠ none := by
  match tail, hlen with
  | [], _ => simp [encodeB32Tail]
  | [b], _ =>
      simp only [encodeB32Tail]
      exact b32TailElem_encode_ne_none [b] (by simp) (by simp)
  | [a, b], _ =>
      simp only [encodeB32Tail]
      exact b32TailElem_encode_ne_none [a, b] (by simp) (by simp)
  | [a, b, c], _ =>
      simp only [encodeB32Tail]
      exact b32TailElem_encode_ne_none [a, b, c] (by simp) (by simp)
  | [a, b, c, d], _ =>
      simp only [encodeB32Tail]
      exact b32TailElem_encode_ne_none [a, b, c, d] (by simp) (by simp)
  | _ :: _ :: _ :: _ :: _ :: _, h => simp at h

/-- `encodeB32'` is total when every block is 5 bytes and the tail is at most 4. -/
theorem encodeB32'_ne_none (blocks : List (List UInt8)) (tail : List UInt8)
    (hblocks : ∀ b ∈ blocks, b.length = 5) (htail : tail.length ≤ 4) :
    encodeB32' blocks tail ≠ none := by
  unfold encodeB32'
  have hb : encodeRepeat b32BlockElem blocks ≠ none := by
    induction blocks with
    | nil => simp [Codec.encodeRepeat]
    | cons b rest ih =>
        have hbl : b.length = 5 := hblocks b (by simp)
        have hrest : ∀ x ∈ rest, x.length = 5 := fun x hx => hblocks x (by simp [hx])
        rw [Codec.encodeRepeat]
        have hne : Codec.encode b32BlockElem b ≠ none := b32BlockElem_encode_ne_none b hbl
        cases h₁ : Codec.encode b32BlockElem b with
        | none => exact absurd h₁ hne
        | some e₁ =>
            cases h₂ : Codec.encodeRepeat b32BlockElem rest with
            | none => exact absurd h₂ (ih hrest)
            | some e₂ => simp
  have ht : encodeB32Tail tail ≠ none := encodeB32Tail_ne_none tail htail
  cases hb' : encodeRepeat b32BlockElem blocks with
  | none => exact absurd hb' hb
  | some e₁ =>
      cases ht' : encodeB32Tail tail with
      | none => exact absurd ht' ht
      | some e₂ => simp

/-- For every `B32` spine value, the split's blocks are all 5 bytes and its tail
is at most 4 — the structural fact the encoder's totality rests on. -/
theorem b32Split_ofBytes_shape_bounds (v : B32) :
    (∀ b ∈ (b32Split_ofBytes v).1, b.length = 5) ∧ (b32Split_ofBytes v).2.length ≤ 4 := by
  induction v with
  | nil => exact ⟨by simp [b32Split_ofBytes], by simp [b32Split_ofBytes]⟩
  | tail1 b0 => exact ⟨by simp [b32Split_ofBytes], by simp [b32Split_ofBytes]⟩
  | tail2 b0 b1 => exact ⟨by simp [b32Split_ofBytes], by simp [b32Split_ofBytes]⟩
  | tail3 b0 b1 b2 => exact ⟨by simp [b32Split_ofBytes], by simp [b32Split_ofBytes]⟩
  | tail4 b0 b1 b2 b3 => exact ⟨by simp [b32Split_ofBytes], by simp [b32Split_ofBytes]⟩
  | full a b c d e rest ih =>
      obtain ⟨ihb, iht⟩ := ih
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [b32Split_ofBytes, List.mem_cons] at hx
        rcases hx with h | h
        · subst h; rfl
        · exact ihb x h
      · simpa [b32Split_ofBytes] using iht

/-- **Base32 encoding is total** — `encodeB32` never returns `none`.

`encodeB32` splits its value along the `B32` spine and delegates to
`encodeB32'`, whose totality needs exactly the bounds
`b32Split_ofBytes_shape_bounds` supplies (5-byte blocks, ≤ 4-byte tail).
`[propext, Quot.sound]`-only. -/
theorem encodeB32_ne_none (bs : List UInt8) : encodeB32 bs ≠ none := by
  unfold encodeB32
  obtain ⟨hb, ht⟩ := b32Split_ofBytes_shape_bounds (b32OfBytes bs)
  exact encodeB32'_ne_none _ _ hb ht

/-- `encodeB32` injectivity, in the both-succeed form:
`encodeB32 v = some ⟨n, s⟩ → encodeB32 v' = some ⟨n, s⟩ → v = v'`. -/
theorem encodeB32_injective {v v' : List UInt8} {n : Nat} {s : Bytes n}
    (h : encodeB32 v = some ⟨n, s⟩) (h' : encodeB32 v' = some ⟨n, s⟩) :
    v = v' := by
  have hv : decodeFullB32 s = some v := decodeFullB32_roundtrip v h
  have hv' : decodeFullB32 s = some v' := decodeFullB32_roundtrip v' h'
  exact Option.some.inj (hv.symm.trans hv')

/-- **`encodeB32` is injective, in the spec's `Option`-equality form:**
`encodeB32 v = encodeB32 v' → v = v'` — exactly the `basen` spec's Scenario
"Encoding is injective" (`encode{X} v = encode{X} v' → v = v'`).

Because `encodeB32` is total (`encodeB32_ne_none`), the left side cannot be
`none`; destructure the common result and hand both successes to
`encodeB32_injective`. `[propext, Quot.sound]`-only. -/
theorem encodeB32_injective_eq {v v' : List UInt8} (h : encodeB32 v = encodeB32 v') :
    v = v' := by
  cases hv : encodeB32 v with
  | none => exact absurd hv (encodeB32_ne_none v)
  | some e =>
      rcases e with ⟨n, s⟩
      have hv' : encodeB32 v' = some ⟨n, s⟩ := by rw [← h]; exact hv
      exact encodeB32_injective hv hv'

/-! ## The "unique canonical inverse" law (task 6.3)

Base32 mirror of the base64 section: the single proposition the roundtrip +
converse + injectivity trio jointly amounts to, i.e. **the decoder succeeds
exactly on the encoder's image**:

  `decodeFullB32 s = some v  ↔  ∃ v', encodeB32 v' = some ⟨n, s⟩ ∧ v = v'`

`→` is `decodeFullB32_conv`, `←` is `decodeFullB32_roundtrip`.
`[propext, Quot.sound]`-only. -/

/-- **Base32: decode succeeds iff `s` is in `encodeB32`'s image, at that value.**
`decodeFullB32 s = some v ↔ ∃ v', encodeB32 v' = some ⟨n, s⟩ ∧ v = v'`.
`[propext, Quot.sound]`-only. -/
theorem decodeFullB32_char {n : Nat} (s : Bytes n) (v : List UInt8) :
    decodeFullB32 s = some v ↔ ∃ v', encodeB32 v' = some ⟨n, s⟩ ∧ v = v' := by
  constructor
  · intro h
    exact ⟨v, decodeFullB32_conv s v h, rfl⟩
  · rintro ⟨w, he, hv⟩
    rw [hv]
    exact decodeFullB32_roundtrip w he

/-! ## General rejection laws (task 6.4, base32 mirror)

The base64 laws of the same names, mirrored over the base32 composition
(8-char code words, full blocks of 5 bytes, a tail of 0–4 bytes).  Each is
`[propext, Quot.sound]`-only, zero `sorry`:

* (a) `decodeFullB32_reject_invalid_at` — a non-`b32OrPad` byte at any index;
* (b) `decodeFullB32_reject_pad_at_low_slot` — a `=` at code-word slot 0 or 1
  (the `MY======MY======` class);
* (c) `decodeFullB32_reject_arity` — a byte count not divisible by 8. -/

/-- **Every consumed byte of a successful base32 decode satisfies `b32OrPad`.**

A success decomposes into a full-block region (every byte a `b32Char`, hence
`b32OrPad`) and a terminal-tail region (every byte `b32OrPad` by the `count 8
(satisfy b32OrPad)` window), and together they consume the whole input — the
general replacement for the index-0-only `decodeFullB32_reject_first_invalid`. -/
theorem decodeFullB32_consumed_alphabet {n : Nat} (s : Bytes n) (v : List UInt8)
    (h : decodeFullB32 s = some v) :
    ∀ i : Fin n, b32OrPad (s i) = true := by
  rcases decodeFullB32_some s v h with ⟨blocks, t, tails, hmem, htail, _hlen, _hflat⟩
  rcases (decodeRepeat_spec b32BlockElem b32BlockConsumesByte blocks n s t).1 hmem with
    ⟨s₁, hs, hrel⟩
  have hcanon : ∀ j : Fin (n - t.remaining), b32Char (s₁ j) = true :=
    relRepeat_forall b32Char (fun x {m} tt ht => Rel_b32BlockElem_canonical ht)
      blocks (n - t.remaining) s₁ hrel
  have htail_mem : (tails, Suffix.empty t.remaining) ∈
      decodeRepeat b32TailElem b32TailConsumesByte t.remaining t.bytes :=
    decodeFull_some b32TailElem b32TailConsumesByte t.bytes tails htail
  rcases (decodeRepeat_spec b32TailElem b32TailConsumesByte tails t.remaining t.bytes
    (Suffix.empty t.remaining)).1 htail_mem with ⟨s₂, hs₂, hrel₂⟩
  have htail_s : t.bytes = cast (congrArg Bytes (Nat.sub_zero t.remaining)) s₂ := by
    rw [hs₂]
    exact prepend_empty_eq s₂
  have hrel₂' : relRepeat (Rel b32TailElem) tails t.remaining t.bytes := by
    rw [htail_s]
    exact (relRepeat_cast (Rel b32TailElem) tails (Nat.sub_zero t.remaining) s₂).1 hrel₂
  have htail_forall : ∀ j : Fin t.remaining, b32OrPad (t.bytes j) = true :=
    relRepeat_forall b32OrPad
      (fun x {m} tt ht => by
        unfold b32TailElem at ht
        rw [Rel_iso] at ht
        rcases ht with ⟨a, _, hc⟩
        exact Rel_count_satisfy_forall b32OrPad 8 a tt hc)
      tails t.remaining t.bytes hrel₂'
  intro i
  by_cases hin : i.val < n - t.remaining
  · have hread : s i = s₁ ⟨i.val, hin⟩ := by
      rw [hs]
      exact Codec.prepend_prefix_read t s₁ i hin
    have hc : b32Char (s₁ ⟨i.val, hin⟩) = true := hcanon ⟨i.val, hin⟩
    rw [hread]
    unfold b32OrPad
    have hcv : b32Valid (s₁ ⟨i.val, hin⟩).toNat = true := hc
    rw [hcv]
    rfl
  · have hread : s i = t.bytes ⟨i.val - (n - t.remaining), by
      have := t.hle
      omega⟩ := by
      have hdrop : bdrop (n - t.remaining) s =
          cast (congrArg Bytes (Nat.sub_sub_self t.hle).symm) t.bytes := by
        rw [hs]
        exact bdrop_prepend t s₁
      have hsi : s i = s ⟨(⟨i.val - (n - t.remaining), by
            have := t.hle
            omega⟩ : Fin (n - (n - t.remaining))).val + (n - t.remaining), by
          have := t.hle
          have := i.isLt
          omega⟩ := by
        congr 1
        exact Fin.ext (by simp; omega)
      have hc := congrFun hdrop ⟨i.val - (n - t.remaining), by
        have := t.hle
        omega⟩
      unfold Codec.bdrop at hc
      rw [hsi]
      refine hc.trans ?_
      rw [Codec.cast_bytes_val_symm]
      congr 1
      exact Nat.sub_sub_self t.hle
    rw [hread]
    exact htail_forall _

/-- **An alphabet-invalid byte at any index is rejected (base32).**  Generalises
`decodeFullB32_reject_first_invalid` from index 0 to **every** index. -/
theorem decodeFullB32_reject_invalid_at {n : Nat} (s : Bytes n) (i : Fin n)
    (hbad : b32OrPad (s i) = false) :
    decodeFullB32 s = none := by
  cases h : decodeFullB32 s with
  | none => rfl
  | some v =>
      have htrue : b32OrPad (s i) = true := decodeFullB32_consumed_alphabet s v h i
      rw [htrue] at hbad
      exact absurd hbad (by decide : (true = false) → False)

/-- **A `b32TailElem` block pads only at slots 2 and later.**  A base32 tail block
is a padded 8-char window; `b32TailUnapply` of a 1-, 2-, 3- or 4-byte value puts
`valToB32` outputs in slots 0 and 1 and the `=` run only from slot 2 on.  So a `=`
byte of a tail block sits at index ≥ 2.

This is the "`=` is terminal only" half of RFC 4648 §6 at the block level, and the
input `decodeFullB32_reject_pad_at_low_slot` consumes. -/
theorem Rel_b32TailElem_pad_pos (x : List UInt8) {n : Nat} (s : Bytes n)
    (h : Rel b32TailElem x s) :
    ∀ i : Fin n, (s i).toNat = 61 → 2 ≤ i.val := by
  intro i hi
  unfold b32TailElem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, ha, hr⟩
  have hofn : List.ofFn s = a := Rel_count_satisfy_ofFn b32OrPad 8 a s hr
  have hn8 : n = 8 := Rel_count_satisfy_len b32OrPad 8 a s hr
  subst hn8
  unfold b32TailIso at ha
  change b32TailApply a = some x at ha
  have hsl : b32TailUnapply x = some a := (b32TailIso_law a x).1 ha
  -- read window slot `j` as a byte of `s`
  have read : ∀ (j : Nat) (hj : j < 8) {c : UInt8}, a[j]? = some c →
      s ⟨j, hj⟩ = c := by
    intro j hj c hc
    rw [← hofn] at hc
    rw [List.getElem?_ofFn] at hc
    rw [dite_eq_left hj] at hc
    exact Option.some.inj hc
  -- slot 0 of every tail shape is `valToB32 (v0 / 8)`
  have s0 : ∀ (v0 : UInt8) (rest : List UInt8), b32TailUnapply (v0 :: rest) = some a →
      a[0]? = some (toByte (valToB32 (v0.toNat / 8))) := by
    intro v0 rest hun
    -- enumerate the four encodable shapes; a 5+-byte value is `none`
    rcases rest with _ | ⟨w, r2⟩
    · simp only [b32TailUnapply, b32BlockUnapply, Option.some.injEq] at hun
      subst hun; rfl
    rcases r2 with _ | ⟨u, r3⟩
    · simp only [b32TailUnapply, b32BlockUnapply, Option.some.injEq] at hun
      subst hun; rfl
    rcases r3 with _ | ⟨u2, r4⟩
    · simp only [b32TailUnapply, b32BlockUnapply, Option.some.injEq] at hun
      subst hun; rfl
    rcases r4 with _ | ⟨u3, r5⟩
    · simp only [b32TailUnapply, b32BlockUnapply, Option.some.injEq] at hun
      subst hun; rfl
    · simp [b32TailUnapply, b32BlockUnapply] at hun
  have s1 : ∀ (v0 w : UInt8) (r2 : List UInt8), b32TailUnapply (v0 :: w :: r2) = some a →
      a[1]? = some (toByte (valToB32 ((v0.toNat % 8) * 4 + w.toNat / 64))) := by
    intro v0 w r2 hun
    rcases r2 with _ | ⟨u, r3⟩
    · simp only [b32TailUnapply, b32BlockUnapply, Option.some.injEq] at hun
      subst hun; rfl
    rcases r3 with _ | ⟨u2, r4⟩
    · simp only [b32TailUnapply, b32BlockUnapply, Option.some.injEq] at hun
      subst hun; rfl
    rcases r4 with _ | ⟨u3, r5⟩
    · simp only [b32TailUnapply, b32BlockUnapply, Option.some.injEq] at hun
      subst hun; rfl
    · simp [b32TailUnapply, b32BlockUnapply] at hun

  rcases i with ⟨k, hk⟩
  have hk8 : k = 0 ∨ k = 1 ∨ 2 ≤ k := by omega
  rcases hk8 with rfl | hk1 | hk2
  · rcases x with _ | ⟨v0, rest⟩
    · simp [b32TailUnapply] at hsl
    refine absurd hi ?_
    rw [read 0 hk (s0 v0 rest hsl), toByte_valToB32 _
      (by have := UInt8.toNat_lt v0; omega)]
    exact valToB32_not_pad _ (by have := UInt8.toNat_lt v0; omega)
  · subst hk1
    rcases x with _ | ⟨v0, rest⟩
    · simp [b32TailUnapply] at hsl
    rcases rest with _ | ⟨w, r2⟩
    · -- 1-byte tail: slot 1 is `valToB32 ((v0 % 8) * 4)`, an alphabet char
      have key : a[1]? = some (toByte (valToB32 ((v0.toNat % 8) * 4))) := by
        simp only [b32TailUnapply, b32BlockUnapply, Option.some.injEq] at hsl
        subst hsl
        rfl
      refine absurd hi ?_
      rw [read 1 hk key, toByte_valToB32 _
        (by have := UInt8.toNat_lt v0; omega)]
      exact valToB32_not_pad _ (by have := UInt8.toNat_lt v0; omega)
    · refine absurd hi ?_
      rw [read 1 hk (s1 v0 w r2 (by simpa using hsl)), toByte_valToB32 _
        (by have := UInt8.toNat_lt v0; have := UInt8.toNat_lt w; omega)]
      exact valToB32_not_pad _
        (by have := UInt8.toNat_lt v0; have := UInt8.toNat_lt w; omega)
  · exact hk2

/-- **A pad byte at code-word slot 0 or 1 is rejected (base32).**

Mirror of `Base64.decodeFullB64_reject_pad_at_low_slot`: the full-block region is
alphabet-only and 8-aligned, and a terminal-tail block pads only at slots 2 and
later (`Rel_b32TailElem_pad_pos`).  So a `=` whose position modulo 8 is 0 or 1
cannot occur in a successful decode — covering the `MY======MY======` class. -/
theorem decodeFullB32_reject_pad_at_low_slot {n : Nat} (s : Bytes n) (i : Fin n)
    (hpad : (s i).toNat = 61) (hslots : i.val % 8 = 0 ∨ i.val % 8 = 1) :
    decodeFullB32 s = none := by
  cases h : decodeFullB32 s with
  | none => rfl
  | some v =>
    rcases decodeFullB32_some s v h with ⟨blocks, t, tails, hmem, htail, _hlen, _hflat⟩
    rcases (decodeRepeat_spec b32BlockElem b32BlockConsumesByte blocks n s t).1 hmem with
      ⟨s₁, hs, hrel⟩
    have hblk_len : n - t.remaining = 8 * blocks.length := relB32Block_len s₁ hrel
    have hcanon : ∀ j : Fin (n - t.remaining), b32Char (s₁ j) = true :=
      relRepeat_forall b32Char (fun x {m} tt ht => Rel_b32BlockElem_canonical ht)
        blocks (n - t.remaining) s₁ hrel
    have htail_mem : (tails, Suffix.empty t.remaining) ∈
        decodeRepeat b32TailElem b32TailConsumesByte t.remaining t.bytes :=
      decodeFull_some b32TailElem b32TailConsumesByte t.bytes tails htail
    rcases (decodeRepeat_spec b32TailElem b32TailConsumesByte tails t.remaining t.bytes
      (Suffix.empty t.remaining)).1 htail_mem with ⟨s₂, hs₂, hrel₂⟩
    have htail_s : t.bytes = cast (congrArg Bytes (Nat.sub_zero t.remaining)) s₂ := by
      rw [hs₂]
      exact prepend_empty_eq s₂
    have hrel₂' : relRepeat (Rel b32TailElem) tails t.remaining t.bytes := by
      rw [htail_s]
      exact (relRepeat_cast (Rel b32TailElem) tails (Nat.sub_zero t.remaining) s₂).1 hrel₂
    have htail_len : t.remaining = 8 * tails.length := relB32Tail_len t.bytes hrel₂'
    by_cases hin : i.val < n - t.remaining
    · -- block region: alphabet only, never the pad
      have hread : s i = s₁ ⟨i.val, hin⟩ := by
        rw [hs]
        exact Codec.prepend_prefix_read t s₁ i hin
      have hc : b32Char (s₁ ⟨i.val, hin⟩) = true := hcanon ⟨i.val, hin⟩
      rw [hread] at hpad
      unfold b32Char at hc
      rw [hpad] at hc
      have hfalse : b32Valid 61 = false := by decide
      rw [hfalse] at hc
      exact absurd hc (by decide)
    · -- tail region
      have hge : n - t.remaining ≤ i.val := Nat.le_of_not_gt hin
      have hdrop : bdrop (n - t.remaining) s =
          cast (congrArg Bytes (Nat.sub_sub_self t.hle).symm) t.bytes := by
        rw [hs]
        exact bdrop_prepend t s₁
      have hread : s i = t.bytes ⟨i.val - (n - t.remaining), by
        have := t.hle
        omega⟩ := by
        have hsi : s i = s ⟨(⟨i.val - (n - t.remaining), by
              have := t.hle
              omega⟩ : Fin (n - (n - t.remaining))).val + (n - t.remaining), by
            have := t.hle
            have := i.isLt
            omega⟩ := by
          congr 1
          exact Fin.ext (by simp; omega)
        have hc := congrFun hdrop ⟨i.val - (n - t.remaining), by
          have := t.hle
          omega⟩
        unfold Codec.bdrop at hc
        rw [hsi]
        refine hc.trans ?_
        rw [Codec.cast_bytes_val_symm]
        congr 1
        exact Nat.sub_sub_self t.hle
      rcases tails with _ | ⟨x, xs⟩
      · rw [relRepeat_nil] at hrel₂'
        omega
      rw [relRepeat_cons] at hrel₂'
      rcases hrel₂' with ⟨m, hm, sb, srest, hsplice, hx, _⟩
      have hm8 : m = 8 := Rel_b32TailElem_len x sb hx
      subst hm8
      have hk : i.val - (n - t.remaining) < 8 := by
        rcases xs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> simp_all <;> omega
      have hpad_t : (t.bytes ⟨i.val - (n - t.remaining), by
          have := t.hle
          omega⟩).toNat = 61 := by
        rw [← hread]
        exact hpad
      have hread' : t.bytes ⟨i.val - (n - t.remaining), by
          have := t.hle
          omega⟩ = sb ⟨i.val - (n - t.remaining), hk⟩ := by
        rw [hsplice]
        exact Codec.splice_prefix_read hm sb srest
          ⟨i.val - (n - t.remaining), by omega⟩ hk
      have hpad_sb : (sb ⟨i.val - (n - t.remaining), hk⟩).toNat = 61 := by
        rw [← hread']
        exact hpad_t
      have hpos : 2 ≤ i.val - (n - t.remaining) :=
        Rel_b32TailElem_pad_pos x sb hx ⟨i.val - (n - t.remaining), hk⟩ hpad_sb
      have hmod : (i.val - (n - t.remaining)) % 8 = i.val % 8 := by
        rw [hblk_len]
        omega
      rcases hslots with h0 | h0 <;> omega

/-- **A successful base32 decode consumes a whole number of 8-byte code words.**

The arity law: `relB32Block_len` gives `n - t.remaining = 8 · blocks.length`,
`relB32Tail_len` gives `t.remaining = 8 · tails.length`, and the two regions
partition `n` — so `n % 8 = 0`.  No case-splitting on named vectors. -/
theorem decodeFullB32_arity {n : Nat} (s : Bytes n) (v : List UInt8)
    (h : decodeFullB32 s = some v) :
    n % 8 = 0 := by
  rcases decodeFullB32_some s v h with ⟨blocks, t, tails, hmem, htail, _hlen, _hflat⟩
  rcases (decodeRepeat_spec b32BlockElem b32BlockConsumesByte blocks n s t).1 hmem with
    ⟨s₁, hs, hrel⟩
  have hblk_len : n - t.remaining = 8 * blocks.length := relB32Block_len s₁ hrel
  have htail_mem : (tails, Suffix.empty t.remaining) ∈
      decodeRepeat b32TailElem b32TailConsumesByte t.remaining t.bytes :=
    decodeFull_some b32TailElem b32TailConsumesByte t.bytes tails htail
  rcases (decodeRepeat_spec b32TailElem b32TailConsumesByte tails t.remaining t.bytes
    (Suffix.empty t.remaining)).1 htail_mem with ⟨s₂, hs₂, hrel₂⟩
  have htail_s : t.bytes = cast (congrArg Bytes (Nat.sub_zero t.remaining)) s₂ := by
    rw [hs₂]
    exact prepend_empty_eq s₂
  have hrel₂' : relRepeat (Rel b32TailElem) tails t.remaining t.bytes := by
    rw [htail_s]
    exact (relRepeat_cast (Rel b32TailElem) tails (Nat.sub_zero t.remaining) s₂).1 hrel₂
  have htail_len : t.remaining = 8 * tails.length := relB32Tail_len t.bytes hrel₂'
  have hn : n = 8 * (blocks.length + tails.length) := by
    have hle := t.hle
    omega
  rw [hn, Nat.mul_mod_right]

/-- **Wrong-arity input is rejected (base32).**  Generalises
`decodeFullB32_reject_bad_length`: a byte count not divisible by 8 cannot be a
base32 encoding. -/
theorem decodeFullB32_reject_arity {n : Nat} (s : Bytes n) (hmod : n % 8 ≠ 0) :
    decodeFullB32 s = none := by
  cases h : decodeFullB32 s with
  | none => rfl
  | some v =>
      exact absurd (decodeFullB32_arity s v h) hmod

end BaseN.Base32
