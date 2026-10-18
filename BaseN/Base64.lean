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

namespace BaseN.Base64

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

-- Nat-level codec

/-- Encode a byte list as base64 (Nat level), RFC 4648 §4 with `=` padding. -/
def encodeN (bs : List Nat) : List Nat :=
  match bs with
  | [] => []
  | b0 :: b1 :: b2 :: rest =>
    [valToB64 (b0 / 4), valToB64 ((b0 % 4) * 16 + b1 / 16),
     valToB64 ((b1 % 16) * 4 + b2 / 64), valToB64 (b2 % 64)] ++ encodeN rest
  | [b0] => [valToB64 (b0 / 4), valToB64 ((b0 % 4) * 16), 61, 61]
  | [b0, b1] => [valToB64 (b0 / 4), valToB64 ((b0 % 4) * 16 + b1 / 16), valToB64 ((b1 % 16) * 4), 61]

/-- Decode 4-char groups of base64 into bytes (`none` on bad input), Nat level. -/
def decodeN (bs : List Nat) : Option (List Nat) :=
  match bs with
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: rest =>
    if c0 = 61 || c1 = 61 then none
    else if ¬ b64Valid c0 || ¬ b64Valid c1 then none
    else
      let v0 := b64ToVal c0
      let v1 := b64ToVal c1
      let b0 := v0 * 4 + v1 / 16
      if c2 = 61 && c3 = 61 then
        if rest = [] then
          match decodeN rest with
          | some tl => some (b0 :: tl)
          | none => none
        else none
      else if c2 = 61 then none
      else if ¬ b64Valid c2 then none
      else
        let v2 := b64ToVal c2
        let b1 := (v1 % 16) * 16 + v2 / 4
        if c3 = 61 then
          if rest = [] then
            match decodeN rest with
            | some tl => some (b0 :: b1 :: tl)
            | none => none
          else none
        else if ¬ b64Valid c3 then none
        else
          let v3 := b64ToVal c3
          let b2 := (v2 % 4) * 64 + v3
          match decodeN rest with
          | some tl => some (b0 :: b1 :: b2 :: tl)
          | none => none
  | _ => none

/-- `decodeN (c0::c1::c2::c3::rest)` — the 4-char group case, stated equationally. -/
theorem decodeN_cons4 (c0 c1 c2 c3 : Nat) (rest : List Nat) :
    decodeN (c0 :: c1 :: c2 :: c3 :: rest) =
      if c0 = 61 || c1 = 61 then none
      else if ¬ b64Valid c0 || ¬ b64Valid c1 then none
      else
        let v0 := b64ToVal c0
        let v1 := b64ToVal c1
        let b0 := v0 * 4 + v1 / 16
        if c2 = 61 && c3 = 61 then
          if rest = [] then
            match decodeN rest with
            | some tl => some (b0 :: tl)
            | none => none
          else none
        else if c2 = 61 then none
        else if ¬ b64Valid c2 then none
        else
          let v2 := b64ToVal c2
          let b1 := (v1 % 16) * 16 + v2 / 4
          if c3 = 61 then
            if rest = [] then
              match decodeN rest with
              | some tl => some (b0 :: b1 :: tl)
              | none => none
            else none
          else if ¬ b64Valid c3 then none
          else
            let v3 := b64ToVal c3
            let b2 := (v2 % 4) * 64 + v3
            match decodeN rest with
            | some tl => some (b0 :: b1 :: b2 :: tl)
            | none => none :=
  rfl

/-- `decodeN (encodeN [b0]) = some [b0]` (1-byte tail, two pads). -/
theorem decodeN_encodeN_single (b0 : Nat) (hb0 : b0 < 256) :
    decodeN (encodeN [b0]) = some [b0] := by
  have h0 : b0 / 4 ≤ 63 := by omega
  have h1 : (b0 % 4) * 16 ≤ 63 := by omega
  have hnp0 : valToB64 (b0 / 4) ≠ 61 := valToB64_not_pad (b0 / 4) h0
  have hnp1 : valToB64 ((b0 % 4) * 16) ≠ 61 := valToB64_not_pad ((b0 % 4) * 16) h1
  have hvalid0 : b64Valid (valToB64 (b0 / 4)) = true := valToB64_valid (b0 / 4) h0
  have hvalid1 : b64Valid (valToB64 ((b0 % 4) * 16)) = true := valToB64_valid ((b0 % 4) * 16) h1
  have hsum : (b0 / 4) * 4 + (((b0 % 4) * 16) / 16) = b0 := by
    have hbd : ((b0 % 4) * 16) / 16 = b0 % 4 := Nat.mul_div_left (b0 % 4) (by decide : 0 < 16)
    have hdiv := Nat.div_add_mod b0 4
    omega
  unfold encodeN decodeN
  rw [hvalid0, hvalid1]
  rw [b64ToVal_valToB64 (b0 / 4) h0, b64ToVal_valToB64 ((b0 % 4) * 16) h1]
  simp only [hnp0, hnp1]
  rw [hsum]
  simp [decodeN]

/-- `decodeN (encodeN [b0; b1]) = some [b0; b1]` (2-byte tail, one pad). -/
theorem decodeN_encodeN_pair (b0 b1 : Nat) (hb0 : b0 < 256) (hb1 : b1 < 256) :
    decodeN (encodeN [b0, b1]) = some [b0, b1] := by
  have h0 : b0 / 4 ≤ 63 := by omega
  have h1 : (b0 % 4) * 16 + b1 / 16 ≤ 63 := by omega
  have h2 : (b1 % 16) * 4 ≤ 63 := by omega
  have hnp0 : valToB64 (b0 / 4) ≠ 61 := valToB64_not_pad (b0 / 4) h0
  have hnp1 : valToB64 ((b0 % 4) * 16 + b1 / 16) ≠ 61 := valToB64_not_pad _ h1
  have hnp2 : valToB64 ((b1 % 16) * 4) ≠ 61 := valToB64_not_pad _ h2
  have hvalid0 : b64Valid (valToB64 (b0 / 4)) = true := valToB64_valid (b0 / 4) h0
  have hvalid1 : b64Valid (valToB64 ((b0 % 4) * 16 + b1 / 16)) = true := valToB64_valid _ h1
  have hvalid2 : b64Valid (valToB64 ((b1 % 16) * 4)) = true := valToB64_valid _ h2
  have hb0v : (b0 / 4) * 4 + (((b0 % 4) * 16 + b1 / 16) / 16) = b0 := byte0 b0 b1 hb0 hb1
  have hb1v : (((b0 % 4) * 16 + b1 / 16) % 16) * 16 + (((b1 % 16) * 4) / 4) = b1 := byte1 b0 b1 hb0 hb1
  unfold encodeN decodeN
  rw [hvalid0, hvalid1]
  rw [b64ToVal_valToB64 (b0 / 4) h0, b64ToVal_valToB64 ((b0 % 4) * 16 + b1 / 16) h1]
  simp only [hnp0, hnp1]
  rw [hb0v]
  rw [hvalid2]
  rw [b64ToVal_valToB64 ((b1 % 16) * 4) h2]
  simp only [hnp2]
  rw [hb1v]
  simp [decodeN]

/-- `decodeN (encodeN [b0; b1; b2]) = some [b0; b1; b2]` (3-byte block). -/
theorem decodeN_encodeN_triple (b0 b1 b2 : Nat) (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) :
    decodeN (encodeN [b0, b1, b2]) = some [b0, b1, b2] := by
  have h0 : b0 / 4 ≤ 63 := by omega
  have h1 : (b0 % 4) * 16 + b1 / 16 ≤ 63 := by omega
  have h2 : (b1 % 16) * 4 + b2 / 64 ≤ 63 := by omega
  have h3 : b2 % 64 ≤ 63 := by omega
  have hnp0 : valToB64 (b0 / 4) ≠ 61 := valToB64_not_pad (b0 / 4) h0
  have hnp1 : valToB64 ((b0 % 4) * 16 + b1 / 16) ≠ 61 := valToB64_not_pad _ h1
  have hnp2 : valToB64 ((b1 % 16) * 4 + b2 / 64) ≠ 61 := valToB64_not_pad _ h2
  have hnp3 : valToB64 (b2 % 64) ≠ 61 := valToB64_not_pad (b2 % 64) h3
  have hvalid0 : b64Valid (valToB64 (b0 / 4)) = true := valToB64_valid (b0 / 4) h0
  have hvalid1 : b64Valid (valToB64 ((b0 % 4) * 16 + b1 / 16)) = true := valToB64_valid _ h1
  have hvalid2 : b64Valid (valToB64 ((b1 % 16) * 4 + b2 / 64)) = true := valToB64_valid _ h2
  have hvalid3 : b64Valid (valToB64 (b2 % 64)) = true := valToB64_valid (b2 % 64) h3
  have hb0v : (b0 / 4) * 4 + (((b0 % 4) * 16 + b1 / 16) / 16) = b0 := byte0 b0 b1 hb0 hb1
  have hb1v : (((b0 % 4) * 16 + b1 / 16) % 16) * 16 + (((b1 % 16) * 4 + b2 / 64) / 4) = b1 := by
    have hmod16 : ((b0 % 4) * 16 + b1 / 16) % 16 = b1 / 16 := by
      have h := Nat.add_mul_mod_self_right (b0 % 4) (b1 / 16) 16
      omega
    have hdiv4 : ((b1 % 16) * 4 + b2 / 64) / 4 = b1 % 16 := by
      have h := Nat.add_mul_div_left (b2 / 64) (b1 % 16) (by decide : 0 < 4)
      have hz : b2 / 64 / 4 = 0 := Nat.div_eq_of_lt (by omega)
      omega
    have hsum := Nat.div_add_mod b1 16
    omega
  have hb2v : (((b1 % 16) * 4 + b2 / 64) % 4) * 64 + (b2 % 64) = b2 := byte2 b1 b2 hb1 hb2
  show decodeN ([valToB64 (b0 / 4), valToB64 ((b0 % 4) * 16 + b1 / 16),
      valToB64 ((b1 % 16) * 4 + b2 / 64), valToB64 (b2 % 64)] ++ encodeN []) = some [b0, b1, b2]
  simp only [encodeN, List.append_nil]
  unfold decodeN
  rw [hvalid0, hvalid1]
  rw [b64ToVal_valToB64 (b0 / 4) h0, b64ToVal_valToB64 ((b0 % 4) * 16 + b1 / 16) h1]
  simp only [hnp0, hnp1]
  rw [hb0v]
  rw [hvalid2]
  rw [b64ToVal_valToB64 ((b1 % 16) * 4 + b2 / 64) h2]
  simp only [hnp2]
  rw [hb1v]
  rw [hvalid3]
  rw [b64ToVal_valToB64 (b2 % 64) h3]
  simp only [hnp3]
  rw [hb2v]
  simp [decodeN]

/-- `decodeN (encodeN(b0::b1::b2::rest)) = (b0::b1::b2::·) <$> decodeN (encodeN rest)`. -/
theorem decodeN_block (b0 b1 b2 : Nat) (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256)
    (rest : List Nat) :
    decodeN (encodeN (b0 :: b1 :: b2 :: rest)) =
      match decodeN (encodeN rest) with
      | some ys => some (b0 :: b1 :: b2 :: ys)
      | none => none := by
  have h0 : b0 / 4 ≤ 63 := by omega
  have h1 : (b0 % 4) * 16 + b1 / 16 ≤ 63 := by omega
  have h2 : (b1 % 16) * 4 + b2 / 64 ≤ 63 := by omega
  have h3 : b2 % 64 ≤ 63 := by omega
  have hnp0 : valToB64 (b0 / 4) ≠ 61 := valToB64_not_pad (b0 / 4) h0
  have hnp1 : valToB64 ((b0 % 4) * 16 + b1 / 16) ≠ 61 := valToB64_not_pad _ h1
  have hnp2 : valToB64 ((b1 % 16) * 4 + b2 / 64) ≠ 61 := valToB64_not_pad _ h2
  have hnp3 : valToB64 (b2 % 64) ≠ 61 := valToB64_not_pad (b2 % 64) h3
  have hvalid0 : b64Valid (valToB64 (b0 / 4)) = true := valToB64_valid (b0 / 4) h0
  have hvalid1 : b64Valid (valToB64 ((b0 % 4) * 16 + b1 / 16)) = true := valToB64_valid _ h1
  have hvalid2 : b64Valid (valToB64 ((b1 % 16) * 4 + b2 / 64)) = true := valToB64_valid _ h2
  have hvalid3 : b64Valid (valToB64 (b2 % 64)) = true := valToB64_valid (b2 % 64) h3
  have hb0v : (b0 / 4) * 4 + (((b0 % 4) * 16 + b1 / 16) / 16) = b0 := byte0 b0 b1 hb0 hb1
  have hb1v : (((b0 % 4) * 16 + b1 / 16) % 16) * 16 + (((b1 % 16) * 4 + b2 / 64) / 4) = b1 := by
    have hmod16 : ((b0 % 4) * 16 + b1 / 16) % 16 = b1 / 16 := by
      have h := Nat.add_mul_mod_self_right (b0 % 4) (b1 / 16) 16
      omega
    have hdiv4 : ((b1 % 16) * 4 + b2 / 64) / 4 = b1 % 16 := by
      have h := Nat.add_mul_div_left (b2 / 64) (b1 % 16) (by decide : 0 < 4)
      have hz : b2 / 64 / 4 = 0 := Nat.div_eq_of_lt (by omega)
      omega
    have hsum := Nat.div_add_mod b1 16
    omega
  have hb2v : (((b1 % 16) * 4 + b2 / 64) % 4) * 64 + (b2 % 64) = b2 := byte2 b1 b2 hb1 hb2
  show decodeN ([valToB64 (b0 / 4), valToB64 ((b0 % 4) * 16 + b1 / 16),
      valToB64 ((b1 % 16) * 4 + b2 / 64), valToB64 (b2 % 64)] ++ encodeN rest) =
    match decodeN (encodeN rest) with
    | some ys => some (b0 :: b1 :: b2 :: ys)
    | none => none
  simp only [List.cons_append, List.nil_append]
  rw [decodeN_cons4]
  rw [hvalid0, hvalid1]
  rw [b64ToVal_valToB64 (b0 / 4) h0, b64ToVal_valToB64 ((b0 % 4) * 16 + b1 / 16) h1]
  simp only [hnp0, hnp1]
  rw [hb0v]
  rw [hvalid2]
  rw [b64ToVal_valToB64 ((b1 % 16) * 4 + b2 / 64) h2]
  simp only [hnp2]
  rw [hb1v]
  rw [hvalid3]
  rw [b64ToVal_valToB64 (b2 % 64) h3]
  simp only [hnp3]
  rw [hb2v]
  simp


/-- `decodeN (encodeN bs) = some bs`, for byte lists (all elements `< 256`). -/
theorem roundtripN (bs : List Nat) :
    (∀ b ∈ bs, b < 256) → decodeN (encodeN bs) = some bs := by
  intro hbs
  have h := Nat.strongRecOn (motive := fun n => ∀ (ys : List Nat), ys.length = n →
      (∀ b ∈ ys, b < 256) → decodeN (encodeN ys) = some ys)
    bs.length (fun n ih ys hlen hys => by
      cases ys with
      | nil => rfl
      | cons b bs =>
          cases bs with
          | nil => exact decodeN_encodeN_single b (hys b (by simp))
          | cons b1 bs =>
              cases bs with
              | nil => exact decodeN_encodeN_pair b b1 (hys b (by simp)) (hys b1 (by simp))
              | cons b2 rest =>
                  have hb : b < 256 := hys b (by simp)
                  have hb1 : b1 < 256 := hys b1 (by simp)
                  have hb2 : b2 < 256 := hys b2 (by simp)
                  have hrest : ∀ x ∈ rest, x < 256 := by intro x hx; exact hys x (by simp [hx])
                  rw [decodeN_block b b1 b2 hb hb1 hb2 rest]
                  have hlen' : rest.length < n := by
                    have hlt : rest.length < (b :: b1 :: b2 :: rest).length := by
                      simp only [List.length_cons]
                      omega
                    rw [hlen] at hlt
                    exact hlt
                  rw [ih rest.length hlen' rest rfl hrest])
  exact h bs rfl hbs

-- UInt8 surface

private theorem toByte_valToB64 (i : Nat) (hi : i ≤ 63) :
    (toByte (valToB64 i)).toNat = valToB64 i := by
  unfold toByte
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToB64_lt_256 i hi)]

/-- Encode a byte list as base64, RFC 4648 §4 with `=` padding. -/
def encode (bs : List UInt8) : List UInt8 :=
  match bs with
  | [] => []
  | b0 :: b1 :: b2 :: rest =>
    [toByte (valToB64 (b0.toNat / 4)), toByte (valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16)),
     toByte (valToB64 ((b1.toNat % 16) * 4 + b2.toNat / 64)), toByte (valToB64 (b2.toNat % 64))] ++ encode rest
  | [b0] => [toByte (valToB64 (b0.toNat / 4)), toByte (valToB64 ((b0.toNat % 4) * 16)), 61, 61]
  | [b0, b1] => [toByte (valToB64 (b0.toNat / 4)), toByte (valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16)), toByte (valToB64 ((b1.toNat % 16) * 4)), 61]

/-- Decode 4-char groups of base64 into bytes (`none` on bad input). -/
def decode (bs : List UInt8) : Option (List UInt8) :=
  match bs with
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: rest =>
    if c0.toNat = 61 || c1.toNat = 61 then none
    else if ¬ b64Valid c0.toNat || ¬ b64Valid c1.toNat then none
    else
      let v0 := b64ToVal c0.toNat
      let v1 := b64ToVal c1.toNat
      let b0 := v0 * 4 + v1 / 16
      if c2.toNat = 61 && c3.toNat = 61 then
        if rest = [] then
          match decode rest with
          | some tl => some (toByte b0 :: tl)
          | none => none
        else none
      else if c2.toNat = 61 then none
      else if ¬ b64Valid c2.toNat then none
      else
        let v2 := b64ToVal c2.toNat
        let b1 := (v1 % 16) * 16 + v2 / 4
        if c3.toNat = 61 then
          if rest = [] then
            match decode rest with
            | some tl => some (toByte b0 :: toByte b1 :: tl)
            | none => none
          else none
        else if ¬ b64Valid c3.toNat then none
        else
          let v3 := b64ToVal c3.toNat
          let b2 := (v2 % 4) * 64 + v3
          match decode rest with
          | some tl => some (toByte b0 :: toByte b1 :: toByte b2 :: tl)
          | none => none
  | _ => none

/-- `decode (c0::c1::c2::c3::rest)` — the 4-char group case (`UInt8`), stated equationally. -/
theorem decode_cons4 (c0 c1 c2 c3 : UInt8) (rest : List UInt8) :
    decode (c0 :: c1 :: c2 :: c3 :: rest) =
      if c0.toNat = 61 || c1.toNat = 61 then none
      else if ¬ b64Valid c0.toNat || ¬ b64Valid c1.toNat then none
      else
        let v0 := b64ToVal c0.toNat
        let v1 := b64ToVal c1.toNat
        let b0 := v0 * 4 + v1 / 16
        if c2.toNat = 61 && c3.toNat = 61 then
          if rest = [] then
            match decode rest with
            | some tl => some (toByte b0 :: tl)
            | none => none
          else none
        else if c2.toNat = 61 then none
        else if ¬ b64Valid c2.toNat then none
        else
          let v2 := b64ToVal c2.toNat
          let b1 := (v1 % 16) * 16 + v2 / 4
          if c3.toNat = 61 then
            if rest = [] then
              match decode rest with
              | some tl => some (toByte b0 :: toByte b1 :: tl)
              | none => none
            else none
          else if ¬ b64Valid c3.toNat then none
          else
            let v3 := b64ToVal c3.toNat
            let b2 := (v2 % 4) * 64 + v3
            match decode rest with
            | some tl => some (toByte b0 :: toByte b1 :: toByte b2 :: tl)
            | none => none :=
  rfl

/-- `decode (encode bs) = some bs` — the full roundtrip, `UInt8` level. -/
theorem roundtrip (bs : List UInt8) :
    decode (encode bs) = some bs := by
  have h := Nat.strongRecOn (motive := fun n => ∀ (ys : List UInt8), ys.length = n →
      decode (encode ys) = some ys)
    bs.length (fun n ih ys hlen => by
      cases ys with
      | nil => rfl
      | cons b bs =>
          cases bs with
          | nil =>
              have hb : b.toNat < 256 := by simpa using UInt8.toNat_lt b
              have h0 : b.toNat / 4 ≤ 63 := by omega
              have h1 : (b.toNat % 4) * 16 ≤ 63 := by omega
              have hnp0 : valToB64 (b.toNat / 4) ≠ 61 := valToB64_not_pad _ h0
              have hnp1 : valToB64 ((b.toNat % 4) * 16) ≠ 61 := valToB64_not_pad _ h1
              have hvalid0 : b64Valid (valToB64 (b.toNat / 4)) = true := valToB64_valid _ h0
              have hvalid1 : b64Valid (valToB64 ((b.toNat % 4) * 16)) = true := valToB64_valid _ h1
              have hsum : (b.toNat / 4) * 4 + (((b.toNat % 4) * 16) / 16) = b.toNat := by
                have hbd : ((b.toNat % 4) * 16) / 16 = b.toNat % 4 := Nat.mul_div_left (b.toNat % 4) (by decide : 0 < 16)
                have hdiv := Nat.div_add_mod b.toNat 4
                omega
              unfold encode decode
              rw [toByte_valToB64 (b.toNat / 4) h0, toByte_valToB64 ((b.toNat % 4) * 16) h1]
              rw [hvalid0, hvalid1]
              rw [b64ToVal_valToB64 (b.toNat / 4) h0, b64ToVal_valToB64 ((b.toNat % 4) * 16) h1]
              simp only [hnp0, hnp1]
              rw [hsum]
              simp [decode, toByte, UInt8.ofNat_toNat]
          | cons b1 bs =>
              cases bs with
              | nil =>
                  have hb : b.toNat < 256 := by simpa using UInt8.toNat_lt b
                  have hb1 : b1.toNat < 256 := by simpa using UInt8.toNat_lt b1
                  have h0 : b.toNat / 4 ≤ 63 := by omega
                  have h1 : (b.toNat % 4) * 16 + b1.toNat / 16 ≤ 63 := by omega
                  have h2 : (b1.toNat % 16) * 4 ≤ 63 := by omega
                  have hnp0 : valToB64 (b.toNat / 4) ≠ 61 := valToB64_not_pad _ h0
                  have hnp1 : valToB64 ((b.toNat % 4) * 16 + b1.toNat / 16) ≠ 61 := valToB64_not_pad _ h1
                  have hnp2 : valToB64 ((b1.toNat % 16) * 4) ≠ 61 := valToB64_not_pad _ h2
                  have hvalid0 : b64Valid (valToB64 (b.toNat / 4)) = true := valToB64_valid _ h0
                  have hvalid1 : b64Valid (valToB64 ((b.toNat % 4) * 16 + b1.toNat / 16)) = true := valToB64_valid _ h1
                  have hvalid2 : b64Valid (valToB64 ((b1.toNat % 16) * 4)) = true := valToB64_valid _ h2
                  have hb0v : (b.toNat / 4) * 4 + (((b.toNat % 4) * 16 + b1.toNat / 16) / 16) = b.toNat := byte0 b.toNat b1.toNat hb hb1
                  have hb1v : (((b.toNat % 4) * 16 + b1.toNat / 16) % 16) * 16 + (((b1.toNat % 16) * 4) / 4) = b1.toNat := byte1 b.toNat b1.toNat hb hb1
                  unfold encode decode
                  rw [toByte_valToB64 (b.toNat / 4) h0, toByte_valToB64 ((b.toNat % 4) * 16 + b1.toNat / 16) h1,
                      toByte_valToB64 ((b1.toNat % 16) * 4) h2]
                  rw [hvalid0, hvalid1]
                  rw [b64ToVal_valToB64 (b.toNat / 4) h0, b64ToVal_valToB64 ((b.toNat % 4) * 16 + b1.toNat / 16) h1]
                  simp only [hnp0, hnp1]
                  rw [hb0v]
                  rw [hvalid2]
                  rw [b64ToVal_valToB64 ((b1.toNat % 16) * 4) h2]
                  simp only [hnp2]
                  rw [hb1v]
                  simp [decode, toByte, UInt8.ofNat_toNat]
              | cons b2 rest =>
                  have hb : b.toNat < 256 := by simpa using UInt8.toNat_lt b
                  have hb1 : b1.toNat < 256 := by simpa using UInt8.toNat_lt b1
                  have hb2 : b2.toNat < 256 := by simpa using UInt8.toNat_lt b2
                  have h0 : b.toNat / 4 ≤ 63 := by omega
                  have h1 : (b.toNat % 4) * 16 + b1.toNat / 16 ≤ 63 := by omega
                  have h2 : (b1.toNat % 16) * 4 + b2.toNat / 64 ≤ 63 := by omega
                  have h3 : b2.toNat % 64 ≤ 63 := by omega
                  have hnp0 : valToB64 (b.toNat / 4) ≠ 61 := valToB64_not_pad _ h0
                  have hnp1 : valToB64 ((b.toNat % 4) * 16 + b1.toNat / 16) ≠ 61 := valToB64_not_pad _ h1
                  have hnp2 : valToB64 ((b1.toNat % 16) * 4 + b2.toNat / 64) ≠ 61 := valToB64_not_pad _ h2
                  have hnp3 : valToB64 (b2.toNat % 64) ≠ 61 := valToB64_not_pad _ h3
                  have hvalid0 : b64Valid (valToB64 (b.toNat / 4)) = true := valToB64_valid _ h0
                  have hvalid1 : b64Valid (valToB64 ((b.toNat % 4) * 16 + b1.toNat / 16)) = true := valToB64_valid _ h1
                  have hvalid2 : b64Valid (valToB64 ((b1.toNat % 16) * 4 + b2.toNat / 64)) = true := valToB64_valid _ h2
                  have hvalid3 : b64Valid (valToB64 (b2.toNat % 64)) = true := valToB64_valid _ h3
                  have hb0v : (b.toNat / 4) * 4 + (((b.toNat % 4) * 16 + b1.toNat / 16) / 16) = b.toNat := byte0 b.toNat b1.toNat hb hb1
                  have hb1v : (((b.toNat % 4) * 16 + b1.toNat / 16) % 16) * 16 + (((b1.toNat % 16) * 4 + b2.toNat / 64) / 4) = b1.toNat := by
                    have hmod16 : ((b.toNat % 4) * 16 + b1.toNat / 16) % 16 = b1.toNat / 16 := by
                      have h := Nat.add_mul_mod_self_right (b.toNat % 4) (b1.toNat / 16) 16
                      omega
                    have hdiv4 : ((b1.toNat % 16) * 4 + b2.toNat / 64) / 4 = b1.toNat % 16 := by
                      have h := Nat.add_mul_div_left (b2.toNat / 64) (b1.toNat % 16) (by decide : 0 < 4)
                      have hz : b2.toNat / 64 / 4 = 0 := Nat.div_eq_of_lt (by omega)
                      omega
                    have hsum := Nat.div_add_mod b1.toNat 16
                    omega
                  have hb2v : (((b1.toNat % 16) * 4 + b2.toNat / 64) % 4) * 64 + (b2.toNat % 64) = b2.toNat := byte2 b1.toNat b2.toNat hb1 hb2
                  have hcat : encode (b :: b1 :: b2 :: rest) = encode [b, b1, b2] ++ encode rest := by simp [encode]
                  rw [hcat]
                  show decode ([toByte (valToB64 (b.toNat / 4)), toByte (valToB64 ((b.toNat % 4) * 16 + b1.toNat / 16)),
                      toByte (valToB64 ((b1.toNat % 16) * 4 + b2.toNat / 64)), toByte (valToB64 (b2.toNat % 64))] ++ encode rest)
                      = some (b :: b1 :: b2 :: rest)
                  simp only [List.cons_append, List.nil_append]
                  rw [decode_cons4]
                  rw [toByte_valToB64 (b.toNat / 4) h0, toByte_valToB64 ((b.toNat % 4) * 16 + b1.toNat / 16) h1,
                      toByte_valToB64 ((b1.toNat % 16) * 4 + b2.toNat / 64) h2, toByte_valToB64 (b2.toNat % 64) h3]
                  rw [hvalid0, hvalid1]
                  rw [b64ToVal_valToB64 (b.toNat / 4) h0, b64ToVal_valToB64 ((b.toNat % 4) * 16 + b1.toNat / 16) h1]
                  simp only [hnp0, hnp1]
                  rw [hb0v]
                  rw [hvalid2]
                  rw [b64ToVal_valToB64 ((b1.toNat % 16) * 4 + b2.toNat / 64) h2]
                  simp only [hnp2]
                  rw [hb1v]
                  rw [hvalid3]
                  rw [b64ToVal_valToB64 (b2.toNat % 64) h3]
                  simp only [hnp3]
                  rw [hb2v]
                  simp
                  have hlen' : rest.length < n := by
                    have hlt : rest.length < (b :: b1 :: b2 :: rest).length := by
                      simp only [List.length_cons]
                      omega
                    rw [hlen] at hlt
                    exact hlt
                  rw [ih rest.length hlen' rest rfl]
                  simp [toByte, UInt8.ofNat_toNat])
  exact h bs rfl

end BaseN.Base64
