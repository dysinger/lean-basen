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

namespace BaseN.Base32

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

-- Nat-level codec

/-- Encode a byte list as base32 (Nat level), RFC 4648 §6 with `=` padding. -/
def encodeN (bs : List Nat) : List Nat :=
  match bs with
  | [] => []
  | v0 :: v1 :: v2 :: v3 :: v4 :: rest =>
    [valToB32 (v0 / 8), valToB32 ((v0 % 8) * 4 + v1 / 64),
     valToB32 ((v1 / 2) % 32), valToB32 ((v1 % 2) * 16 + v2 / 16),
     valToB32 ((v2 % 16) * 2 + v3 / 128), valToB32 ((v3 / 4) % 32),
     valToB32 ((v3 % 4) * 8 + v4 / 32), valToB32 (v4 % 32)] ++ encodeN rest
  | [v0] => [valToB32 (v0 / 8), valToB32 ((v0 % 8) * 4), 61, 61, 61, 61, 61, 61]
  | [v0, v1] => [valToB32 (v0 / 8), valToB32 ((v0 % 8) * 4 + v1 / 64),
                 valToB32 ((v1 / 2) % 32), valToB32 ((v1 % 2) * 16), 61, 61, 61, 61]
  | [v0, v1, v2] => [valToB32 (v0 / 8), valToB32 ((v0 % 8) * 4 + v1 / 64),
                     valToB32 ((v1 / 2) % 32), valToB32 ((v1 % 2) * 16 + v2 / 16),
                     valToB32 ((v2 % 16) * 2), 61, 61, 61]
  | [v0, v1, v2, v3] => [valToB32 (v0 / 8), valToB32 ((v0 % 8) * 4 + v1 / 64),
                         valToB32 ((v1 / 2) % 32), valToB32 ((v1 % 2) * 16 + v2 / 16),
                         valToB32 ((v2 % 16) * 2 + v3 / 128), valToB32 ((v3 / 4) % 32),
                         valToB32 ((v3 % 4) * 8), 61]

/-- Decode 8-char groups of base32 into bytes (`none` on bad input), Nat level. -/
def decodeN (bs : List Nat) : Option (List Nat) :=
  match bs with
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest =>
    if c0 = 61 || c1 = 61 then none
    else if ¬ b32Valid c0 || ¬ b32Valid c1 then none
    else
      let v0 := b32ToVal c0
      let v1 := b32ToVal c1
      let b0 := v0 * 8 + v1 / 4
      if c2 = 61 then
        if c3 = 61 && c4 = 61 && c5 = 61 && c6 = 61 && c7 = 61 then
          match decodeN rest with
          | some tl => some (b0 :: tl)
          | none => none
        else none
      else if ¬ b32Valid c2 then none
      else
        let v2 := b32ToVal c2
        if c3 = 61 then none
        else if ¬ b32Valid c3 then none
        else
          let v3 := b32ToVal c3
          let b1 := (v1 % 4) * 64 + v2 * 2 + v3 / 16
          if c4 = 61 then
            if c5 = 61 && c6 = 61 && c7 = 61 then
              match decodeN rest with
              | some tl => some (b0 :: b1 :: tl)
              | none => none
            else none
          else if ¬ b32Valid c4 then none
          else
            let v4 := b32ToVal c4
            let b2 := (v3 % 16) * 16 + v4 / 2
            if c5 = 61 then
              if c6 = 61 && c7 = 61 then
                match decodeN rest with
                | some tl => some (b0 :: b1 :: b2 :: tl)
                | none => none
              else none
            else if ¬ b32Valid c5 then none
            else
              let v5 := b32ToVal c5
              if c6 = 61 then none
              else if ¬ b32Valid c6 then none
              else
                let v6 := b32ToVal c6
                let b3 := (v4 % 2) * 128 + v5 * 4 + v6 / 8
                if c7 = 61 then
                  match decodeN rest with
                  | some tl => some (b0 :: b1 :: b2 :: b3 :: tl)
                  | none => none
                else if ¬ b32Valid c7 then none
                else
                  let v7 := b32ToVal c7
                  let b4 := (v6 % 8) * 32 + v7
                  match decodeN rest with
                  | some tl => some (b0 :: b1 :: b2 :: b3 :: b4 :: tl)
                  | none => none
  | _ => none

/-- `decodeN (c0::..::c7::rest)` — the 8-char block case, stated equationally. -/
theorem decodeN_cons8 (c0 c1 c2 c3 c4 c5 c6 c7 : Nat) (rest : List Nat) :
    decodeN (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) =
      if c0 = 61 || c1 = 61 then none
      else if ¬ b32Valid c0 || ¬ b32Valid c1 then none
      else
        let v0 := b32ToVal c0
        let v1 := b32ToVal c1
        let b0 := v0 * 8 + v1 / 4
        if c2 = 61 then
          if c3 = 61 && c4 = 61 && c5 = 61 && c6 = 61 && c7 = 61 then
            match decodeN rest with
            | some tl => some (b0 :: tl)
            | none => none
          else none
        else if ¬ b32Valid c2 then none
        else
          let v2 := b32ToVal c2
          if c3 = 61 then none
          else if ¬ b32Valid c3 then none
          else
            let v3 := b32ToVal c3
            let b1 := (v1 % 4) * 64 + v2 * 2 + v3 / 16
            if c4 = 61 then
              if c5 = 61 && c6 = 61 && c7 = 61 then
                match decodeN rest with
                | some tl => some (b0 :: b1 :: tl)
                | none => none
              else none
            else if ¬ b32Valid c4 then none
            else
              let v4 := b32ToVal c4
              let b2 := (v3 % 16) * 16 + v4 / 2
              if c5 = 61 then
                if c6 = 61 && c7 = 61 then
                  match decodeN rest with
                  | some tl => some (b0 :: b1 :: b2 :: tl)
                  | none => none
                else none
              else if ¬ b32Valid c5 then none
              else
                let v5 := b32ToVal c5
                if c6 = 61 then none
                else if ¬ b32Valid c6 then none
                else
                  let v6 := b32ToVal c6
                  let b3 := (v4 % 2) * 128 + v5 * 4 + v6 / 8
                  if c7 = 61 then
                    match decodeN rest with
                    | some tl => some (b0 :: b1 :: b2 :: b3 :: tl)
                    | none => none
                  else if ¬ b32Valid c7 then none
                  else
                    let v7 := b32ToVal c7
                    let b4 := (v6 % 8) * 32 + v7
                    match decodeN rest with
                    | some tl => some (b0 :: b1 :: b2 :: b3 :: b4 :: tl)
                    | none => none :=
  rfl

/-- `decodeN (encodeN [b0]) = some [b0]` (1-byte tail, six pads). -/
theorem decodeN_encodeN_single (b0 : Nat) (hb0 : b0 < 256) :
    decodeN (encodeN [b0]) = some [b0] := by
  have h0 : b0 / 8 ≤ 31 := by omega
  have h1 : (b0 % 8) * 4 ≤ 31 := by omega
  have hnp0 : valToB32 (b0 / 8) ≠ 61 := valToB32_not_pad (b0 / 8) h0
  have hnp1 : valToB32 ((b0 % 8) * 4) ≠ 61 := valToB32_not_pad ((b0 % 8) * 4) h1
  have hvalid0 : b32Valid (valToB32 (b0 / 8)) = true := valToB32_valid (b0 / 8) h0
  have hvalid1 : b32Valid (valToB32 ((b0 % 8) * 4)) = true := valToB32_valid ((b0 % 8) * 4) h1
  have hb0v : (b0 / 8) * 8 + (((b0 % 8) * 4) / 4) = b0 := by
    have hdiv4 : ((b0 % 8) * 4) / 4 = b0 % 8 := Nat.mul_div_left (b0 % 8) (by decide : 0 < 4)
    have hsum := Nat.div_add_mod b0 8
    omega
  unfold encodeN decodeN
  rw [hvalid0, hvalid1]
  rw [b32ToVal_valToB32 (b0 / 8) h0, b32ToVal_valToB32 ((b0 % 8) * 4) h1]
  simp only [hnp0, hnp1]
  rw [hb0v]
  simp [decodeN]

/-- `decodeN (encodeN [b0; b1]) = some [b0; b1]` (2-byte tail, four pads). -/
theorem decodeN_encodeN_pair (b0 b1 : Nat) (hb0 : b0 < 256) (hb1 : b1 < 256) :
    decodeN (encodeN [b0, b1]) = some [b0, b1] := by
  have h0 : b0 / 8 ≤ 31 := by omega
  have h1 : (b0 % 8) * 4 + b1 / 64 ≤ 31 := by omega
  have h2 : (b1 / 2) % 32 ≤ 31 := by omega
  have h3 : (b1 % 2) * 16 ≤ 31 := by omega
  have hnp0 : valToB32 (b0 / 8) ≠ 61 := valToB32_not_pad (b0 / 8) h0
  have hnp1 : valToB32 ((b0 % 8) * 4 + b1 / 64) ≠ 61 := valToB32_not_pad _ h1
  have hnp2 : valToB32 ((b1 / 2) % 32) ≠ 61 := valToB32_not_pad _ h2
  have hnp3 : valToB32 ((b1 % 2) * 16) ≠ 61 := valToB32_not_pad _ h3
  have hvalid0 : b32Valid (valToB32 (b0 / 8)) = true := valToB32_valid (b0 / 8) h0
  have hvalid1 : b32Valid (valToB32 ((b0 % 8) * 4 + b1 / 64)) = true := valToB32_valid _ h1
  have hvalid2 : b32Valid (valToB32 ((b1 / 2) % 32)) = true := valToB32_valid _ h2
  have hvalid3 : b32Valid (valToB32 ((b1 % 2) * 16)) = true := valToB32_valid _ h3
  have hb0v : (b0 / 8) * 8 + (((b0 % 8) * 4 + b1 / 64) / 4) = b0 := byte0 b0 b1 hb0 hb1
  have hb1v : (((b0 % 8) * 4 + b1 / 64) % 4) * 64 + (((b1 / 2) % 32) * 2) + (((b1 % 2) * 16) / 16) = b1 := by
    have h := byte1 b0 b1 0 hb0 hb1 (by decide)
    simpa using h
  unfold encodeN decodeN
  rw [hvalid0, hvalid1]
  rw [b32ToVal_valToB32 (b0 / 8) h0, b32ToVal_valToB32 ((b0 % 8) * 4 + b1 / 64) h1]
  simp only [hnp0, hnp1]
  rw [hb0v]
  rw [hvalid2, hvalid3]
  rw [b32ToVal_valToB32 ((b1 / 2) % 32) h2, b32ToVal_valToB32 ((b1 % 2) * 16) h3]
  simp only [hnp2, hnp3]
  rw [hb1v]
  simp [decodeN]

/-- `decodeN (encodeN [b0; b1; b2]) = some [b0; b1; b2]` (3-byte tail, three pads). -/
theorem decodeN_encodeN_triple (b0 b1 b2 : Nat) (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) :
    decodeN (encodeN [b0, b1, b2]) = some [b0, b1, b2] := by
  have h0 : b0 / 8 ≤ 31 := by omega
  have h1 : (b0 % 8) * 4 + b1 / 64 ≤ 31 := by omega
  have h2 : (b1 / 2) % 32 ≤ 31 := by omega
  have h3 : (b1 % 2) * 16 + b2 / 16 ≤ 31 := by omega
  have h4 : (b2 % 16) * 2 ≤ 31 := by omega
  have hvalid0 : b32Valid (valToB32 (b0 / 8)) = true := valToB32_valid (b0 / 8) h0
  have hvalid1 : b32Valid (valToB32 ((b0 % 8) * 4 + b1 / 64)) = true := valToB32_valid _ h1
  have hvalid2 : b32Valid (valToB32 ((b1 / 2) % 32)) = true := valToB32_valid _ h2
  have hvalid3 : b32Valid (valToB32 ((b1 % 2) * 16 + b2 / 16)) = true := valToB32_valid _ h3
  have hvalid4 : b32Valid (valToB32 ((b2 % 16) * 2)) = true := valToB32_valid _ h4
  have hnp0 : valToB32 (b0 / 8) ≠ 61 := valToB32_not_pad (b0 / 8) h0
  have hnp1 : valToB32 ((b0 % 8) * 4 + b1 / 64) ≠ 61 := valToB32_not_pad _ h1
  have hnp2 : valToB32 ((b1 / 2) % 32) ≠ 61 := valToB32_not_pad _ h2
  have hnp3 : valToB32 ((b1 % 2) * 16 + b2 / 16) ≠ 61 := valToB32_not_pad _ h3
  have hnp4 : valToB32 ((b2 % 16) * 2) ≠ 61 := valToB32_not_pad _ h4
  have hb0v : (b0 / 8) * 8 + (((b0 % 8) * 4 + b1 / 64) / 4) = b0 := byte0 b0 b1 hb0 hb1
  have hb1v : (((b0 % 8) * 4 + b1 / 64) % 4) * 64 + (((b1 / 2) % 32) * 2) + (((b1 % 2) * 16 + b2 / 16) / 16) = b1 := byte1 b0 b1 b2 hb0 hb1 hb2
  have hb2v : (((b1 % 2) * 16 + b2 / 16) % 16) * 16 + (((b2 % 16) * 2) / 2) = b2 := by
    have h := byte2 b1 b2 0 hb1 hb2 (by decide)
    simpa using h
  unfold encodeN decodeN
  rw [hvalid0, hvalid1]
  rw [b32ToVal_valToB32 (b0 / 8) h0, b32ToVal_valToB32 ((b0 % 8) * 4 + b1 / 64) h1]
  simp only [hnp0, hnp1]
  rw [hb0v]
  rw [hvalid2, hvalid3]
  rw [b32ToVal_valToB32 ((b1 / 2) % 32) h2, b32ToVal_valToB32 ((b1 % 2) * 16 + b2 / 16) h3]
  simp only [hnp2, hnp3]
  rw [hb1v]
  rw [hvalid4]
  rw [b32ToVal_valToB32 ((b2 % 16) * 2) h4]
  simp only [hnp4]
  rw [hb2v]
  simp [decodeN]

/-- `decodeN (encodeN [b0; b1; b2; b3]) = some [b0; b1; b2; b3]` (4-byte tail, one pad). -/
theorem decodeN_encodeN_quad (b0 b1 b2 b3 : Nat) (hb0 : b0 < 256) (hb1 : b1 < 256)
    (hb2 : b2 < 256) (hb3 : b3 < 256) :
    decodeN (encodeN [b0, b1, b2, b3]) = some [b0, b1, b2, b3] := by
  have h0 : b0 / 8 ≤ 31 := by omega
  have h1 : (b0 % 8) * 4 + b1 / 64 ≤ 31 := by omega
  have h2 : (b1 / 2) % 32 ≤ 31 := by omega
  have h3 : (b1 % 2) * 16 + b2 / 16 ≤ 31 := by omega
  have h4 : (b2 % 16) * 2 + b3 / 128 ≤ 31 := by omega
  have h5 : (b3 / 4) % 32 ≤ 31 := by omega
  have h6 : (b3 % 4) * 8 ≤ 31 := by omega
  have hvalid0 : b32Valid (valToB32 (b0 / 8)) = true := valToB32_valid (b0 / 8) h0
  have hvalid1 : b32Valid (valToB32 ((b0 % 8) * 4 + b1 / 64)) = true := valToB32_valid _ h1
  have hvalid2 : b32Valid (valToB32 ((b1 / 2) % 32)) = true := valToB32_valid _ h2
  have hvalid3 : b32Valid (valToB32 ((b1 % 2) * 16 + b2 / 16)) = true := valToB32_valid _ h3
  have hvalid4 : b32Valid (valToB32 ((b2 % 16) * 2 + b3 / 128)) = true := valToB32_valid _ h4
  have hvalid5 : b32Valid (valToB32 ((b3 / 4) % 32)) = true := valToB32_valid _ h5
  have hvalid6 : b32Valid (valToB32 ((b3 % 4) * 8)) = true := valToB32_valid _ h6
  have hnp0 : valToB32 (b0 / 8) ≠ 61 := valToB32_not_pad (b0 / 8) h0
  have hnp1 : valToB32 ((b0 % 8) * 4 + b1 / 64) ≠ 61 := valToB32_not_pad _ h1
  have hnp2 : valToB32 ((b1 / 2) % 32) ≠ 61 := valToB32_not_pad _ h2
  have hnp3 : valToB32 ((b1 % 2) * 16 + b2 / 16) ≠ 61 := valToB32_not_pad _ h3
  have hnp4 : valToB32 ((b2 % 16) * 2 + b3 / 128) ≠ 61 := valToB32_not_pad _ h4
  have hnp5 : valToB32 ((b3 / 4) % 32) ≠ 61 := valToB32_not_pad _ h5
  have hnp6 : valToB32 ((b3 % 4) * 8) ≠ 61 := valToB32_not_pad _ h6
  have hb0v : (b0 / 8) * 8 + (((b0 % 8) * 4 + b1 / 64) / 4) = b0 := byte0 b0 b1 hb0 hb1
  have hb1v : (((b0 % 8) * 4 + b1 / 64) % 4) * 64 + (((b1 / 2) % 32) * 2) + (((b1 % 2) * 16 + b2 / 16) / 16) = b1 := byte1 b0 b1 b2 hb0 hb1 hb2
  have hb2v : (((b1 % 2) * 16 + b2 / 16) % 16) * 16 + (((b2 % 16) * 2 + b3 / 128) / 2) = b2 := byte2 b1 b2 b3 hb1 hb2 hb3
  have hb3v : (((b2 % 16) * 2 + b3 / 128) % 2) * 128 + (((b3 / 4) % 32) * 4) + (((b3 % 4) * 8) / 8) = b3 := by
    have h := byte3 b2 b3 0 hb2 hb3 (by decide)
    simpa using h
  unfold encodeN decodeN
  rw [hvalid0, hvalid1]
  rw [b32ToVal_valToB32 (b0 / 8) h0, b32ToVal_valToB32 ((b0 % 8) * 4 + b1 / 64) h1]
  simp only [hnp0, hnp1]
  rw [hb0v]
  rw [hvalid2, hvalid3]
  rw [b32ToVal_valToB32 ((b1 / 2) % 32) h2, b32ToVal_valToB32 ((b1 % 2) * 16 + b2 / 16) h3]
  simp only [hnp2, hnp3]
  rw [hb1v]
  rw [hvalid4]
  rw [b32ToVal_valToB32 ((b2 % 16) * 2 + b3 / 128) h4]
  simp only [hnp4]
  rw [hb2v]
  rw [hvalid5, hvalid6]
  rw [b32ToVal_valToB32 ((b3 / 4) % 32) h5, b32ToVal_valToB32 ((b3 % 4) * 8) h6]
  simp only [hnp5, hnp6]
  rw [hb3v]
  simp [decodeN]

/-- `decodeN (encodeN [b0..b4]) = some [b0..b4]` (5-byte block, no pads). -/
theorem decodeN_encodeN_quintet (b0 b1 b2 b3 b4 : Nat) (hb0 : b0 < 256) (hb1 : b1 < 256)
    (hb2 : b2 < 256) (hb3 : b3 < 256) (hb4 : b4 < 256) :
    decodeN (encodeN [b0, b1, b2, b3, b4]) = some [b0, b1, b2, b3, b4] := by
  have h0 : b0 / 8 ≤ 31 := by omega
  have h1 : (b0 % 8) * 4 + b1 / 64 ≤ 31 := by omega
  have h2 : (b1 / 2) % 32 ≤ 31 := by omega
  have h3 : (b1 % 2) * 16 + b2 / 16 ≤ 31 := by omega
  have h4 : (b2 % 16) * 2 + b3 / 128 ≤ 31 := by omega
  have h5 : (b3 / 4) % 32 ≤ 31 := by omega
  have h6 : (b3 % 4) * 8 + b4 / 32 ≤ 31 := by omega
  have h7 : b4 % 32 ≤ 31 := by omega
  have hvalid0 : b32Valid (valToB32 (b0 / 8)) = true := valToB32_valid (b0 / 8) h0
  have hvalid1 : b32Valid (valToB32 ((b0 % 8) * 4 + b1 / 64)) = true := valToB32_valid _ h1
  have hvalid2 : b32Valid (valToB32 ((b1 / 2) % 32)) = true := valToB32_valid _ h2
  have hvalid3 : b32Valid (valToB32 ((b1 % 2) * 16 + b2 / 16)) = true := valToB32_valid _ h3
  have hvalid4 : b32Valid (valToB32 ((b2 % 16) * 2 + b3 / 128)) = true := valToB32_valid _ h4
  have hvalid5 : b32Valid (valToB32 ((b3 / 4) % 32)) = true := valToB32_valid _ h5
  have hvalid6 : b32Valid (valToB32 ((b3 % 4) * 8 + b4 / 32)) = true := valToB32_valid _ h6
  have hvalid7 : b32Valid (valToB32 (b4 % 32)) = true := valToB32_valid (b4 % 32) h7
  have hnp0 : valToB32 (b0 / 8) ≠ 61 := valToB32_not_pad (b0 / 8) h0
  have hnp1 : valToB32 ((b0 % 8) * 4 + b1 / 64) ≠ 61 := valToB32_not_pad _ h1
  have hnp2 : valToB32 ((b1 / 2) % 32) ≠ 61 := valToB32_not_pad _ h2
  have hnp3 : valToB32 ((b1 % 2) * 16 + b2 / 16) ≠ 61 := valToB32_not_pad _ h3
  have hnp4 : valToB32 ((b2 % 16) * 2 + b3 / 128) ≠ 61 := valToB32_not_pad _ h4
  have hnp5 : valToB32 ((b3 / 4) % 32) ≠ 61 := valToB32_not_pad _ h5
  have hnp6 : valToB32 ((b3 % 4) * 8 + b4 / 32) ≠ 61 := valToB32_not_pad _ h6
  have hnp7 : valToB32 (b4 % 32) ≠ 61 := valToB32_not_pad (b4 % 32) h7
  have hb0v : (b0 / 8) * 8 + (((b0 % 8) * 4 + b1 / 64) / 4) = b0 := byte0 b0 b1 hb0 hb1
  have hb1v : (((b0 % 8) * 4 + b1 / 64) % 4) * 64 + (((b1 / 2) % 32) * 2) + (((b1 % 2) * 16 + b2 / 16) / 16) = b1 := byte1 b0 b1 b2 hb0 hb1 hb2
  have hb2v : (((b1 % 2) * 16 + b2 / 16) % 16) * 16 + (((b2 % 16) * 2 + b3 / 128) / 2) = b2 := byte2 b1 b2 b3 hb1 hb2 hb3
  have hb3v : (((b2 % 16) * 2 + b3 / 128) % 2) * 128 + (((b3 / 4) % 32) * 4) + (((b3 % 4) * 8 + b4 / 32) / 8) = b3 := byte3 b2 b3 b4 hb2 hb3 hb4
  have hb4v : (((b3 % 4) * 8 + b4 / 32) % 8) * 32 + (b4 % 32) = b4 := byte4 b3 b4 hb3 hb4
  show decodeN ([valToB32 (b0 / 8), valToB32 ((b0 % 8) * 4 + b1 / 64),
      valToB32 ((b1 / 2) % 32), valToB32 ((b1 % 2) * 16 + b2 / 16),
      valToB32 ((b2 % 16) * 2 + b3 / 128), valToB32 ((b3 / 4) % 32),
      valToB32 ((b3 % 4) * 8 + b4 / 32), valToB32 (b4 % 32)]) = some [b0, b1, b2, b3, b4]
  unfold decodeN
  rw [hvalid0, hvalid1]
  rw [b32ToVal_valToB32 (b0 / 8) h0, b32ToVal_valToB32 ((b0 % 8) * 4 + b1 / 64) h1]
  simp only [hnp0, hnp1]
  rw [hb0v]
  rw [hvalid2, hvalid3]
  rw [b32ToVal_valToB32 ((b1 / 2) % 32) h2, b32ToVal_valToB32 ((b1 % 2) * 16 + b2 / 16) h3]
  simp only [hnp2, hnp3]
  rw [hb1v]
  rw [hvalid4]
  rw [b32ToVal_valToB32 ((b2 % 16) * 2 + b3 / 128) h4]
  simp only [hnp4]
  rw [hb2v]
  rw [hvalid5]
  rw [b32ToVal_valToB32 ((b3 / 4) % 32) h5]
  simp only [hnp5]
  simp only [hnp6]
  rw [hvalid6]
  rw [b32ToVal_valToB32 ((b3 % 4) * 8 + b4 / 32) h6]
  rw [hb3v]
  simp only [hnp7]
  rw [hvalid7]
  rw [b32ToVal_valToB32 (b4 % 32) h7]
  rw [hb4v]
  simp [decodeN]

/-- `decodeN (encodeN (b0::..::b4::rest)) = (b0::..::b4::·) <$> decodeN (encodeN rest)`. -/
theorem decodeN_block (b0 b1 b2 b3 b4 : Nat) (hb0 : b0 < 256) (hb1 : b1 < 256)
    (hb2 : b2 < 256) (hb3 : b3 < 256) (hb4 : b4 < 256) (rest : List Nat) :
    decodeN (encodeN (b0 :: b1 :: b2 :: b3 :: b4 :: rest)) =
      match decodeN (encodeN rest) with
      | some ys => some (b0 :: b1 :: b2 :: b3 :: b4 :: ys)
      | none => none := by
  have h0 : b0 / 8 ≤ 31 := by omega
  have h1 : (b0 % 8) * 4 + b1 / 64 ≤ 31 := by omega
  have h2 : (b1 / 2) % 32 ≤ 31 := by omega
  have h3 : (b1 % 2) * 16 + b2 / 16 ≤ 31 := by omega
  have h4 : (b2 % 16) * 2 + b3 / 128 ≤ 31 := by omega
  have h5 : (b3 / 4) % 32 ≤ 31 := by omega
  have h6 : (b3 % 4) * 8 + b4 / 32 ≤ 31 := by omega
  have h7 : b4 % 32 ≤ 31 := by omega
  have hvalid0 : b32Valid (valToB32 (b0 / 8)) = true := valToB32_valid (b0 / 8) h0
  have hvalid1 : b32Valid (valToB32 ((b0 % 8) * 4 + b1 / 64)) = true := valToB32_valid _ h1
  have hvalid2 : b32Valid (valToB32 ((b1 / 2) % 32)) = true := valToB32_valid _ h2
  have hvalid3 : b32Valid (valToB32 ((b1 % 2) * 16 + b2 / 16)) = true := valToB32_valid _ h3
  have hvalid4 : b32Valid (valToB32 ((b2 % 16) * 2 + b3 / 128)) = true := valToB32_valid _ h4
  have hvalid5 : b32Valid (valToB32 ((b3 / 4) % 32)) = true := valToB32_valid _ h5
  have hvalid6 : b32Valid (valToB32 ((b3 % 4) * 8 + b4 / 32)) = true := valToB32_valid _ h6
  have hvalid7 : b32Valid (valToB32 (b4 % 32)) = true := valToB32_valid (b4 % 32) h7
  have hnp0 : valToB32 (b0 / 8) ≠ 61 := valToB32_not_pad (b0 / 8) h0
  have hnp1 : valToB32 ((b0 % 8) * 4 + b1 / 64) ≠ 61 := valToB32_not_pad _ h1
  have hnp2 : valToB32 ((b1 / 2) % 32) ≠ 61 := valToB32_not_pad _ h2
  have hnp3 : valToB32 ((b1 % 2) * 16 + b2 / 16) ≠ 61 := valToB32_not_pad _ h3
  have hnp4 : valToB32 ((b2 % 16) * 2 + b3 / 128) ≠ 61 := valToB32_not_pad _ h4
  have hnp5 : valToB32 ((b3 / 4) % 32) ≠ 61 := valToB32_not_pad _ h5
  have hnp6 : valToB32 ((b3 % 4) * 8 + b4 / 32) ≠ 61 := valToB32_not_pad _ h6
  have hnp7 : valToB32 (b4 % 32) ≠ 61 := valToB32_not_pad (b4 % 32) h7
  have hb0v : (b0 / 8) * 8 + (((b0 % 8) * 4 + b1 / 64) / 4) = b0 := byte0 b0 b1 hb0 hb1
  have hb1v : (((b0 % 8) * 4 + b1 / 64) % 4) * 64 + (((b1 / 2) % 32) * 2) + (((b1 % 2) * 16 + b2 / 16) / 16) = b1 := byte1 b0 b1 b2 hb0 hb1 hb2
  have hb2v : (((b1 % 2) * 16 + b2 / 16) % 16) * 16 + (((b2 % 16) * 2 + b3 / 128) / 2) = b2 := byte2 b1 b2 b3 hb1 hb2 hb3
  have hb3v : (((b2 % 16) * 2 + b3 / 128) % 2) * 128 + (((b3 / 4) % 32) * 4) + (((b3 % 4) * 8 + b4 / 32) / 8) = b3 := byte3 b2 b3 b4 hb2 hb3 hb4
  have hb4v : (((b3 % 4) * 8 + b4 / 32) % 8) * 32 + (b4 % 32) = b4 := byte4 b3 b4 hb3 hb4
  show decodeN ([valToB32 (b0 / 8), valToB32 ((b0 % 8) * 4 + b1 / 64),
      valToB32 ((b1 / 2) % 32), valToB32 ((b1 % 2) * 16 + b2 / 16),
      valToB32 ((b2 % 16) * 2 + b3 / 128), valToB32 ((b3 / 4) % 32),
      valToB32 ((b3 % 4) * 8 + b4 / 32), valToB32 (b4 % 32)] ++ encodeN rest) =
    match decodeN (encodeN rest) with
    | some ys => some (b0 :: b1 :: b2 :: b3 :: b4 :: ys)
    | none => none
  simp only [List.cons_append, List.nil_append]
  rw [decodeN_cons8]
  rw [hvalid0, hvalid1]
  rw [b32ToVal_valToB32 (b0 / 8) h0, b32ToVal_valToB32 ((b0 % 8) * 4 + b1 / 64) h1]
  simp only [hnp0, hnp1]
  rw [hb0v]
  rw [hvalid2, hvalid3]
  rw [b32ToVal_valToB32 ((b1 / 2) % 32) h2, b32ToVal_valToB32 ((b1 % 2) * 16 + b2 / 16) h3]
  simp only [hnp2, hnp3]
  rw [hb1v]
  rw [hvalid4]
  rw [b32ToVal_valToB32 ((b2 % 16) * 2 + b3 / 128) h4]
  simp only [hnp4]
  rw [hb2v]
  rw [hvalid5]
  rw [b32ToVal_valToB32 ((b3 / 4) % 32) h5]
  simp only [hnp5]
  simp only [hnp6]
  rw [hvalid6]
  rw [b32ToVal_valToB32 ((b3 % 4) * 8 + b4 / 32) h6]
  rw [hb3v]
  simp only [hnp7]
  rw [hvalid7]
  rw [b32ToVal_valToB32 (b4 % 32) h7]
  rw [hb4v]
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
              | cons b2 bs =>
                  cases bs with
                  | nil => exact decodeN_encodeN_triple b b1 b2 (hys b (by simp)) (hys b1 (by simp)) (hys b2 (by simp))
                  | cons b3 bs =>
                      cases bs with
                      | nil => exact decodeN_encodeN_quad b b1 b2 b3 (hys b (by simp)) (hys b1 (by simp)) (hys b2 (by simp)) (hys b3 (by simp))
                      | cons b4 rest =>
                          have hb : b < 256 := hys b (by simp)
                          have hb1 : b1 < 256 := hys b1 (by simp)
                          have hb2 : b2 < 256 := hys b2 (by simp)
                          have hb3 : b3 < 256 := hys b3 (by simp)
                          have hb4 : b4 < 256 := hys b4 (by simp)
                          have hrest : ∀ x ∈ rest, x < 256 := by intro x hx; exact hys x (by simp [hx])
                          rw [decodeN_block b b1 b2 b3 b4 hb hb1 hb2 hb3 hb4 rest]
                          have hlen' : rest.length < n := by
                            have hlt : rest.length < (b :: b1 :: b2 :: b3 :: b4 :: rest).length := by
                              simp only [List.length_cons]
                              omega
                            rw [hlen] at hlt
                            exact hlt
                          rw [ih rest.length hlen' rest rfl hrest])
  exact h bs rfl hbs

-- UInt8 surface

private theorem toByte_valToB32 (i : Nat) (hi : i ≤ 31) :
    (toByte (valToB32 i)).toNat = valToB32 i := by
  unfold toByte
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToB32_lt_256 i hi)]

/-- Encode a byte list as base32, RFC 4648 §6 with `=` padding. -/
def encode (bs : List UInt8) : List UInt8 :=
  match bs with
  | [] => []
  | v0 :: v1 :: v2 :: v3 :: v4 :: rest =>
    [toByte (valToB32 (v0.toNat / 8)), toByte (valToB32 ((v0.toNat % 8) * 4 + v1.toNat / 64)),
     toByte (valToB32 ((v1.toNat / 2) % 32)), toByte (valToB32 ((v1.toNat % 2) * 16 + v2.toNat / 16)),
     toByte (valToB32 ((v2.toNat % 16) * 2 + v3.toNat / 128)), toByte (valToB32 ((v3.toNat / 4) % 32)),
     toByte (valToB32 ((v3.toNat % 4) * 8 + v4.toNat / 32)), toByte (valToB32 (v4.toNat % 32))] ++ encode rest
  | [v0] => [toByte (valToB32 (v0.toNat / 8)), toByte (valToB32 ((v0.toNat % 8) * 4)), 61, 61, 61, 61, 61, 61]
  | [v0, v1] => [toByte (valToB32 (v0.toNat / 8)), toByte (valToB32 ((v0.toNat % 8) * 4 + v1.toNat / 64)),
                 toByte (valToB32 ((v1.toNat / 2) % 32)), toByte (valToB32 ((v1.toNat % 2) * 16)), 61, 61, 61, 61]
  | [v0, v1, v2] => [toByte (valToB32 (v0.toNat / 8)), toByte (valToB32 ((v0.toNat % 8) * 4 + v1.toNat / 64)),
                     toByte (valToB32 ((v1.toNat / 2) % 32)), toByte (valToB32 ((v1.toNat % 2) * 16 + v2.toNat / 16)),
                     toByte (valToB32 ((v2.toNat % 16) * 2)), 61, 61, 61]
  | [v0, v1, v2, v3] => [toByte (valToB32 (v0.toNat / 8)), toByte (valToB32 ((v0.toNat % 8) * 4 + v1.toNat / 64)),
                         toByte (valToB32 ((v1.toNat / 2) % 32)), toByte (valToB32 ((v1.toNat % 2) * 16 + v2.toNat / 16)),
                         toByte (valToB32 ((v2.toNat % 16) * 2 + v3.toNat / 128)), toByte (valToB32 ((v3.toNat / 4) % 32)),
                         toByte (valToB32 ((v3.toNat % 4) * 8)), 61]

/-- Decode 8-char groups of base32 into bytes (`none` on bad input). -/
def decode (bs : List UInt8) : Option (List UInt8) :=
  match bs with
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest =>
    if c0.toNat = 61 || c1.toNat = 61 then none
    else if ¬ b32Valid c0.toNat || ¬ b32Valid c1.toNat then none
    else
      let v0 := b32ToVal c0.toNat
      let v1 := b32ToVal c1.toNat
      let b0 := v0 * 8 + v1 / 4
      if c2.toNat = 61 then
        if c3.toNat = 61 && c4.toNat = 61 && c5.toNat = 61 && c6.toNat = 61 && c7.toNat = 61 then
          match decode rest with
          | some tl => some (toByte b0 :: tl)
          | none => none
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
            if c5.toNat = 61 && c6.toNat = 61 && c7.toNat = 61 then
              match decode rest with
              | some tl => some (toByte b0 :: toByte b1 :: tl)
              | none => none
            else none
          else if ¬ b32Valid c4.toNat then none
          else
            let v4 := b32ToVal c4.toNat
            let b2 := (v3 % 16) * 16 + v4 / 2
            if c5.toNat = 61 then
              if c6.toNat = 61 && c7.toNat = 61 then
                match decode rest with
                | some tl => some (toByte b0 :: toByte b1 :: toByte b2 :: tl)
                | none => none
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
                  match decode rest with
                  | some tl => some (toByte b0 :: toByte b1 :: toByte b2 :: toByte b3 :: tl)
                  | none => none
                else if ¬ b32Valid c7.toNat then none
                else
                  let v7 := b32ToVal c7.toNat
                  let b4 := (v6 % 8) * 32 + v7
                  match decode rest with
                  | some tl => some (toByte b0 :: toByte b1 :: toByte b2 :: toByte b3 :: toByte b4 :: tl)
                  | none => none
  | _ => none

/-- `decode (c0::..::c7::rest)` — the 8-char block case (`UInt8`), stated equationally. -/
theorem decode_cons8 (c0 c1 c2 c3 c4 c5 c6 c7 : UInt8) (rest : List UInt8) :
    decode (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) =
      if c0.toNat = 61 || c1.toNat = 61 then none
      else if ¬ b32Valid c0.toNat || ¬ b32Valid c1.toNat then none
      else
        let v0 := b32ToVal c0.toNat
        let v1 := b32ToVal c1.toNat
        let b0 := v0 * 8 + v1 / 4
        if c2.toNat = 61 then
          if c3.toNat = 61 && c4.toNat = 61 && c5.toNat = 61 && c6.toNat = 61 && c7.toNat = 61 then
            match decode rest with
            | some tl => some (toByte b0 :: tl)
            | none => none
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
              if c5.toNat = 61 && c6.toNat = 61 && c7.toNat = 61 then
                match decode rest with
                | some tl => some (toByte b0 :: toByte b1 :: tl)
                | none => none
              else none
            else if ¬ b32Valid c4.toNat then none
            else
              let v4 := b32ToVal c4.toNat
              let b2 := (v3 % 16) * 16 + v4 / 2
              if c5.toNat = 61 then
                if c6.toNat = 61 && c7.toNat = 61 then
                  match decode rest with
                  | some tl => some (toByte b0 :: toByte b1 :: toByte b2 :: tl)
                  | none => none
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
                    match decode rest with
                    | some tl => some (toByte b0 :: toByte b1 :: toByte b2 :: toByte b3 :: tl)
                    | none => none
                  else if ¬ b32Valid c7.toNat then none
                  else
                    let v7 := b32ToVal c7.toNat
                    let b4 := (v6 % 8) * 32 + v7
                    match decode rest with
                    | some tl => some (toByte b0 :: toByte b1 :: toByte b2 :: toByte b3 :: toByte b4 :: tl)
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
              have h0 : b.toNat / 8 ≤ 31 := by omega
              have h1 : (b.toNat % 8) * 4 ≤ 31 := by omega
              have hnp0 : valToB32 (b.toNat / 8) ≠ 61 := valToB32_not_pad _ h0
              have hnp1 : valToB32 ((b.toNat % 8) * 4) ≠ 61 := valToB32_not_pad _ h1
              have hvalid0 : b32Valid (valToB32 (b.toNat / 8)) = true := valToB32_valid _ h0
              have hvalid1 : b32Valid (valToB32 ((b.toNat % 8) * 4)) = true := valToB32_valid _ h1
              have hsum : (b.toNat / 8) * 8 + (((b.toNat % 8) * 4) / 4) = b.toNat := byte0 b.toNat 0 hb (by decide)
              unfold encode decode
              rw [toByte_valToB32 (b.toNat / 8) h0, toByte_valToB32 ((b.toNat % 8) * 4) h1]
              rw [hvalid0, hvalid1]
              rw [b32ToVal_valToB32 (b.toNat / 8) h0, b32ToVal_valToB32 ((b.toNat % 8) * 4) h1]
              simp only [hnp0, hnp1]
              rw [hsum]
              simp [decode, toByte, UInt8.ofNat_toNat]
          | cons b1 bs =>
              cases bs with
              | nil =>
                  have hb : b.toNat < 256 := by simpa using UInt8.toNat_lt b
                  have hb1 : b1.toNat < 256 := by simpa using UInt8.toNat_lt b1
                  have h0 : b.toNat / 8 ≤ 31 := by omega
                  have h1 : (b.toNat % 8) * 4 + b1.toNat / 64 ≤ 31 := by omega
                  have h2 : (b1.toNat / 2) % 32 ≤ 31 := by omega
                  have h3 : (b1.toNat % 2) * 16 ≤ 31 := by omega
                  have hnp0 : valToB32 (b.toNat / 8) ≠ 61 := valToB32_not_pad _ h0
                  have hnp1 : valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64) ≠ 61 := valToB32_not_pad _ h1
                  have hnp2 : valToB32 ((b1.toNat / 2) % 32) ≠ 61 := valToB32_not_pad _ h2
                  have hnp3 : valToB32 ((b1.toNat % 2) * 16) ≠ 61 := valToB32_not_pad _ h3
                  have hvalid0 : b32Valid (valToB32 (b.toNat / 8)) = true := valToB32_valid _ h0
                  have hvalid1 : b32Valid (valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64)) = true := valToB32_valid _ h1
                  have hvalid2 : b32Valid (valToB32 ((b1.toNat / 2) % 32)) = true := valToB32_valid _ h2
                  have hvalid3 : b32Valid (valToB32 ((b1.toNat % 2) * 16)) = true := valToB32_valid _ h3
                  have hb0v : (b.toNat / 8) * 8 + (((b.toNat % 8) * 4 + b1.toNat / 64) / 4) = b.toNat := byte0 b.toNat b1.toNat hb hb1
                  have hb1v : (((b.toNat % 8) * 4 + b1.toNat / 64) % 4) * 64 + (((b1.toNat / 2) % 32) * 2) + (((b1.toNat % 2) * 16) / 16) = b1.toNat := by
                    have h := byte1 b.toNat b1.toNat 0 hb hb1 (by decide)
                    simpa using h
                  unfold encode decode
                  rw [toByte_valToB32 (b.toNat / 8) h0, toByte_valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64) h1,
                      toByte_valToB32 ((b1.toNat / 2) % 32) h2, toByte_valToB32 ((b1.toNat % 2) * 16) h3]
                  rw [hvalid0, hvalid1]
                  rw [b32ToVal_valToB32 (b.toNat / 8) h0, b32ToVal_valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64) h1]
                  simp only [hnp0, hnp1]
                  rw [hb0v]
                  rw [hvalid2, hvalid3]
                  rw [b32ToVal_valToB32 ((b1.toNat / 2) % 32) h2, b32ToVal_valToB32 ((b1.toNat % 2) * 16) h3]
                  simp only [hnp2, hnp3]
                  rw [hb1v]
                  simp [decode, toByte, UInt8.ofNat_toNat]
              | cons b2 bs =>
                  cases bs with
                  | nil =>
                      have hb : b.toNat < 256 := by simpa using UInt8.toNat_lt b
                      have hb1 : b1.toNat < 256 := by simpa using UInt8.toNat_lt b1
                      have hb2 : b2.toNat < 256 := by simpa using UInt8.toNat_lt b2
                      have h0 : b.toNat / 8 ≤ 31 := by omega
                      have h1 : (b.toNat % 8) * 4 + b1.toNat / 64 ≤ 31 := by omega
                      have h2 : (b1.toNat / 2) % 32 ≤ 31 := by omega
                      have h3 : (b1.toNat % 2) * 16 + b2.toNat / 16 ≤ 31 := by omega
                      have h4 : (b2.toNat % 16) * 2 ≤ 31 := by omega
                      have hnp0 : valToB32 (b.toNat / 8) ≠ 61 := valToB32_not_pad _ h0
                      have hnp1 : valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64) ≠ 61 := valToB32_not_pad _ h1
                      have hnp2 : valToB32 ((b1.toNat / 2) % 32) ≠ 61 := valToB32_not_pad _ h2
                      have hnp3 : valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) ≠ 61 := valToB32_not_pad _ h3
                      have hnp4 : valToB32 ((b2.toNat % 16) * 2) ≠ 61 := valToB32_not_pad _ h4
                      have hvalid0 : b32Valid (valToB32 (b.toNat / 8)) = true := valToB32_valid _ h0
                      have hvalid1 : b32Valid (valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64)) = true := valToB32_valid _ h1
                      have hvalid2 : b32Valid (valToB32 ((b1.toNat / 2) % 32)) = true := valToB32_valid _ h2
                      have hvalid3 : b32Valid (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)) = true := valToB32_valid _ h3
                      have hvalid4 : b32Valid (valToB32 ((b2.toNat % 16) * 2)) = true := valToB32_valid _ h4
                      have hb0v : (b.toNat / 8) * 8 + (((b.toNat % 8) * 4 + b1.toNat / 64) / 4) = b.toNat := byte0 b.toNat b1.toNat hb hb1
                      have hb1v : (((b.toNat % 8) * 4 + b1.toNat / 64) % 4) * 64 + (((b1.toNat / 2) % 32) * 2) + (((b1.toNat % 2) * 16 + b2.toNat / 16) / 16) = b1.toNat := byte1 b.toNat b1.toNat b2.toNat hb hb1 hb2
                      have hb2v : (((b1.toNat % 2) * 16 + b2.toNat / 16) % 16) * 16 + (((b2.toNat % 16) * 2) / 2) = b2.toNat := by
                        have h := byte2 b1.toNat b2.toNat 0 hb1 hb2 (by decide)
                        simpa using h
                      unfold encode decode
                      rw [toByte_valToB32 (b.toNat / 8) h0, toByte_valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64) h1,
                          toByte_valToB32 ((b1.toNat / 2) % 32) h2, toByte_valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) h3,
                          toByte_valToB32 ((b2.toNat % 16) * 2) h4]
                      rw [hvalid0, hvalid1]
                      rw [b32ToVal_valToB32 (b.toNat / 8) h0, b32ToVal_valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64) h1]
                      simp only [hnp0, hnp1]
                      rw [hb0v]
                      rw [hvalid2, hvalid3]
                      rw [b32ToVal_valToB32 ((b1.toNat / 2) % 32) h2, b32ToVal_valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) h3]
                      simp only [hnp2, hnp3]
                      rw [hb1v]
                      rw [hvalid4]
                      rw [b32ToVal_valToB32 ((b2.toNat % 16) * 2) h4]
                      simp only [hnp4]
                      rw [hb2v]
                      simp [decode, toByte, UInt8.ofNat_toNat]
                  | cons b3 bs =>
                      cases bs with
                      | nil =>
                          have hb : b.toNat < 256 := by simpa using UInt8.toNat_lt b
                          have hb1 : b1.toNat < 256 := by simpa using UInt8.toNat_lt b1
                          have hb2 : b2.toNat < 256 := by simpa using UInt8.toNat_lt b2
                          have hb3 : b3.toNat < 256 := by simpa using UInt8.toNat_lt b3
                          have h0 : b.toNat / 8 ≤ 31 := by omega
                          have h1 : (b.toNat % 8) * 4 + b1.toNat / 64 ≤ 31 := by omega
                          have h2 : (b1.toNat / 2) % 32 ≤ 31 := by omega
                          have h3 : (b1.toNat % 2) * 16 + b2.toNat / 16 ≤ 31 := by omega
                          have h4 : (b2.toNat % 16) * 2 + b3.toNat / 128 ≤ 31 := by omega
                          have h5 : (b3.toNat / 4) % 32 ≤ 31 := by omega
                          have h6 : (b3.toNat % 4) * 8 ≤ 31 := by omega
                          have hnp0 : valToB32 (b.toNat / 8) ≠ 61 := valToB32_not_pad _ h0
                          have hnp1 : valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64) ≠ 61 := valToB32_not_pad _ h1
                          have hnp2 : valToB32 ((b1.toNat / 2) % 32) ≠ 61 := valToB32_not_pad _ h2
                          have hnp3 : valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) ≠ 61 := valToB32_not_pad _ h3
                          have hnp4 : valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128) ≠ 61 := valToB32_not_pad _ h4
                          have hnp5 : valToB32 ((b3.toNat / 4) % 32) ≠ 61 := valToB32_not_pad _ h5
                          have hnp6 : valToB32 ((b3.toNat % 4) * 8) ≠ 61 := valToB32_not_pad _ h6
                          have hvalid0 : b32Valid (valToB32 (b.toNat / 8)) = true := valToB32_valid _ h0
                          have hvalid1 : b32Valid (valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64)) = true := valToB32_valid _ h1
                          have hvalid2 : b32Valid (valToB32 ((b1.toNat / 2) % 32)) = true := valToB32_valid _ h2
                          have hvalid3 : b32Valid (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)) = true := valToB32_valid _ h3
                          have hvalid4 : b32Valid (valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128)) = true := valToB32_valid _ h4
                          have hvalid5 : b32Valid (valToB32 ((b3.toNat / 4) % 32)) = true := valToB32_valid _ h5
                          have hvalid6 : b32Valid (valToB32 ((b3.toNat % 4) * 8)) = true := valToB32_valid _ h6
                          have hb0v : (b.toNat / 8) * 8 + (((b.toNat % 8) * 4 + b1.toNat / 64) / 4) = b.toNat := byte0 b.toNat b1.toNat hb hb1
                          have hb1v : (((b.toNat % 8) * 4 + b1.toNat / 64) % 4) * 64 + (((b1.toNat / 2) % 32) * 2) + (((b1.toNat % 2) * 16 + b2.toNat / 16) / 16) = b1.toNat := byte1 b.toNat b1.toNat b2.toNat hb hb1 hb2
                          have hb2v : (((b1.toNat % 2) * 16 + b2.toNat / 16) % 16) * 16 + (((b2.toNat % 16) * 2 + b3.toNat / 128) / 2) = b2.toNat := byte2 b1.toNat b2.toNat b3.toNat hb1 hb2 hb3
                          have hb3v : (((b2.toNat % 16) * 2 + b3.toNat / 128) % 2) * 128 + (((b3.toNat / 4) % 32) * 4) + (((b3.toNat % 4) * 8) / 8) = b3.toNat := by
                            have h := byte3 b2.toNat b3.toNat 0 hb2 hb3 (by decide)
                            simpa using h
                          unfold encode decode
                          rw [toByte_valToB32 (b.toNat / 8) h0, toByte_valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64) h1,
                              toByte_valToB32 ((b1.toNat / 2) % 32) h2, toByte_valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) h3,
                              toByte_valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128) h4, toByte_valToB32 ((b3.toNat / 4) % 32) h5,
                              toByte_valToB32 ((b3.toNat % 4) * 8) h6]
                          rw [hvalid0, hvalid1]
                          rw [b32ToVal_valToB32 (b.toNat / 8) h0, b32ToVal_valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64) h1]
                          simp only [hnp0, hnp1]
                          rw [hb0v]
                          rw [hvalid2, hvalid3]
                          rw [b32ToVal_valToB32 ((b1.toNat / 2) % 32) h2, b32ToVal_valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) h3]
                          simp only [hnp2, hnp3]
                          rw [hb1v]
                          rw [hvalid4]
                          rw [b32ToVal_valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128) h4]
                          simp only [hnp4]
                          rw [hb2v]
                          rw [hvalid5, hvalid6]
                          rw [b32ToVal_valToB32 ((b3.toNat / 4) % 32) h5, b32ToVal_valToB32 ((b3.toNat % 4) * 8) h6]
                          simp only [hnp5, hnp6]
                          rw [hb3v]
                          simp [decode, toByte, UInt8.ofNat_toNat]
                      | cons b4 rest =>
                          have hb : b.toNat < 256 := by simpa using UInt8.toNat_lt b
                          have hb1 : b1.toNat < 256 := by simpa using UInt8.toNat_lt b1
                          have hb2 : b2.toNat < 256 := by simpa using UInt8.toNat_lt b2
                          have hb3 : b3.toNat < 256 := by simpa using UInt8.toNat_lt b3
                          have hb4 : b4.toNat < 256 := by simpa using UInt8.toNat_lt b4
                          have h0 : b.toNat / 8 ≤ 31 := by omega
                          have h1 : (b.toNat % 8) * 4 + b1.toNat / 64 ≤ 31 := by omega
                          have h2 : (b1.toNat / 2) % 32 ≤ 31 := by omega
                          have h3 : (b1.toNat % 2) * 16 + b2.toNat / 16 ≤ 31 := by omega
                          have h4 : (b2.toNat % 16) * 2 + b3.toNat / 128 ≤ 31 := by omega
                          have h5 : (b3.toNat / 4) % 32 ≤ 31 := by omega
                          have h6 : (b3.toNat % 4) * 8 + b4.toNat / 32 ≤ 31 := by omega
                          have h7 : b4.toNat % 32 ≤ 31 := by omega
                          have hnp0 : valToB32 (b.toNat / 8) ≠ 61 := valToB32_not_pad _ h0
                          have hnp1 : valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64) ≠ 61 := valToB32_not_pad _ h1
                          have hnp2 : valToB32 ((b1.toNat / 2) % 32) ≠ 61 := valToB32_not_pad _ h2
                          have hnp3 : valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) ≠ 61 := valToB32_not_pad _ h3
                          have hnp4 : valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128) ≠ 61 := valToB32_not_pad _ h4
                          have hnp5 : valToB32 ((b3.toNat / 4) % 32) ≠ 61 := valToB32_not_pad _ h5
                          have hnp6 : valToB32 ((b3.toNat % 4) * 8 + b4.toNat / 32) ≠ 61 := valToB32_not_pad _ h6
                          have hnp7 : valToB32 (b4.toNat % 32) ≠ 61 := valToB32_not_pad _ h7
                          have hvalid0 : b32Valid (valToB32 (b.toNat / 8)) = true := valToB32_valid _ h0
                          have hvalid1 : b32Valid (valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64)) = true := valToB32_valid _ h1
                          have hvalid2 : b32Valid (valToB32 ((b1.toNat / 2) % 32)) = true := valToB32_valid _ h2
                          have hvalid3 : b32Valid (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)) = true := valToB32_valid _ h3
                          have hvalid4 : b32Valid (valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128)) = true := valToB32_valid _ h4
                          have hvalid5 : b32Valid (valToB32 ((b3.toNat / 4) % 32)) = true := valToB32_valid _ h5
                          have hvalid6 : b32Valid (valToB32 ((b3.toNat % 4) * 8 + b4.toNat / 32)) = true := valToB32_valid _ h6
                          have hvalid7 : b32Valid (valToB32 (b4.toNat % 32)) = true := valToB32_valid _ h7
                          have hb0v : (b.toNat / 8) * 8 + (((b.toNat % 8) * 4 + b1.toNat / 64) / 4) = b.toNat := byte0 b.toNat b1.toNat hb hb1
                          have hb1v : (((b.toNat % 8) * 4 + b1.toNat / 64) % 4) * 64 + (((b1.toNat / 2) % 32) * 2) + (((b1.toNat % 2) * 16 + b2.toNat / 16) / 16) = b1.toNat := byte1 b.toNat b1.toNat b2.toNat hb hb1 hb2
                          have hb2v : (((b1.toNat % 2) * 16 + b2.toNat / 16) % 16) * 16 + (((b2.toNat % 16) * 2 + b3.toNat / 128) / 2) = b2.toNat := byte2 b1.toNat b2.toNat b3.toNat hb1 hb2 hb3
                          have hb3v : (((b2.toNat % 16) * 2 + b3.toNat / 128) % 2) * 128 + (((b3.toNat / 4) % 32) * 4) + (((b3.toNat % 4) * 8 + b4.toNat / 32) / 8) = b3.toNat := byte3 b2.toNat b3.toNat b4.toNat hb2 hb3 hb4
                          have hb4v : (((b3.toNat % 4) * 8 + b4.toNat / 32) % 8) * 32 + (b4.toNat % 32) = b4.toNat := byte4 b3.toNat b4.toNat hb3 hb4
                          have hcat : encode (b :: b1 :: b2 :: b3 :: b4 :: rest) = encode [b, b1, b2, b3, b4] ++ encode rest := by simp [encode]
                          rw [hcat]
                          show decode ([toByte (valToB32 (b.toNat / 8)), toByte (valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64)),
                              toByte (valToB32 ((b1.toNat / 2) % 32)), toByte (valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)),
                              toByte (valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128)), toByte (valToB32 ((b3.toNat / 4) % 32)),
                              toByte (valToB32 ((b3.toNat % 4) * 8 + b4.toNat / 32)), toByte (valToB32 (b4.toNat % 32))] ++ encode rest)
                              = some (b :: b1 :: b2 :: b3 :: b4 :: rest)
                          simp only [List.cons_append, List.nil_append]
                          rw [decode_cons8]
                          rw [toByte_valToB32 (b.toNat / 8) h0, toByte_valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64) h1,
                              toByte_valToB32 ((b1.toNat / 2) % 32) h2, toByte_valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) h3,
                              toByte_valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128) h4, toByte_valToB32 ((b3.toNat / 4) % 32) h5,
                              toByte_valToB32 ((b3.toNat % 4) * 8 + b4.toNat / 32) h6, toByte_valToB32 (b4.toNat % 32) h7]
                          rw [hvalid0, hvalid1]
                          rw [b32ToVal_valToB32 (b.toNat / 8) h0, b32ToVal_valToB32 ((b.toNat % 8) * 4 + b1.toNat / 64) h1]
                          simp only [hnp0, hnp1]
                          rw [hb0v]
                          rw [hvalid2, hvalid3]
                          rw [b32ToVal_valToB32 ((b1.toNat / 2) % 32) h2, b32ToVal_valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16) h3]
                          simp only [hnp2, hnp3]
                          rw [hb1v]
                          rw [hvalid4]
                          rw [b32ToVal_valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128) h4]
                          simp only [hnp4]
                          rw [hb2v]
                          rw [hvalid5]
                          rw [b32ToVal_valToB32 ((b3.toNat / 4) % 32) h5]
                          simp only [hnp5]
                          simp only [hnp6]
                          rw [hvalid6]
                          rw [b32ToVal_valToB32 ((b3.toNat % 4) * 8 + b4.toNat / 32) h6]
                          rw [hb3v]
                          simp only [hnp7]
                          rw [hvalid7]
                          rw [b32ToVal_valToB32 (b4.toNat % 32) h7]
                          rw [hb4v]
                          simp
                          have hlen' : rest.length < n := by
                            have hlt : rest.length < (b :: b1 :: b2 :: b3 :: b4 :: rest).length := by
                              simp only [List.length_cons]
                              omega
                            rw [hlen] at hlt
                            exact hlt
                          rw [ih rest.length hlen' rest rfl]
                          simp [toByte, UInt8.ofNat_toNat])
  exact h bs rfl

end BaseN.Base32
