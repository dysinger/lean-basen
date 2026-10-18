/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# BaseN.Base8

Octal encoding: each byte encodes as **three** zero-padded octal digits
(`000`-`377`), MSB-first (`v/64`, `(v/8)%8`, `v%8`).  Three octal digits span
`0..511`, exceeding a byte, so decoding rejects a triple with value `> 255`.

This is not an RFC encoding (RFC 4648 covers only 16/32/64); its semantics are
defined by this package's spec: "three octal digits per byte", matching
`fstar-basen`'s `Data.BaseN.Base08`.  Digit math is `Nat`-level as in `Base16`;
the alphabet is ASCII `0-7` (48-55), all `< 256`.
-/

namespace BaseN.Base8

/-- `valToOct d` — the octal digit character for `d ∈ {0..7}`. -/
def valToOct (d : Nat) : Nat := 48 + d

/-- `octToVal e` — the octal value of a digit, or `8` if invalid (`0-7`). -/
def octToVal (e : Nat) : Nat :=
  if e ≤ 55 then if 48 ≤ e then e - 48 else 8 else 8

/-- `octValid e` — `true` iff `e` is an octal digit. -/
def octValid (e : Nat) : Bool := decide (octToVal e ≤ 7)

/-- `toByte n` — the `UInt8` embedding (all produced bytes are `< 256`). -/
def toByte (n : Nat) : UInt8 := UInt8.ofNat n

/-- `octToVal (valToOct d) = d` — the digit ↔ value bijection. -/
theorem octToVal_valToOct (d : Nat) (hd : d ≤ 7) :
    octToVal (valToOct d) = d := by
  have hd0 : 0 ≤ d := by omega
  unfold octToVal valToOct
  have h1 : 48 + d ≤ 55 := by omega
  have h2 : 48 ≤ 48 + d := by omega
  simp only [h1, ite_true, h2, ite_true]
  omega

/-- `valToOct d` is a valid octal digit. -/
theorem valToOct_valid (d : Nat) (hd : d ≤ 7) : octValid (valToOct d) = true := by
  unfold octValid
  apply decide_eq_true
  rw [octToVal_valToOct d hd]
  exact hd

/-- `valToOct d < 256` — every octal digit is a single byte. -/
theorem valToOct_lt_256 (d : Nat) (hd : d ≤ 7) : valToOct d < 256 := by
  unfold valToOct
  omega

-- Nat-level codec

/-- Encode each byte as three zero-padded octal digits (Nat level). -/
def encodeN (bs : List Nat) : List Nat :=
  bs.flatMap (fun b => [valToOct (b / 64), valToOct ((b / 8) % 8), valToOct (b % 8)])

/-- Decode triples of octal digits into bytes (`none` on bad input or overflow). -/
def decodeN (bs : List Nat) : Option (List Nat) :=
  match bs with
  | [] => some []
  | d0 :: d1 :: d2 :: rest =>
    if octValid d0 then
    if octValid d1 then
    if octValid d2 then
      let n := octToVal d0 * 64 + octToVal d1 * 8 + octToVal d2
      if n ≤ 255 then
        match decodeN rest with
        | some tl => some (n :: tl)
        | none => none
      else none
    else none
    else none
    else none
  | _ => none

/-- `decodeN (encodeN [b]) = some [b]`. -/
theorem decodeN_encodeN_single (b : Nat) (hb : b < 256) :
    decodeN (encodeN [b]) = some [b] := by
  have h0 : b / 64 ≤ 7 := by omega
  have h1 : (b / 8) % 8 ≤ 7 := by omega
  have h2 : b % 8 ≤ 7 := by omega
  have hle : b / 64 * 64 + (b / 8) % 8 * 8 + b % 8 ≤ 255 := by
    have hdiv64 := Nat.div_add_mod b 64
    have hdiv8 := Nat.div_add_mod b 8
    omega
  simp [encodeN, decodeN]
  rw [valToOct_valid (b / 64) h0, valToOct_valid ((b / 8) % 8) h1, valToOct_valid (b % 8) h2]
  rw [octToVal_valToOct (b / 64) h0, octToVal_valToOct ((b / 8) % 8) h1, octToVal_valToOct (b % 8) h2]
  have hsum : b / 64 * 64 + (b / 8) % 8 * 8 + b % 8 = b := by omega
  have hle' : b / 64 * 64 + (b / 8) % 8 * 8 + b % 8 ≤ 255 := by omega
  rw [hsum]
  have hb_le : b ≤ 255 := by omega
  simp [hb_le]

/-- `decodeN (encodeN [b] ++ xs) = (b :: ·) <$> decodeN xs`. -/
theorem decodeN_block (b : Nat) (hb : b < 256) (xs : List Nat) :
    decodeN (encodeN [b] ++ xs) =
      match decodeN xs with
      | some ys => some (b :: ys)
      | none => none := by
  have h0 : b / 64 ≤ 7 := by omega
  have h1 : (b / 8) % 8 ≤ 7 := by omega
  have h2 : b % 8 ≤ 7 := by omega
  simp [encodeN, decodeN]
  rw [valToOct_valid (b / 64) h0, valToOct_valid ((b / 8) % 8) h1, valToOct_valid (b % 8) h2]
  rw [octToVal_valToOct (b / 64) h0, octToVal_valToOct ((b / 8) % 8) h1, octToVal_valToOct (b % 8) h2]
  have hsum : b / 64 * 64 + (b / 8) % 8 * 8 + b % 8 = b := by omega
  have hle' : b / 64 * 64 + (b / 8) % 8 * 8 + b % 8 ≤ 255 := by omega
  rw [hsum]
  have hb_le : b ≤ 255 := by omega
  simp [hb_le]

/-- `decodeN (encodeN bs) = some bs`, for byte lists. -/
theorem roundtripN (bs : List Nat) :
    (∀ b ∈ bs, b < 256) → decodeN (encodeN bs) = some bs := by
  intro hbs
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      have hb : b < 256 := hbs b (by simp)
      have htail : ∀ x ∈ bs, x < 256 := by intro x hx; exact hbs x (by simp [hx])
      have hcat : encodeN (b :: bs) = encodeN [b] ++ encodeN bs := by simp [encodeN]
      rw [hcat, decodeN_block b hb (encodeN bs), ih htail]

-- UInt8 surface

private theorem toByte_valToOct (d : Nat) (hd : d ≤ 7) :
    (toByte (valToOct d)).toNat = valToOct d := by
  unfold toByte
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToOct_lt_256 d hd)]

/-- Encode each byte as three zero-padded octal digits. -/
def encode (bs : List UInt8) : List UInt8 :=
  bs.flatMap (fun b => [toByte (valToOct (b.toNat / 64)), toByte (valToOct ((b.toNat / 8) % 8)), toByte (valToOct (b.toNat % 8))])

/-- Decode triples of octal digits into bytes. -/
def decode (bs : List UInt8) : Option (List UInt8) :=
  match bs with
  | [] => some []
  | d0 :: d1 :: d2 :: rest =>
    if octValid d0.toNat then
    if octValid d1.toNat then
    if octValid d2.toNat then
      let n := octToVal d0.toNat * 64 + octToVal d1.toNat * 8 + octToVal d2.toNat
      if n ≤ 255 then
        match decode rest with
        | some tl => some (toByte n :: tl)
        | none => none
      else none
    else none
    else none
    else none
  | _ => none

/-- `decode (encode bs) = some bs` — the full roundtrip, `UInt8` level. -/
theorem roundtrip (bs : List UInt8) :
    decode (encode bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      have hlt : b.toNat < 256 := by simpa using UInt8.toNat_lt b
      have h0 : b.toNat / 64 ≤ 7 := by omega
      have h1 : (b.toNat / 8) % 8 ≤ 7 := by omega
      have h2 : b.toNat % 8 ≤ 7 := by omega
      have hcat : encode (b :: bs) = encode [b] ++ encode bs := by simp [encode]
      rw [hcat]
      change decode (encode [b] ++ encode bs) = some (b :: bs)
      change decode ([toByte (valToOct (b.toNat / 64)), toByte (valToOct ((b.toNat / 8) % 8)), toByte (valToOct (b.toNat % 8))] ++ encode bs) = some (b :: bs)
      simp [decode]
      rw [toByte_valToOct (b.toNat / 64) h0, toByte_valToOct ((b.toNat / 8) % 8) h1, toByte_valToOct (b.toNat % 8) h2]
      rw [valToOct_valid (b.toNat / 64) h0, valToOct_valid ((b.toNat / 8) % 8) h1, valToOct_valid (b.toNat % 8) h2]
      rw [octToVal_valToOct (b.toNat / 64) h0, octToVal_valToOct ((b.toNat / 8) % 8) h1, octToVal_valToOct (b.toNat % 8) h2]
      have hsum : b.toNat / 64 * 64 + (b.toNat / 8) % 8 * 8 + b.toNat % 8 = b.toNat := by omega
      have hle : b.toNat / 64 * 64 + (b.toNat / 8) % 8 * 8 + b.toNat % 8 ≤ 255 := by omega
      rw [hsum]
      have hb_le : b.toNat ≤ 255 := by omega
      simp [hb_le]
      rw [ih]
      simp [toByte, UInt8.ofNat_toNat]

end BaseN.Base8
