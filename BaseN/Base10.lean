/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# BaseN.Base10

Decimal encoding, **byte-oriented** and **sign-free**: each byte encodes as
**three zero-padded decimal digits** (`000`-`255`), MSB-first (`v/100`,
`(v/10)%10`, `v%10`).  Three decimal digits span `0..999`, exceeding a byte, so
decoding rejects a triple with value `> 255`.

Not an RFC encoding; semantics are defined by this package's spec (see design
D3: "decimal digit math, byte-oriented, no sign").  The three-digit fixed width
is what makes `decode (encode bs) = some bs` hold unconditionally: a
variable-width decimal (whole-byte-list-as-one-number) would drop leading zero
bytes and break the roundtrip.  Alphabet is ASCII `0-9` (48-57).
-/

namespace BaseN.Base10

/-- `digVal e` — the decimal value of a `0-9` character, or `10` if invalid. -/
def digVal (e : Nat) : Nat :=
  if e ≤ 57 then if 48 ≤ e then e - 48 else 10 else 10

/-- `valToDig d` — the `0-9` character for digit `d`. -/
def valToDig (d : Nat) : Nat := 48 + d

/-- `digValid e` — `true` iff `e` is a decimal digit (`0-9`). -/
def digValid (e : Nat) : Bool := decide (digVal e ≤ 9)

/-- `toByte n` — the `UInt8` embedding. -/
def toByte (n : Nat) : UInt8 := UInt8.ofNat n

theorem digVal_valToDig (d : Nat) (hd : d ≤ 9) :
    digVal (valToDig d) = d := by
  unfold digVal valToDig
  have h1 : 48 + d ≤ 57 := by omega
  have h2 : 48 ≤ 48 + d := by omega
  simp only [h1, ite_true, h2, ite_true]
  omega

theorem valToDig_valid (d : Nat) (hd : d ≤ 9) : digValid (valToDig d) = true := by
  unfold digValid
  apply decide_eq_true
  rw [digVal_valToDig d hd]
  exact hd

theorem valToDig_lt_256 (d : Nat) (hd : d ≤ 9) : valToDig d < 256 := by
  unfold valToDig
  omega

/-- Encode each byte as three zero-padded decimal digits (Nat level). -/
def encodeN (bs : List Nat) : List Nat :=
  bs.flatMap (fun b => [valToDig (b / 100), valToDig ((b / 10) % 10), valToDig (b % 10)])

/-- Decode triples of decimal digits into bytes (`none` on bad input or overflow). -/
def decodeN (bs : List Nat) : Option (List Nat) :=
  match bs with
  | [] => some []
  | d0 :: d1 :: d2 :: rest =>
    if digValid d0 && digValid d1 && digValid d2 then
      let n := digVal d0 * 100 + digVal d1 * 10 + digVal d2
      if n ≤ 255 then
        match decodeN rest with
        | some tl => some (n :: tl)
        | none => none
      else none
    else none
  | _ => none

/-- `decodeN (encodeN [b]) = some [b]`. -/
theorem decodeN_encodeN_single (b : Nat) (hb : b < 256) :
    decodeN (encodeN [b]) = some [b] := by
  have h0 : b / 100 ≤ 9 := by omega
  have h1 : (b / 10) % 10 ≤ 9 := by omega
  have h2 : b % 10 ≤ 9 := by omega
  simp [encodeN, decodeN]
  rw [valToDig_valid (b / 100) h0, valToDig_valid ((b / 10) % 10) h1, valToDig_valid (b % 10) h2]
  rw [digVal_valToDig (b / 100) h0, digVal_valToDig ((b / 10) % 10) h1, digVal_valToDig (b % 10) h2]
  have hsum : b / 100 * 100 + (b / 10) % 10 * 10 + b % 10 = b := by omega
  have hle : b / 100 * 100 + (b / 10) % 10 * 10 + b % 10 ≤ 255 := by omega
  rw [hsum]
  have hb_le : b ≤ 255 := by omega
  simp [hb_le]

/-- `decodeN (encodeN [b] ++ xs) = (b :: ·) <$> decodeN xs`. -/
theorem decodeN_block (b : Nat) (hb : b < 256) (xs : List Nat) :
    decodeN (encodeN [b] ++ xs) =
      match decodeN xs with
      | some ys => some (b :: ys)
      | none => none := by
  have h0 : b / 100 ≤ 9 := by omega
  have h1 : (b / 10) % 10 ≤ 9 := by omega
  have h2 : b % 10 ≤ 9 := by omega
  simp [encodeN, decodeN]
  rw [valToDig_valid (b / 100) h0, valToDig_valid ((b / 10) % 10) h1, valToDig_valid (b % 10) h2]
  rw [digVal_valToDig (b / 100) h0, digVal_valToDig ((b / 10) % 10) h1, digVal_valToDig (b % 10) h2]
  have hsum : b / 100 * 100 + (b / 10) % 10 * 10 + b % 10 = b := by omega
  have hle : b / 100 * 100 + (b / 10) % 10 * 10 + b % 10 ≤ 255 := by omega
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

private theorem toByte_valToDig (d : Nat) (hd : d ≤ 9) :
    (toByte (valToDig d)).toNat = valToDig d := by
  unfold toByte
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToDig_lt_256 d hd)]

/-- Encode each byte as three zero-padded decimal digits. -/
def encode (bs : List UInt8) : List UInt8 :=
  bs.flatMap (fun b => [toByte (valToDig (b.toNat / 100)), toByte (valToDig ((b.toNat / 10) % 10)), toByte (valToDig (b.toNat % 10))])

/-- Decode triples of decimal digits into bytes. -/
def decode (bs : List UInt8) : Option (List UInt8) :=
  match bs with
  | [] => some []
  | d0 :: d1 :: d2 :: rest =>
    if digValid d0.toNat && digValid d1.toNat && digValid d2.toNat then
      let n := digVal d0.toNat * 100 + digVal d1.toNat * 10 + digVal d2.toNat
      if n ≤ 255 then
        match decode rest with
        | some tl => some (toByte n :: tl)
        | none => none
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
      have h0 : b.toNat / 100 ≤ 9 := by omega
      have h1 : (b.toNat / 10) % 10 ≤ 9 := by omega
      have h2 : b.toNat % 10 ≤ 9 := by omega
      have hcat : encode (b :: bs) = encode [b] ++ encode bs := by simp [encode]
      rw [hcat]
      change decode (encode [b] ++ encode bs) = some (b :: bs)
      change decode ([toByte (valToDig (b.toNat / 100)), toByte (valToDig ((b.toNat / 10) % 10)), toByte (valToDig (b.toNat % 10))] ++ encode bs) = some (b :: bs)
      simp [decode]
      rw [toByte_valToDig (b.toNat / 100) h0, toByte_valToDig ((b.toNat / 10) % 10) h1, toByte_valToDig (b.toNat % 10) h2]
      rw [valToDig_valid (b.toNat / 100) h0, valToDig_valid ((b.toNat / 10) % 10) h1, valToDig_valid (b.toNat % 10) h2]
      rw [digVal_valToDig (b.toNat / 100) h0, digVal_valToDig ((b.toNat / 10) % 10) h1, digVal_valToDig (b.toNat % 10) h2]
      have hsum : b.toNat / 100 * 100 + (b.toNat / 10) % 10 * 10 + b.toNat % 10 = b.toNat := by omega
      rw [hsum]
      have hb_le : b.toNat ≤ 255 := by omega
      simp [hb_le]
      rw [ih]
      simp [toByte, UInt8.ofNat_toNat]

end BaseN.Base10
