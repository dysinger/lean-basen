/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# BaseN.Base16

RFC 4648 §8 hex encoding.  `nibbleToHex` emits **uppercase** (`0-9A-F`), the RFC
canonical form; `hexToNibble` accepts **any** case (`0-9`, `A-F`, `a-f`),
identifying `A~a`, `B~b`, … as the RFC permits (RFC 4648 §8: "the letters may be
uppercase or lowercase").  The bijection is over the 16 nibbles ↔ 16 uppercase
digits, and `decode` additionally accepts the lowercase forms as aliases, so

  * `hexToNibble ∘ nibbleToHex = id` on `{0..15}` (the representative bijection)
  * `decode (encode bs) = some bs` (roundtrip, unconditionally)

both hold with `[propext, Quot.sound]` only.  The digit math is done on `Nat`
(`UInt8.toNat`); the alphabet is ASCII 48-102, all `< 256`, so `UInt8.ofNat`/
`.toNat` are transparent on every value this module produces.
-/

namespace BaseN.Base16

/-- The uppercase-hex digit character (an ASCII byte value) for nibble `n`. -/
def nibbleToHex (n : Nat) : Nat :=
  if n ≤ 9 then 48 + n else 55 + n

/-- `hexToNibble e` — the nibble value of a hex digit, or `16` if invalid. -/
def hexToNibble (e : Nat) : Nat :=
  if e ≤ 57 then
    if 48 ≤ e then e - 48 else 16
  else if e ≤ 70 then
    if 65 ≤ e then e - 55 else 16
  else if e ≤ 102 then
    if 97 ≤ e then e - 87 else 16
  else 16

/-- `hexNibbleValid e` — `true` iff `e` is a hex digit. -/
def hexNibbleValid (e : Nat) : Bool := decide (hexToNibble e ≤ 15)

/-- `fromByte b` / `toByte n` — the `UInt8 ↔ Nat(<256)` correspondence. -/
def fromByte (b : UInt8) : Nat := b.toNat
def toByte (n : Nat) : UInt8 := UInt8.ofNat n

/-- `hexToNibble (nibbleToHex n) = n` — the nibble ↔ uppercase-digit bijection. -/
theorem hexToNibble_nibbleToHex (n : Nat) (hn : n ≤ 15) :
    hexToNibble (nibbleToHex n) = n := by
  have hn0 : 0 ≤ n := by omega
  unfold hexToNibble nibbleToHex
  by_cases h9 : n ≤ 9
  · simp only [h9, ite_true]
    have h1 : 48 + n ≤ 57 := by omega
    have h2 : 48 ≤ 48 + n := by omega
    simp only [h1, ite_true, h2, ite_true]
    omega
  · simp only [h9, ite_false]
    have h1 : 55 + n ≤ 70 := by omega
    have h1' : ¬ 55 + n ≤ 57 := by omega
    have h2 : 65 ≤ 55 + n := by omega
    simp only [h1', ite_false, h1, ite_true, h2, ite_true]
    omega

/-- `nibbleToHex n` is a valid hex digit. -/
theorem nibbleToHex_valid (n : Nat) (hn : n ≤ 15) : hexNibbleValid (nibbleToHex n) = true := by
  unfold hexNibbleValid
  apply decide_eq_true
  rw [hexToNibble_nibbleToHex n hn]
  exact hn

/-- `nibbleToHex n < 256` — every hex digit is a single byte. -/
theorem nibbleToHex_lt_256 (n : Nat) (hn : n ≤ 15) : nibbleToHex n < 256 := by
  unfold nibbleToHex
  by_cases h9 : n ≤ 9 <;> simp [h9] <;> omega

-- the Nat-level codec

/-- Encode a byte list as uppercase hex characters (Nat level). -/
def encodeN (bs : List Nat) : List Nat :=
  bs.flatMap (fun b => [nibbleToHex (b / 16), nibbleToHex (b % 16)])

/-- Decode pairs of hex chars into bytes (`none` on bad input), Nat level. -/
def decodeN (bs : List Nat) : Option (List Nat) :=
  match bs with
  | [] => some []
  | hi :: lo :: rest =>
    if hexNibbleValid hi then
    if hexNibbleValid lo then
      let n := hexToNibble hi * 16 + hexToNibble lo
      match decodeN rest with
      | some tl => some (n :: tl)
      | none => none
    else none
    else none
  | _ => none

/-- `decodeN (encodeN [b]) = some [b]`. -/
theorem decodeN_encodeN_single (b : Nat) (hb : b < 256) :
    decodeN (encodeN [b]) = some [b] := by
  have hv16 : b / 16 ≤ 15 := by omega
  have hvmod16 : b % 16 ≤ 15 := by omega
  simp [encodeN, decodeN]
  rw [nibbleToHex_valid (b / 16) hv16, nibbleToHex_valid (b % 16) hvmod16]
  rw [hexToNibble_nibbleToHex (b / 16) hv16, hexToNibble_nibbleToHex (b % 16) hvmod16]
  have hdiv : b / 16 * 16 + b % 16 = b := by
    have h := Nat.div_add_mod b 16
    rw [Nat.mul_comm] at h
    exact h
  simp [hdiv]

/-- `decodeN (encodeN [b] ++ xs) = (b :: ·) <$> decodeN xs`. -/
theorem decodeN_block (b : Nat) (hb : b < 256) (xs : List Nat) :
    decodeN (encodeN [b] ++ xs) =
      match decodeN xs with
      | some ys => some (b :: ys)
      | none => none := by
  have hv16 : b / 16 ≤ 15 := by omega
  have hvmod16 : b % 16 ≤ 15 := by omega
  simp [encodeN, decodeN]
  rw [nibbleToHex_valid (b / 16) hv16, nibbleToHex_valid (b % 16) hvmod16]
  rw [hexToNibble_nibbleToHex (b / 16) hv16, hexToNibble_nibbleToHex (b % 16) hvmod16]
  have hdiv : b / 16 * 16 + b % 16 = b := by
    have h := Nat.div_add_mod b 16
    rw [Nat.mul_comm] at h
    exact h
  simp [hdiv]

/-- `decodeN (encodeN bs) = some bs`, for byte lists (all elements `< 256`). -/
theorem roundtripN (bs : List Nat) :
    (∀ b ∈ bs, b < 256) → decodeN (encodeN bs) = some bs := by
  intro hbs
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      have hb : b < 256 := hbs b (by simp)
      have htail : ∀ x ∈ bs, x < 256 := by intro x hx; exact hbs x (by simp [hx])
      have hcat : encodeN (b :: bs) = encodeN [b] ++ encodeN bs := by
        simp [encodeN]
      rw [hcat, decodeN_block b hb (encodeN bs), ih htail]

-- the UInt8 surface

/-- `(toByte (nibbleToHex n)).toNat = nibbleToHex n` — shift via `< 256`. -/
theorem toByte_nibbleToHex (n : Nat) (hn : n ≤ 15) :
    (toByte (nibbleToHex n)).toNat = nibbleToHex n := by
  unfold toByte
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (nibbleToHex_lt_256 n hn)]

/-- Encode a byte list as uppercase hex characters. -/
def encode (bs : List UInt8) : List UInt8 :=
  bs.flatMap (fun b => [toByte (nibbleToHex (b.toNat / 16)), toByte (nibbleToHex (b.toNat % 16))])

/-- Decode pairs of hex chars into bytes (`none` on bad input). -/
def decode (bs : List UInt8) : Option (List UInt8) :=
  match bs with
  | [] => some []
  | hi :: lo :: rest =>
    if hexNibbleValid hi.toNat then
    if hexNibbleValid lo.toNat then
      let n := hexToNibble hi.toNat * 16 + hexToNibble lo.toNat
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
      have hv16 : b.toNat / 16 ≤ 15 := by omega
      have hvmod16 : b.toNat % 16 ≤ 15 := by omega
      have hcat : encode (b :: bs) = encode [b] ++ encode bs := by simp [encode]
      rw [hcat]
      change decode (encode [b] ++ encode bs) = some (b :: bs)
      -- encode [b] = [toByte (nibbleToHex (b.toNat/16)), toByte (nibbleToHex (b.toNat%16))]
      change decode ([toByte (nibbleToHex (b.toNat / 16)), toByte (nibbleToHex (b.toNat % 16))] ++ encode bs) = some (b :: bs)
      simp [decode]
      rw [toByte_nibbleToHex (b.toNat / 16) hv16, toByte_nibbleToHex (b.toNat % 16) hvmod16]
      rw [nibbleToHex_valid (b.toNat / 16) hv16, nibbleToHex_valid (b.toNat % 16) hvmod16]
      rw [hexToNibble_nibbleToHex (b.toNat / 16) hv16, hexToNibble_nibbleToHex (b.toNat % 16) hvmod16]
      have hdiv : b.toNat / 16 * 16 + b.toNat % 16 = b.toNat := by
        have h := Nat.div_add_mod b.toNat 16
        rw [Nat.mul_comm] at h
        exact h
      rw [hdiv]
      rw [ih]
      simp [toByte, UInt8.ofNat_toNat]

end BaseN.Base16
