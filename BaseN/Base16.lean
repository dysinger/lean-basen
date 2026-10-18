/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# BaseN.Base16

RFC 4648 §8 hex encoding: each byte encodes as two uppercase hex characters
(`0-9A-F`), two hex digits always decode to a byte (no overflow check), and
there is no padding.

Architecture (ported from `fstar-basen`'s `Data.BaseN.Base16`):

  * `nibbleToHex` / `hexToNibble` / `isHexDigit` — the character ↔ nibble
    (0-15) bijection over `UInt8`.
  * `encode` — each byte → two uppercase hex chars.
  * `decode` — parse pairs of hex chars → bytes (`none` on odd length or a
    non-hex char).
  * `roundtrip` — `decode (encode bs) = some bs`, by induction on `bs`,
    `[propext, Quot.sound]`-only.

The digit math is done in `Nat` (`UInt8.toNat`), and re-embedded via
`UInt8.ofNat`, so the proofs are plain `Nat` arithmetic (`omega` over `/` and
`%`).
-/

namespace BaseN.Base16

/-- `nibbleToHex n` — the uppercase ASCII hex digit for nibble `0 ≤ n ≤ 15`. -/
def nibbleToHex (n : Nat) : UInt8 :=
  if n ≤ 9 then UInt8.ofNat (48 + n) else UInt8.ofNat (55 + n)

/-- `isHexDigit b` — is `b` an ASCII hex digit (`0-9`, `A-F`, `a-f`)? -/
def isHexDigit (b : UInt8) : Bool :=
  let v := b.toNat
  (48 ≤ v && v ≤ 57) || (65 ≤ v && v ≤ 70) || (97 ≤ v && v ≤ 102)

/-- `hexToNibble b` — the nibble value of an ASCII hex digit (0-15). -/
def hexToNibble (b : UInt8) : Nat :=
  let v := b.toNat
  if 48 ≤ v && v ≤ 57 then v - 48
  else if 65 ≤ v && v ≤ 70 then v - 55
  else v - 87

/-- `encode bs` — encode each byte as two uppercase hex characters. -/
def encode (bs : List UInt8) : List UInt8 :=
  bs.flatMap (fun b =>
    let v := b.toNat
    [nibbleToHex (v / 16), nibbleToHex (v % 16)])

/-- `decode bs` — parse pairs of hex digits into bytes (`none` on bad input). -/
def decode (bs : List UInt8) : Option (List UInt8) :=
  match bs with
  | [] => some []
  | hi :: lo :: rest =>
    if isHexDigit hi && isHexDigit lo then
      let n := hexToNibble hi * 16 + hexToNibble lo
      match decode rest with
      | some tl => some (UInt8.ofNat n :: tl)
      | none => none
    else none
  | _ => none

-- character ↔ nibble bijection

theorem nibbleToHex_isHexDigit (n : Nat) (hn : n ≤ 15) :
    isHexDigit (nibbleToHex n) = true := by
  simp [isHexDigit, nibbleToHex]
  by_cases h : n ≤ 9
  · simp [h]
    have h1 : 48 ≤ 48 + n := by omega
    have h2 : 48 + n ≤ 57 := by omega
    simp [h1, h2]
  · simp [h]
    have h1 : 65 ≤ 55 + n := by omega
    have h2 : 55 + n ≤ 70 := by omega
    simp [h1, h2]

theorem hexToNibble_nibbleToHex (n : Nat) (hn : n ≤ 15) :
    hexToNibble (nibbleToHex n) = n := by
  simp [hexToNibble, nibbleToHex]
  by_cases h : n ≤ 9
  · simp [h]
    have h1 : 48 ≤ 48 + n := by omega
    have h2 : 48 + n ≤ 57 := by omega
    simp [h1, h2]
  · simp [h]
    have h1 : 65 ≤ 55 + n := by omega
    have h2 : 55 + n ≤ 70 := by omega
    simp [h1, h2]

/-- `decode (encode [b]) = some [b]` — the single-byte roundtrip. -/
theorem encode_single (b : UInt8) :
    decode (encode [b]) = some [b] := by
  let v := b.toNat
  simp [encode, decode]
  rw [nibbleToHex_isHexDigit (v / 16) (by omega),
      nibbleToHex_isHexDigit (v % 16) (by omega)]
  rw [hexToNibble_nibbleToHex (v / 16) (by omega),
      hexToNibble_nibbleToHex (v % 16) (by omega)]
  have hlo : v / 16 * 16 + v % 16 = v := by exact Nat.div_add_mod v 16 |>.symm
  rw [hlo]
  rfl

/-- `encode` distributes over list append. -/
theorem encode_append (xs ys : List UInt8) :
    encode (xs ++ ys) = encode xs ++ encode ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encode, ih]

/-- `decode (encode bs) = some bs` — the full roundtrip. -/
theorem roundtrip (bs : List UInt8) :
    decode (encode bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [encode_append [b] bs]
    -- decode (encode [b] ++ encode bs)
    let v := b.toNat
    -- encode [b] = [nibbleToHex (v/16), nibbleToHex (v%16)]
    rw [encode]  -- hmm, need to unfold the single-element encode
    simp [encode]
    rw [nibbleToHex_isHexDigit (v / 16) (by omega),
        nibbleToHex_isHexDigit (v % 16) (by omega)]
    rw [hexToNibble_nibbleToHex (v / 16) (by omega),
        hexToNibble_nibbleToHex (v % 16) (by omega)]
    rw [ih]
    have hlo : v / 16 * 16 + v % 16 = v := by exact Nat.div_add_mod v 16 |>.symm
    rw [hlo]
    rfl
