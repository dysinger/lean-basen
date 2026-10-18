/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# BaseN.Base2

Binary encoding: one bit per `0`/`1` character, **eight** characters per byte,
**MSB-first** (bit 7 first, bit 0 last).  Eight bits always span exactly one
byte, so decoding needs no overflow check.

Not an RFC encoding (RFC 4648 covers 16/32/64 only); semantics are defined by
this package's spec: "one bit per `0`/`1` char, 8 chars per byte, MSB-first".
Alphabet is ASCII `0`/`1` (48-49).
-/

namespace BaseN.Base2

/-- `bitVal e` — the bit value of a `0`/`1` character, or `2` if invalid. -/
def bitVal (e : Nat) : Nat :=
  if e = 48 then 0 else if e = 49 then 1 else 2

/-- `valToBit b` — the `0`/`1` character for bit `b` (`b ∈ {0,1}`, else `49`). -/
def valToBit (b : Nat) : Nat :=
  if b = 0 then 48 else 49

/-- `bitValid e` — `true` iff `e` is `0` or `1`. -/
def bitValid (e : Nat) : Bool := decide (bitVal e ≤ 1)

/-- `toByte n` — the `UInt8` embedding. -/
def toByte (n : Nat) : UInt8 := UInt8.ofNat n

theorem bitVal_valToBit (b : Nat) (hb : b ≤ 1) : bitVal (valToBit b) = b := by
  unfold bitVal valToBit
  by_cases h : b = 0
  · simp [h]
  · have hb1 : b = 1 := by omega
    simp [hb1]

theorem valToBit_valid (b : Nat) (hb : b ≤ 1) : bitValid (valToBit b) = true := by
  unfold bitValid
  apply decide_eq_true
  rw [bitVal_valToBit b hb]
  exact hb

theorem valToBit_lt_256 (b : Nat) (_hb : b ≤ 1) : valToBit b < 256 := by
  unfold valToBit
  by_cases h : b = 0 <;> simp [h] <;> omega

/-- The `i`-th bit (0-indexed from the MSB) of `v`: `(v / 2^(7-i)) % 2`. -/
def bitAt (v : Nat) (i : Nat) : Nat := (v / 2 ^ (7 - i)) % 2

/-- The 8 MSB-first bits of `v` (values `0`/`1`). -/
def bitsOf (v : Nat) : List Nat :=
  [bitAt v 0, bitAt v 1, bitAt v 2, bitAt v 3, bitAt v 4, bitAt v 5, bitAt v 6, bitAt v 7]

/-- The value of 8 MSB-first bits `b0..b7`. -/
def bitsVal (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) : Nat :=
  b0 * 128 + b1 * 64 + b2 * 32 + b3 * 16 + b4 * 8 + b5 * 4 + b6 * 2 + b7

-- The `bitsVal (bitsOf v) = v` identity is proved inline in the codec theorems.

/-- Encode each byte as 8 MSB-first bits (Nat level). -/
def encodeN (bs : List Nat) : List Nat :=
  bs.flatMap (fun b => (bitsOf b).map valToBit)

/-- Decode groups of 8 bits into bytes (`none` on bad input), Nat level. -/
def decodeN (bs : List Nat) : Option (List Nat) :=
  match bs with
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest =>
    if bitValid c0 && bitValid c1 && bitValid c2 && bitValid c3
       && bitValid c4 && bitValid c5 && bitValid c6 && bitValid c7 then
      let v := bitsVal (bitVal c0) (bitVal c1) (bitVal c2) (bitVal c3)
                (bitVal c4) (bitVal c5) (bitVal c6) (bitVal c7)
      match decodeN rest with
      | some tl => some (v :: tl)
      | none => none
    else none
  | _ => none

/-- `decodeN (encodeN [b]) = some [b]`. -/
theorem decodeN_encodeN_single (b : Nat) (hb : b < 256) :
    decodeN (encodeN [b]) = some [b] := by
  have hbits : ∀ i, bitAt b i ≤ 1 := by
    intro i; unfold bitAt; omega
  simp [encodeN, decodeN, bitsOf]
  rw [valToBit_valid (bitAt b 0) (hbits 0), valToBit_valid (bitAt b 1) (hbits 1),
      valToBit_valid (bitAt b 2) (hbits 2), valToBit_valid (bitAt b 3) (hbits 3),
      valToBit_valid (bitAt b 4) (hbits 4), valToBit_valid (bitAt b 5) (hbits 5),
      valToBit_valid (bitAt b 6) (hbits 6), valToBit_valid (bitAt b 7) (hbits 7)]
  rw [bitVal_valToBit (bitAt b 0) (hbits 0), bitVal_valToBit (bitAt b 1) (hbits 1),
      bitVal_valToBit (bitAt b 2) (hbits 2), bitVal_valToBit (bitAt b 3) (hbits 3),
      bitVal_valToBit (bitAt b 4) (hbits 4), bitVal_valToBit (bitAt b 5) (hbits 5),
      bitVal_valToBit (bitAt b 6) (hbits 6), bitVal_valToBit (bitAt b 7) (hbits 7)]
  unfold bitsVal
  have hsum : bitAt b 0 * 128 + bitAt b 1 * 64 + bitAt b 2 * 32 + bitAt b 3 * 16
            + bitAt b 4 * 8 + bitAt b 5 * 4 + bitAt b 6 * 2 + bitAt b 7 = b := by
    unfold bitAt
    simp only [Nat.reducePow, Nat.reduceSub]
    omega
  rw [hsum]
  simp

/-- `decodeN (encodeN [b] ++ xs) = (b :: ·) <$> decodeN xs`. -/
theorem decodeN_block (b : Nat) (hb : b < 256) (xs : List Nat) :
    decodeN (encodeN [b] ++ xs) =
      match decodeN xs with
      | some ys => some (b :: ys)
      | none => none := by
  have hbits : ∀ i, bitAt b i ≤ 1 := by
    intro i; unfold bitAt; omega
  simp [encodeN, decodeN, bitsOf]
  rw [valToBit_valid (bitAt b 0) (hbits 0), valToBit_valid (bitAt b 1) (hbits 1),
      valToBit_valid (bitAt b 2) (hbits 2), valToBit_valid (bitAt b 3) (hbits 3),
      valToBit_valid (bitAt b 4) (hbits 4), valToBit_valid (bitAt b 5) (hbits 5),
      valToBit_valid (bitAt b 6) (hbits 6), valToBit_valid (bitAt b 7) (hbits 7)]
  rw [bitVal_valToBit (bitAt b 0) (hbits 0), bitVal_valToBit (bitAt b 1) (hbits 1),
      bitVal_valToBit (bitAt b 2) (hbits 2), bitVal_valToBit (bitAt b 3) (hbits 3),
      bitVal_valToBit (bitAt b 4) (hbits 4), bitVal_valToBit (bitAt b 5) (hbits 5),
      bitVal_valToBit (bitAt b 6) (hbits 6), bitVal_valToBit (bitAt b 7) (hbits 7)]
  unfold bitsVal
  have hsum : bitAt b 0 * 128 + bitAt b 1 * 64 + bitAt b 2 * 32 + bitAt b 3 * 16
            + bitAt b 4 * 8 + bitAt b 5 * 4 + bitAt b 6 * 2 + bitAt b 7 = b := by
    unfold bitAt
    simp only [Nat.reducePow, Nat.reduceSub]
    omega
  rw [hsum]
  simp

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

private theorem toByte_valToBit (b : Nat) (hb : b ≤ 1) :
    (toByte (valToBit b)).toNat = valToBit b := by
  unfold toByte
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToBit_lt_256 b hb)]

/-- Encode each byte as 8 MSB-first bits. -/
def encode (bs : List UInt8) : List UInt8 :=
  bs.flatMap (fun b => (bitsOf b.toNat).map (fun i => toByte (valToBit i)))

/-- Decode groups of 8 bits into bytes. -/
def decode (bs : List UInt8) : Option (List UInt8) :=
  match bs with
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest =>
    if bitValid c0.toNat && bitValid c1.toNat && bitValid c2.toNat && bitValid c3.toNat
       && bitValid c4.toNat && bitValid c5.toNat && bitValid c6.toNat && bitValid c7.toNat then
      let v := bitsVal (bitVal c0.toNat) (bitVal c1.toNat) (bitVal c2.toNat) (bitVal c3.toNat)
                (bitVal c4.toNat) (bitVal c5.toNat) (bitVal c6.toNat) (bitVal c7.toNat)
      match decode rest with
      | some tl => some (toByte v :: tl)
      | none => none
    else none
  | _ => none

/-- `decode (encode bs) = some bs` — the full roundtrip, `UInt8` level. -/
theorem roundtrip (bs : List UInt8) :
    decode (encode bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      have hlt : b.toNat < 256 := by simpa using UInt8.toNat_lt b
      have hbits : ∀ i, bitAt b.toNat i ≤ 1 := by intro i; unfold bitAt; omega
      have hcat : encode (b :: bs) = encode [b] ++ encode bs := by simp [encode]
      rw [hcat]
      change decode (encode [b] ++ encode bs) = some (b :: bs)
      change decode ((bitsOf b.toNat).map (fun i => toByte (valToBit i)) ++ encode bs) = some (b :: bs)
      simp [decode, bitsOf]
      rw [toByte_valToBit (bitAt b.toNat 0) (hbits 0), toByte_valToBit (bitAt b.toNat 1) (hbits 1),
          toByte_valToBit (bitAt b.toNat 2) (hbits 2), toByte_valToBit (bitAt b.toNat 3) (hbits 3),
          toByte_valToBit (bitAt b.toNat 4) (hbits 4), toByte_valToBit (bitAt b.toNat 5) (hbits 5),
          toByte_valToBit (bitAt b.toNat 6) (hbits 6), toByte_valToBit (bitAt b.toNat 7) (hbits 7)]
      rw [valToBit_valid (bitAt b.toNat 0) (hbits 0), valToBit_valid (bitAt b.toNat 1) (hbits 1),
          valToBit_valid (bitAt b.toNat 2) (hbits 2), valToBit_valid (bitAt b.toNat 3) (hbits 3),
          valToBit_valid (bitAt b.toNat 4) (hbits 4), valToBit_valid (bitAt b.toNat 5) (hbits 5),
          valToBit_valid (bitAt b.toNat 6) (hbits 6), valToBit_valid (bitAt b.toNat 7) (hbits 7)]
      rw [bitVal_valToBit (bitAt b.toNat 0) (hbits 0), bitVal_valToBit (bitAt b.toNat 1) (hbits 1),
          bitVal_valToBit (bitAt b.toNat 2) (hbits 2), bitVal_valToBit (bitAt b.toNat 3) (hbits 3),
          bitVal_valToBit (bitAt b.toNat 4) (hbits 4), bitVal_valToBit (bitAt b.toNat 5) (hbits 5),
          bitVal_valToBit (bitAt b.toNat 6) (hbits 6), bitVal_valToBit (bitAt b.toNat 7) (hbits 7)]
      unfold bitsVal
      have hsum : bitAt b.toNat 0 * 128 + bitAt b.toNat 1 * 64 + bitAt b.toNat 2 * 32 + bitAt b.toNat 3 * 16
                + bitAt b.toNat 4 * 8 + bitAt b.toNat 5 * 4 + bitAt b.toNat 6 * 2 + bitAt b.toNat 7 = b.toNat := by
        unfold bitAt
        simp only [Nat.reducePow, Nat.reduceSub]
        omega
      rw [hsum]
      simp
      rw [ih]
      simp [toByte, UInt8.ofNat_toNat]

end BaseN.Base2
