/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# BaseN.Base4

Quaternary encoding: one quartet (2 bits) per `0`-`3` character, **four**
characters per byte, MSB-first (`v/64`, `(v/16)%4`, `(v/4)%4`, `v%4`).  Four
quartets always span exactly one byte, so decoding needs no overflow check.

Not an RFC encoding; semantics are defined by this package's spec: "one quartet
per `0-3` char, 4 chars per byte".  Alphabet is ASCII `0-3` (48-51).
-/

namespace BaseN.Base4

/-- `quartetVal e` — the quartet value of a `0-3` character, or `4` if invalid. -/
def quartetVal (e : Nat) : Nat :=
  if e ≤ 51 then if 48 ≤ e then e - 48 else 4 else 4

/-- `valToQuartet d` — the `0-3` character for quartet `d`. -/
def valToQuartet (d : Nat) : Nat := 48 + d

/-- `quartetValid e` — `true` iff `e` is a quartet digit (`0-3`). -/
def quartetValid (e : Nat) : Bool := decide (quartetVal e ≤ 3)

/-- `toByte n` — the `UInt8` embedding. -/
def toByte (n : Nat) : UInt8 := UInt8.ofNat n

theorem quartetVal_valToQuartet (d : Nat) (hd : d ≤ 3) :
    quartetVal (valToQuartet d) = d := by
  unfold quartetVal valToQuartet
  have h1 : 48 + d ≤ 51 := by omega
  have h2 : 48 ≤ 48 + d := by omega
  simp only [h1, ite_true, h2, ite_true]
  omega

theorem valToQuartet_valid (d : Nat) (hd : d ≤ 3) : quartetValid (valToQuartet d) = true := by
  unfold quartetValid
  apply decide_eq_true
  rw [quartetVal_valToQuartet d hd]
  exact hd

theorem valToQuartet_lt_256 (d : Nat) (hd : d ≤ 3) : valToQuartet d < 256 := by
  unfold valToQuartet
  omega

/-- The `i`-th quartet (0-indexed from MSB) of `v`. -/
def quartetAt (v : Nat) (i : Nat) : Nat := (v / 4 ^ (3 - i)) % 4

def quartetsOf (v : Nat) : List Nat :=
  [quartetAt v 0, quartetAt v 1, quartetAt v 2, quartetAt v 3]

def quartetsVal (q0 q1 q2 q3 : Nat) : Nat :=
  q0 * 64 + q1 * 16 + q2 * 4 + q3

/-- `quartetsVal (quartetsOf v) = v` — the quartet roundtrip at Nat level. -/
theorem quartetsVal_quartetsOf (v : Nat) (hv : v < 256) :
    quartetsVal (quartetAt v 0) (quartetAt v 1) (quartetAt v 2) (quartetAt v 3) = v := by
  unfold quartetsVal quartetAt
  simp only [Nat.reducePow, Nat.reduceSub]
  omega

/-- Encode each byte as 4 quartets (Nat level). -/
def encodeN (bs : List Nat) : List Nat :=
  bs.flatMap (fun b => (quartetsOf b).map valToQuartet)

/-- Decode groups of 4 quartets into bytes (`none` on bad input), Nat level. -/
def decodeN (bs : List Nat) : Option (List Nat) :=
  match bs with
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: rest =>
    if quartetValid c0 && quartetValid c1 && quartetValid c2 && quartetValid c3 then
      let v := quartetsVal (quartetVal c0) (quartetVal c1) (quartetVal c2) (quartetVal c3)
      match decodeN rest with
      | some tl => some (v :: tl)
      | none => none
    else none
  | _ => none

/-- `decodeN (encodeN [b]) = some [b]`. -/
theorem decodeN_encodeN_single (b : Nat) (hb : b < 256) :
    decodeN (encodeN [b]) = some [b] := by
  have hq : ∀ i, quartetAt b i ≤ 3 := by intro i; unfold quartetAt; omega
  simp [encodeN, decodeN, quartetsOf]
  rw [valToQuartet_valid (quartetAt b 0) (hq 0), valToQuartet_valid (quartetAt b 1) (hq 1),
      valToQuartet_valid (quartetAt b 2) (hq 2), valToQuartet_valid (quartetAt b 3) (hq 3)]
  rw [quartetVal_valToQuartet (quartetAt b 0) (hq 0), quartetVal_valToQuartet (quartetAt b 1) (hq 1),
      quartetVal_valToQuartet (quartetAt b 2) (hq 2), quartetVal_valToQuartet (quartetAt b 3) (hq 3)]
  rw [quartetsVal_quartetsOf b hb]
  simp

/-- `decodeN (encodeN [b] ++ xs) = (b :: ·) <$> decodeN xs`. -/
theorem decodeN_block (b : Nat) (hb : b < 256) (xs : List Nat) :
    decodeN (encodeN [b] ++ xs) =
      match decodeN xs with
      | some ys => some (b :: ys)
      | none => none := by
  have hq : ∀ i, quartetAt b i ≤ 3 := by intro i; unfold quartetAt; omega
  simp [encodeN, decodeN, quartetsOf]
  rw [valToQuartet_valid (quartetAt b 0) (hq 0), valToQuartet_valid (quartetAt b 1) (hq 1),
      valToQuartet_valid (quartetAt b 2) (hq 2), valToQuartet_valid (quartetAt b 3) (hq 3)]
  rw [quartetVal_valToQuartet (quartetAt b 0) (hq 0), quartetVal_valToQuartet (quartetAt b 1) (hq 1),
      quartetVal_valToQuartet (quartetAt b 2) (hq 2), quartetVal_valToQuartet (quartetAt b 3) (hq 3)]
  rw [quartetsVal_quartetsOf b hb]
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

private theorem toByte_valToQuartet (d : Nat) (hd : d ≤ 3) :
    (toByte (valToQuartet d)).toNat = valToQuartet d := by
  unfold toByte
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToQuartet_lt_256 d hd)]

/-- Encode each byte as 4 quartets. -/
def encode (bs : List UInt8) : List UInt8 :=
  bs.flatMap (fun b => (quartetsOf b.toNat).map (fun i => toByte (valToQuartet i)))

/-- Decode groups of 4 quartets into bytes. -/
def decode (bs : List UInt8) : Option (List UInt8) :=
  match bs with
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: rest =>
    if quartetValid c0.toNat && quartetValid c1.toNat && quartetValid c2.toNat && quartetValid c3.toNat then
      let v := quartetsVal (quartetVal c0.toNat) (quartetVal c1.toNat) (quartetVal c2.toNat) (quartetVal c3.toNat)
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
      have hq : ∀ i, quartetAt b.toNat i ≤ 3 := by intro i; unfold quartetAt; omega
      have hcat : encode (b :: bs) = encode [b] ++ encode bs := by simp [encode]
      rw [hcat]
      change decode (encode [b] ++ encode bs) = some (b :: bs)
      change decode ((quartetsOf b.toNat).map (fun i => toByte (valToQuartet i)) ++ encode bs) = some (b :: bs)
      simp [decode, quartetsOf]
      rw [toByte_valToQuartet (quartetAt b.toNat 0) (hq 0), toByte_valToQuartet (quartetAt b.toNat 1) (hq 1),
          toByte_valToQuartet (quartetAt b.toNat 2) (hq 2), toByte_valToQuartet (quartetAt b.toNat 3) (hq 3)]
      rw [valToQuartet_valid (quartetAt b.toNat 0) (hq 0), valToQuartet_valid (quartetAt b.toNat 1) (hq 1),
          valToQuartet_valid (quartetAt b.toNat 2) (hq 2), valToQuartet_valid (quartetAt b.toNat 3) (hq 3)]
      rw [quartetVal_valToQuartet (quartetAt b.toNat 0) (hq 0), quartetVal_valToQuartet (quartetAt b.toNat 1) (hq 1),
          quartetVal_valToQuartet (quartetAt b.toNat 2) (hq 2), quartetVal_valToQuartet (quartetAt b.toNat 3) (hq 3)]
      rw [quartetsVal_quartetsOf b.toNat hlt]
      simp
      rw [ih]
      simp [toByte, UInt8.ofNat_toNat]

end BaseN.Base4
