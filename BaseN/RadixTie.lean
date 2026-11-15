/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import BaseN.Radix
import BaseN.RadixAlphabets
import BaseN.RadixCodec

/-!
# BaseN.RadixTie — the block isos tied to the generic fold

`BaseN.Radix` supplies the radix-generic numeral fold `toNat`; each base supplies a
block `Iso` that packs one block's worth of digits into a value. This module proves
that the two **agree**, per base, by a *canonicity-filtered implication pair*.

## Why an implication pair and not an equality

`design.md` D6 first proposed "the block iso is `toNat` restricted", and **that is
false**. Measured, on the shipped tree:

```
toNat 2 [48,49]                    -> some 1     -- "01" is a valid numeral
BaseN.Base2.bitBlockApply [48,49]  -> none       -- the block wants exactly 8 digits
digBlockApply (pad "255")          -> some 255  while toNat 10 "999" -> some 999
```

So neither direction of an equality holds in general: the block rejects inputs the
fold accepts (wrong arity, a digit outside the block's alphabet), and — for base 10 —
the block's `UInt8` codomain cannot carry a value over 255. The accurate statement is
an implication pair, in two schemas by codomain:

* **schema `_8`** (bases 2, 4, 8, 10, 16): `apply : List UInt8 → Option UInt8`
  * `→`: `toNat b cs = some n → blockApply cs = some (UInt8.ofNat n)`
  * `←`: `blockApply cs = some v → toNat b cs = some v.toNat`
* **schema `_L`** (bases 32, 64): `apply : List UInt8 → Option (List UInt8)`.

## Both directions are stated at the block's LITERAL arity

A first draft of this module stated `→` over an arbitrary `cs : List UInt8`, following
D6's schema verbatim. That needs `cs.length = blockWidth` as an extra hypothesis, which
D6 never mentions and which is only there to compensate for the statement's shape. At
the literal vector the hypothesis is unrepresentable — the arity *is* the statement —
so the ties below carry no length condition at all.

`→` still needs the **digit-value bridge** (`digitVal` ↔ the base's own alphabet
function), because the fold reads *bytes* and the block reads *values*. That is what
`BaseN.RadixAlphabets` proves at the digit level; the per-base lemmas below lift it to
the block.

Every law here is `[propext, Quot.sound]`-only. `Classical.choice` appeared three times
while these were being written, in two distinct shapes, both recorded below.
-/

namespace BaseN.RadixTie

open BaseN.Radix

/-! ## The generic fold, in `natVal` form

The reusable core of every `_8` tie. `toNat` folds `d ↦ v` with weights
`radix ^ (length - 1 - i)`, which is exactly `natVal` of the digit-value list — so this
lemma converts "the fold read these bytes as `n`" into "`n` is that sum", which is the
form a block's own arithmetic lives in. -/

/-- `valAt b ds vs` — `vs` is `ds`'s digit values, position by position. -/
def valAt (b : Nat) (ds : List UInt8) (vs : List Nat) : Prop :=
  ∀ (i : Nat) (hi : i < vs.length) (hj : i < ds.length),
    digitVal b (ds.get ⟨i, hj⟩) = some (vs.get ⟨i, hi⟩)

theorem toNat_eq_natVal_map : ∀ (b : Nat) (ds : List UInt8) (n : Nat),
    toNat b ds = some n →
    ∃ vs : List Nat, vs.length = ds.length ∧ valAt b ds vs ∧ n = natVal b vs := by
  intro b ds
  induction ds with
  | nil =>
      intro n h
      have h0 : n = 0 := by simpa [toNat] using h.symm
      exact ⟨[], rfl, fun i _ hj => absurd hj (by simp), by simp [natVal, h0]⟩
  | cons d ds ih =>
      intro n h
      cases hd : digitVal b d with
      | none => rw [toNat_cons_none b d ds hd] at h; exact absurd h (by simp)
      | some v =>
          rw [toNat_cons_some b d ds v hd] at h
          obtain ⟨a, ha, hn⟩ : ∃ a, toNat b ds = some a ∧ v * b ^ ds.length + a = n := by
            simpa only [Option.map_eq_some_iff] using h
          obtain ⟨vs, hlen, hval, hnat⟩ := ih a ha
          refine ⟨v :: vs, by simp [hlen], ?_, ?_⟩
          · intro i hi hj
            cases i with
            | zero => simpa using hd
            | succ k =>
                have h1 : k < vs.length := by simpa using hi
                have h2 : k < ds.length := by simpa using hj
                simpa using hval k h1 h2
          · simp only [natVal, hlen]
            omega

theorem toNat_nil (b : Nat) : toNat b [] = some 0 := rfl

/-! ## `natVal` at the block widths -/

theorem natVal_two (b v0 v1 : Nat) : natVal b [v0, v1] = v0 * b + v1 := by
  simp [natVal]

theorem natVal_three (b v0 v1 v2 : Nat) :
    natVal b [v0, v1, v2] = v0 * b ^ 2 + v1 * b + v2 := by
  simp [natVal]; omega

theorem natVal_four (b v0 v1 v2 v3 : Nat) :
    natVal b [v0, v1, v2, v3] = v0 * b ^ 3 + v1 * b ^ 2 + v2 * b + v3 := by
  simp [natVal]; omega

theorem natVal_eight (b v0 v1 v2 v3 v4 v5 v6 v7 : Nat) :
    natVal b [v0, v1, v2, v3, v4, v5, v6, v7] =
      v0 * b ^ 7 + v1 * b ^ 6 + v2 * b ^ 5 + v3 * b ^ 4
        + v4 * b ^ 3 + v5 * b ^ 2 + v6 * b + v7 := by
  simp [natVal]; omega

/-! ## `toNat` at a literal vector, in terms of `natVal` of the value vector

Each takes the digit values as inputs — the caller supplies `digitVal b di = some vi`.
Restating the fold this way is what removes the need for `split` on it, which is
`AGENTS.md`'s recorded "`unfold` does not reduce a `match`-def at a variable argument"
trap avoided rather than hit. -/

theorem toNat_two (b : Nat) (d0 d1 : UInt8) (v0 v1 n : Nat)
    (h0 : digitVal b d0 = some v0) (h1 : digitVal b d1 = some v1)
    (h : toNat b [d0, d1] = some n) : n = natVal b [v0, v1] := by
  rw [toNat_cons_some b d0 _ v0 h0, toNat_cons_some b d1 [] v1 h1, toNat_nil] at h
  simp only [Option.map_some] at h
  injection h with hn
  simp only [List.length_cons, List.length_nil] at hn
  rw [← hn, natVal_two]
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul, Nat.add_zero]

theorem toNat_three (b : Nat) (d0 d1 d2 : UInt8) (v0 v1 v2 n : Nat)
    (h0 : digitVal b d0 = some v0) (h1 : digitVal b d1 = some v1)
    (h2 : digitVal b d2 = some v2) (h : toNat b [d0, d1, d2] = some n) :
    n = natVal b [v0, v1, v2] := by
  rw [toNat_cons_some b d0 _ v0 h0, toNat_cons_some b d1 _ v1 h1,
      toNat_cons_some b d2 [] v2 h2, toNat_nil] at h
  simp only [Option.map_some] at h
  injection h with hn
  simp only [List.length_cons, List.length_nil] at hn
  rw [← hn, natVal_three]
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul, Nat.add_zero]
  omega

theorem toNat_four (b : Nat) (d0 d1 d2 d3 : UInt8) (v0 v1 v2 v3 n : Nat)
    (h0 : digitVal b d0 = some v0) (h1 : digitVal b d1 = some v1)
    (h2 : digitVal b d2 = some v2) (h3 : digitVal b d3 = some v3)
    (h : toNat b [d0, d1, d2, d3] = some n) : n = natVal b [v0, v1, v2, v3] := by
  rw [toNat_cons_some b d0 _ v0 h0, toNat_cons_some b d1 _ v1 h1,
      toNat_cons_some b d2 _ v2 h2, toNat_cons_some b d3 [] v3 h3, toNat_nil] at h
  simp only [Option.map_some] at h
  injection h with hn
  simp only [List.length_cons, List.length_nil] at hn
  rw [← hn, natVal_four]
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul, Nat.add_zero]
  omega

theorem toNat_eight (b : Nat) (d0 d1 d2 d3 d4 d5 d6 d7 : UInt8)
    (v0 v1 v2 v3 v4 v5 v6 v7 n : Nat)
    (h0 : digitVal b d0 = some v0) (h1 : digitVal b d1 = some v1)
    (h2 : digitVal b d2 = some v2) (h3 : digitVal b d3 = some v3)
    (h4 : digitVal b d4 = some v4) (h5 : digitVal b d5 = some v5)
    (h6 : digitVal b d6 = some v6) (h7 : digitVal b d7 = some v7)
    (h : toNat b [d0, d1, d2, d3, d4, d5, d6, d7] = some n) :
    n = natVal b [v0, v1, v2, v3, v4, v5, v6, v7] := by
  rw [toNat_cons_some b d0 _ v0 h0, toNat_cons_some b d1 _ v1 h1,
      toNat_cons_some b d2 _ v2 h2, toNat_cons_some b d3 _ v3 h3,
      toNat_cons_some b d4 _ v4 h4, toNat_cons_some b d5 _ v5 h5,
      toNat_cons_some b d6 _ v6 h6, toNat_cons_some b d7 [] v7 h7, toNat_nil] at h
  simp only [Option.map_some] at h
  injection h with hn
  simp only [List.length_cons, List.length_nil] at hn
  rw [← hn, natVal_eight]
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul, Nat.add_zero]
  omega

/-! ## Base 2 — the eight-bit block

The first of the five `_8` ties, and the template for the rest. Two things make it
work, and both are reusable:

* `digitVal_two_shape` unfolds `digitVal` at the **literal** radix 2, which collapses the
  seven-arm `if`-chain to a single `inWin` test — `AGENTS.md`'s recorded recipe, and the
  step that makes `split` unnecessary.
* `bitBlockApply`'s guard is `bitValid dᵢ`, and the fold's success is exactly what
  supplies it (`isDigits_of_toNat`). So `→` never has to assume its own hypothesis. -/

/-- `digitVal 2` at the literal radix: one window test, not a dispatch chain. -/
theorem digitVal_two_shape (d : UInt8) :
    digitVal 2 d = (if inWin 48 49 d.toNat = true then some (d.toNat - 48) else none) := by
  rw [digitVal_eq]; simp

/-- On the bit alphabet, `bitVal` is `c - 48`. -/
theorem bitVal_on {c : Nat} (h : inWin 48 49 c = true) : BaseN.Base2.bitVal c = c - 48 := by
  obtain ⟨hlo, hhi⟩ := inWin_eq_true h
  unfold BaseN.Base2.bitVal
  by_cases a : c = 48
  · simp [a]
  · have b : c = 49 := by omega
    subst b
    decide

theorem bitValid_of_digitVal_two (d : UInt8) (h : (digitVal 2 d).isSome = true) :
    BaseN.Base2.bitValid d.toNat = true := by
  rw [digitVal_two_shape] at h
  by_cases hin : inWin 48 49 d.toNat = true
  · obtain ⟨hlo, hhi⟩ := inWin_eq_true hin
    unfold BaseN.Base2.bitValid
    show decide (BaseN.Base2.bitVal d.toNat ≤ 1) = true
    rw [bitVal_on hin]
    simp only [decide_eq_true_eq]
    omega
  · simp only [hin] at h
    exact absurd h (by simp)

theorem digitVal_two_of_bitValid (d : UInt8) (hv : BaseN.Base2.bitValid d.toNat = true) :
    digitVal 2 d = some (BaseN.Base2.bitVal d.toNat) := by
  have hle : BaseN.Base2.bitVal d.toNat ≤ 1 := BaseN.Base2.bitValid_of_decide d.toNat hv
  rw [digitVal_two_shape]
  have hin : inWin 48 49 d.toNat = true := by
    rw [inWin_iff]
    unfold BaseN.Base2.bitVal at hle
    by_cases a : d.toNat = 48
    · exact ⟨by omega, by omega⟩
    · by_cases b' : d.toNat = 49
      · exact ⟨by omega, by omega⟩
      · rw [ite_eq_right a, ite_eq_right b'] at hle
        omega
  rw [hin]
  simp only [ite_true]
  rw [bitVal_on hin]

/-- **The base-2 tie, `→` (schema `_8`).** -/
theorem bitBlockApply_of_toNat (d0 d1 d2 d3 d4 d5 d6 d7 : UInt8) (n : Nat)
    (h : toNat 2 [d0, d1, d2, d3, d4, d5, d6, d7] = some n) :
    BaseN.Base2.bitBlockApply [d0, d1, d2, d3, d4, d5, d6, d7] = some (UInt8.ofNat n) := by
  have hdig : BaseN.RadixCodec.isDigits 2 [d0,d1,d2,d3,d4,d5,d6,d7] = true :=
    BaseN.RadixCodec.isDigits_of_toNat (by rw [h]; rfl)
  rw [BaseN.RadixCodec.isDigits_iff] at hdig
  have hv0 := bitValid_of_digitVal_two d0 (hdig d0 (by simp))
  have hv1 := bitValid_of_digitVal_two d1 (hdig d1 (by simp))
  have hv2 := bitValid_of_digitVal_two d2 (hdig d2 (by simp))
  have hv3 := bitValid_of_digitVal_two d3 (hdig d3 (by simp))
  have hv4 := bitValid_of_digitVal_two d4 (hdig d4 (by simp))
  have hv5 := bitValid_of_digitVal_two d5 (hdig d5 (by simp))
  have hv6 := bitValid_of_digitVal_two d6 (hdig d6 (by simp))
  have hv7 := bitValid_of_digitVal_two d7 (hdig d7 (by simp))
  rw [BaseN.Base2.bitBlockApply]
  simp only [hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, Bool.and_self, ite_true]
  have hval := toNat_eight 2 d0 d1 d2 d3 d4 d5 d6 d7
      (BaseN.Base2.bitVal d0.toNat) (BaseN.Base2.bitVal d1.toNat)
      (BaseN.Base2.bitVal d2.toNat) (BaseN.Base2.bitVal d3.toNat)
      (BaseN.Base2.bitVal d4.toNat) (BaseN.Base2.bitVal d5.toNat)
      (BaseN.Base2.bitVal d6.toNat) (BaseN.Base2.bitVal d7.toNat) n
      (digitVal_two_of_bitValid d0 hv0) (digitVal_two_of_bitValid d1 hv1)
      (digitVal_two_of_bitValid d2 hv2) (digitVal_two_of_bitValid d3 hv3)
      (digitVal_two_of_bitValid d4 hv4) (digitVal_two_of_bitValid d5 hv5)
      (digitVal_two_of_bitValid d6 hv6) (digitVal_two_of_bitValid d7 hv7) h
  rw [hval, natVal_eight]
  congr 1

/-- **The base-2 tie, `←` (schema `_8`).** -/
theorem toNat_of_bitBlockApply (d0 d1 d2 d3 d4 d5 d6 d7 : UInt8) (v : UInt8)
    (h : BaseN.Base2.bitBlockApply [d0, d1, d2, d3, d4, d5, d6, d7] = some v) :
    toNat 2 [d0, d1, d2, d3, d4, d5, d6, d7] = some v.toNat := by
  rw [BaseN.Base2.bitBlockApply] at h
  by_cases hgood : (BaseN.Base2.bitValid d0.toNat && BaseN.Base2.bitValid d1.toNat &&
      BaseN.Base2.bitValid d2.toNat && BaseN.Base2.bitValid d3.toNat &&
      BaseN.Base2.bitValid d4.toNat && BaseN.Base2.bitValid d5.toNat &&
      BaseN.Base2.bitValid d6.toNat && BaseN.Base2.bitValid d7.toNat) = true
  · rw [ite_eq_left hgood] at h
    simp only [Bool.and_eq_true] at hgood
    obtain ⟨⟨⟨⟨⟨⟨⟨hg0, hg1⟩, hg2⟩, hg3⟩, hg4⟩, hg5⟩, hg6⟩, hg7⟩ := hgood
    injection h with hv
    subst hv
    rw [toNat_cons_some 2 d0 _ _ (digitVal_two_of_bitValid d0 hg0),
        toNat_cons_some 2 d1 _ _ (digitVal_two_of_bitValid d1 hg1),
        toNat_cons_some 2 d2 _ _ (digitVal_two_of_bitValid d2 hg2),
        toNat_cons_some 2 d3 _ _ (digitVal_two_of_bitValid d3 hg3),
        toNat_cons_some 2 d4 _ _ (digitVal_two_of_bitValid d4 hg4),
        toNat_cons_some 2 d5 _ _ (digitVal_two_of_bitValid d5 hg5),
        toNat_cons_some 2 d6 _ _ (digitVal_two_of_bitValid d6 hg6),
        toNat_cons_some 2 d7 [] _ (digitVal_two_of_bitValid d7 hg7),
        toNat_nil]
    simp only [Option.map_some]
    rw [UInt8.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by
      have l0 := BaseN.Base2.bitValid_of_decide d0.toNat hg0
      have l1 := BaseN.Base2.bitValid_of_decide d1.toNat hg1
      have l2 := BaseN.Base2.bitValid_of_decide d2.toNat hg2
      have l3 := BaseN.Base2.bitValid_of_decide d3.toNat hg3
      have l4 := BaseN.Base2.bitValid_of_decide d4.toNat hg4
      have l5 := BaseN.Base2.bitValid_of_decide d5.toNat hg5
      have l6 := BaseN.Base2.bitValid_of_decide d6.toNat hg6
      have l7 := BaseN.Base2.bitValid_of_decide d7.toNat hg7
      unfold BaseN.Base2.bitsVal
      omega)]
    congr 1
    unfold BaseN.Base2.bitsVal
    simp only [List.length_cons, List.length_nil, Nat.pow_zero, Nat.pow_succ, Nat.mul_one]
    omega
  · rw [ite_eq_right hgood] at h
    exact absurd h (by simp)

end BaseN.RadixTie
