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

/-! ## Base 4 — the four-quartet block

Same shape as base 2, four digits. `quartetVal` is `e - 48` on its window, and its
validity predicate is `quartetVal e ≤ 3`. -/

theorem digitVal_four_shape (d : UInt8) :
    digitVal 4 d = (if inWin 48 51 d.toNat = true then some (d.toNat - 48) else none) := by
  rw [digitVal_eq]; simp

theorem quartetVal_on {c : Nat} (h : inWin 48 51 c = true) :
    BaseN.Base4.quartetVal c = c - 48 := by
  obtain ⟨hlo, hhi⟩ := inWin_eq_true h
  unfold BaseN.Base4.quartetVal
  rw [ite_eq_left hhi, ite_eq_left hlo]

theorem quartetVal_bounds (c : Nat) (h : BaseN.Base4.quartetVal c ≤ 3) :
    48 ≤ c ∧ c ≤ 51 := by
  unfold BaseN.Base4.quartetVal at h
  by_cases h1 : c ≤ 51
  · rw [ite_eq_left h1] at h
    by_cases h2 : 48 ≤ c
    · exact ⟨h2, h1⟩
    · rw [ite_eq_right h2] at h
      omega
  · rw [ite_eq_right h1] at h
    omega

theorem digitVal_four_of_quartetValid (d : UInt8)
    (hv : BaseN.Base4.quartetValid d.toNat = true) :
    digitVal 4 d = some (BaseN.Base4.quartetVal d.toNat) := by
  have hle := BaseN.Base4.quartetValid_of_decide d.toNat hv
  obtain ⟨hlo, hhi⟩ := quartetVal_bounds d.toNat hle
  rw [digitVal_four_shape]
  have hin : inWin 48 51 d.toNat = true := by rw [inWin_iff]; exact ⟨hlo, hhi⟩
  rw [hin]
  simp only [ite_true]
  rw [quartetVal_on hin]

theorem quartetValid_of_digitVal (d : UInt8) (h : (digitVal 4 d).isSome = true) :
    BaseN.Base4.quartetValid d.toNat = true := by
  rw [digitVal_four_shape] at h
  by_cases hin : inWin 48 51 d.toNat = true
  · obtain ⟨hlo, hhi⟩ := inWin_eq_true hin
    unfold BaseN.Base4.quartetValid
    show decide (BaseN.Base4.quartetVal d.toNat ≤ 3) = true
    rw [quartetVal_on hin]
    simp only [decide_eq_true_eq]
    omega
  · simp only [hin] at h
    exact absurd h (by simp)

/-- **The base-4 tie, `→`.** -/
theorem quartetBlockApply_of_toNat (d0 d1 d2 d3 : UInt8) (n : Nat)
    (h : toNat 4 [d0, d1, d2, d3] = some n) :
    BaseN.Base4.quartetBlockApply [d0, d1, d2, d3] = some (UInt8.ofNat n) := by
  have hdig : BaseN.RadixCodec.isDigits 4 [d0, d1, d2, d3] = true :=
    BaseN.RadixCodec.isDigits_of_toNat (by rw [h]; rfl)
  rw [BaseN.RadixCodec.isDigits_iff] at hdig
  have hv0 := quartetValid_of_digitVal d0 (hdig d0 (by simp))
  have hv1 := quartetValid_of_digitVal d1 (hdig d1 (by simp))
  have hv2 := quartetValid_of_digitVal d2 (hdig d2 (by simp))
  have hv3 := quartetValid_of_digitVal d3 (hdig d3 (by simp))
  rw [BaseN.Base4.quartetBlockApply]
  simp only [hv0, hv1, hv2, hv3, Bool.and_self, ite_true]
  have hval := toNat_four 4 d0 d1 d2 d3
      (BaseN.Base4.quartetVal d0.toNat) (BaseN.Base4.quartetVal d1.toNat)
      (BaseN.Base4.quartetVal d2.toNat) (BaseN.Base4.quartetVal d3.toNat) n
      (digitVal_four_of_quartetValid d0 hv0) (digitVal_four_of_quartetValid d1 hv1)
      (digitVal_four_of_quartetValid d2 hv2) (digitVal_four_of_quartetValid d3 hv3) h
  rw [hval, natVal_four]
  congr 1

/-- **The base-4 tie, `←`.** -/
theorem toNat_of_quartetBlockApply (d0 d1 d2 d3 : UInt8) (v : UInt8)
    (h : BaseN.Base4.quartetBlockApply [d0, d1, d2, d3] = some v) :
    toNat 4 [d0, d1, d2, d3] = some v.toNat := by
  rw [BaseN.Base4.quartetBlockApply] at h
  by_cases hgood : (BaseN.Base4.quartetValid d0.toNat && BaseN.Base4.quartetValid d1.toNat &&
      BaseN.Base4.quartetValid d2.toNat && BaseN.Base4.quartetValid d3.toNat) = true
  · rw [ite_eq_left hgood] at h
    simp only [Bool.and_eq_true] at hgood
    obtain ⟨⟨⟨hg0, hg1⟩, hg2⟩, hg3⟩ := hgood
    injection h with hv
    subst hv
    rw [toNat_cons_some 4 d0 _ _ (digitVal_four_of_quartetValid d0 hg0),
        toNat_cons_some 4 d1 _ _ (digitVal_four_of_quartetValid d1 hg1),
        toNat_cons_some 4 d2 _ _ (digitVal_four_of_quartetValid d2 hg2),
        toNat_cons_some 4 d3 [] _ (digitVal_four_of_quartetValid d3 hg3),
        toNat_nil]
    simp only [Option.map_some]
    rw [UInt8.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by
      have l0 := BaseN.Base4.quartetValid_of_decide d0.toNat hg0
      have l1 := BaseN.Base4.quartetValid_of_decide d1.toNat hg1
      have l2 := BaseN.Base4.quartetValid_of_decide d2.toNat hg2
      have l3 := BaseN.Base4.quartetValid_of_decide d3.toNat hg3
      unfold BaseN.Base4.quartetsVal
      omega)]
    congr 1
    unfold BaseN.Base4.quartetsVal
    simp only [List.length_cons, List.length_nil, Nat.pow_zero, Nat.pow_succ, Nat.mul_one]
    omega
  · rw [ite_eq_right hgood] at h
    exact absurd h (by simp)

/-! ## Base 8 — the three-octal-digit block

Three digits, and — unlike bases 2 and 4 — the block guards `n ≤ 255` explicitly, because
three octal digits reach `511`. That guard is vacuous here (`octToVal ≤ 7` gives
`n ≤ 511`… so the guard is *not* vacuous) and it is why `→` needs the value bound rather
than only the digit bounds. -/

theorem digitVal_eight_shape (d : UInt8) :
    digitVal 8 d = (if inWin 48 55 d.toNat = true then some (d.toNat - 48) else none) := by
  rw [digitVal_eq]; simp

theorem octToVal_on {c : Nat} (h : inWin 48 55 c = true) :
    BaseN.Base8.octToVal c = c - 48 := by
  obtain ⟨hlo, hhi⟩ := inWin_eq_true h
  unfold BaseN.Base8.octToVal
  rw [ite_eq_left hhi, ite_eq_left hlo]

theorem octToVal_bounds (c : Nat) (h : BaseN.Base8.octToVal c ≤ 7) :
    48 ≤ c ∧ c ≤ 55 := by
  unfold BaseN.Base8.octToVal at h
  by_cases h1 : c ≤ 55
  · rw [ite_eq_left h1] at h
    by_cases h2 : 48 ≤ c
    · exact ⟨h2, h1⟩
    · rw [ite_eq_right h2] at h
      omega
  · rw [ite_eq_right h1] at h
    omega

theorem digitVal_eight_of_octValid (d : UInt8)
    (hv : BaseN.Base8.octValid d.toNat = true) :
    digitVal 8 d = some (BaseN.Base8.octToVal d.toNat) := by
  have hle := BaseN.Base8.octValid_of_decide d.toNat hv
  obtain ⟨hlo, hhi⟩ := octToVal_bounds d.toNat hle
  rw [digitVal_eight_shape]
  have hin : inWin 48 55 d.toNat = true := by rw [inWin_iff]; exact ⟨hlo, hhi⟩
  rw [hin]
  simp only [ite_true]
  rw [octToVal_on hin]

theorem octValid_of_digitVal (d : UInt8) (h : (digitVal 8 d).isSome = true) :
    BaseN.Base8.octValid d.toNat = true := by
  rw [digitVal_eight_shape] at h
  by_cases hin : inWin 48 55 d.toNat = true
  · obtain ⟨hlo, hhi⟩ := inWin_eq_true hin
    unfold BaseN.Base8.octValid
    show decide (BaseN.Base8.octToVal d.toNat ≤ 7) = true
    rw [octToVal_on hin]
    simp only [decide_eq_true_eq]
    omega
  · simp only [hin] at h
    exact absurd h (by simp)

/-- **The base-8 tie, `→`, with the domain hypothesis.** Three octal digits reach `511`, so
`octBlockApply` — whose codomain is `UInt8` — is **partial** on the numerals the fold
accepts. The paper models exactly this with a `Maybe` arrow (`PAPER.md`: `apply : α → Maybe β`),
so the domain condition `n ≤ 255` belongs in the *hypothesis*, which is what reading the
arrow correctly means; it is not a weakening of the law.

The rejection itself is a separate law (`octBlockApply_overflow` below), not a disjunct in
this conclusion: `apply` is a function, and a law stating `apply = some … ∨ apply = none` is
a case analysis on a result rather than the paper's `Just b → g b = Just a`. -/
theorem octBlockApply_of_toNat (d0 d1 d2 : UInt8) (n : Nat)
    (h : toNat 8 [d0, d1, d2] = some n) (hn : n ≤ 255) :
    BaseN.Base8.octBlockApply [d0, d1, d2] = some (UInt8.ofNat n) := by
  have hdig : BaseN.RadixCodec.isDigits 8 [d0, d1, d2] = true :=
    BaseN.RadixCodec.isDigits_of_toNat (by rw [h]; rfl)
  rw [BaseN.RadixCodec.isDigits_iff] at hdig
  have hv0 := octValid_of_digitVal d0 (hdig d0 (by simp))
  have hv1 := octValid_of_digitVal d1 (hdig d1 (by simp))
  have hv2 := octValid_of_digitVal d2 (hdig d2 (by simp))
  have hval := toNat_three 8 d0 d1 d2
      (BaseN.Base8.octToVal d0.toNat) (BaseN.Base8.octToVal d1.toNat)
      (BaseN.Base8.octToVal d2.toNat) n
      (digitVal_eight_of_octValid d0 hv0) (digitVal_eight_of_octValid d1 hv1)
      (digitVal_eight_of_octValid d2 hv2) h
  rw [BaseN.Base8.octBlockApply]
  simp only [hv0, hv1, hv2, Bool.and_self]
  rw [hval, natVal_three]
  simp only [Nat.reducePow, ite_true]
  have hn' : BaseN.Base8.octToVal d0.toNat * 64 + BaseN.Base8.octToVal d1.toNat * 8
      + BaseN.Base8.octToVal d2.toNat ≤ 255 := by
    rw [show BaseN.Base8.octToVal d0.toNat * 64 + BaseN.Base8.octToVal d1.toNat * 8
      + BaseN.Base8.octToVal d2.toNat
        = natVal 8 [BaseN.Base8.octToVal d0.toNat, BaseN.Base8.octToVal d1.toNat,
            BaseN.Base8.octToVal d2.toNat] from (natVal_three 8 _ _ _).symm]
    rw [← hval]
    exact hn
  rw [ite_eq_left hn']

/-- **The base-8 overflow law — `apply`'s domain, stated separately.**

Three octal digits reach `511`, so a block whose value exceeds `255` is a numeral the fold
accepts and the block *rejects*. This is the measured characterisation of the block's
domain: `octBlockApply` succeeds **exactly** when its value is at most `255` (verified over
all 512 digit triples), so this is a complete statement about the rejection rather than one
half of it.

Stated over the block's own value expression: the block binds that expression with a `let`,
so restating it as `n` first would shadow rather than connect. -/
theorem octBlockApply_overflow (d0 d1 d2 : UInt8)
    (h : 255 < BaseN.Base8.octToVal d0.toNat * 64 + BaseN.Base8.octToVal d1.toNat * 8
      + BaseN.Base8.octToVal d2.toNat)
    (hv : BaseN.Base8.octValid d0.toNat = true) (hv2 : BaseN.Base8.octValid d1.toNat = true)
    (hv3 : BaseN.Base8.octValid d2.toNat = true) :
    BaseN.Base8.octBlockApply [d0, d1, d2] = none := by
  rw [BaseN.Base8.octBlockApply]
  simp only [hv, hv2, hv3, Bool.and_self, ite_true]
  rw [ite_eq_right (by omega)]

/-- **The base-8 tie, `←`.** -/
theorem toNat_of_octBlockApply (d0 d1 d2 : UInt8) (v : UInt8)
    (h : BaseN.Base8.octBlockApply [d0, d1, d2] = some v) :
    toNat 8 [d0, d1, d2] = some v.toNat := by
  rw [BaseN.Base8.octBlockApply] at h
  by_cases hgood : (BaseN.Base8.octValid d0.toNat && BaseN.Base8.octValid d1.toNat &&
      BaseN.Base8.octValid d2.toNat) = true
  · rw [ite_eq_left hgood] at h
    simp only [Bool.and_eq_true] at hgood
    obtain ⟨⟨hg0, hg1⟩, hg2⟩ := hgood
    by_cases hle : BaseN.Base8.octToVal d0.toNat * 64 + BaseN.Base8.octToVal d1.toNat * 8
        + BaseN.Base8.octToVal d2.toNat ≤ 255
    · rw [ite_eq_left hle] at h
      injection h with hv
      subst hv
      rw [toNat_cons_some 8 d0 _ _ (digitVal_eight_of_octValid d0 hg0),
          toNat_cons_some 8 d1 _ _ (digitVal_eight_of_octValid d1 hg1),
          toNat_cons_some 8 d2 [] _ (digitVal_eight_of_octValid d2 hg2),
          toNat_nil]
      simp only [Option.map_some]
      rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      congr 1
      simp only [List.length_cons, List.length_nil, Nat.pow_zero, Nat.pow_succ, Nat.mul_one]
      omega
    · rw [ite_eq_right hle] at h
      exact absurd h (by simp)
  · rw [ite_eq_right hgood] at h
    exact absurd h (by simp)

/-! ## Base 16 — the two-nibble block

Two digits, and the only `_8` base whose alphabet has **two** windows (`0`–`9` and `A`–`F`),
so the digit bridge is a two-arm shape rather than base 2's single window. The digit-level
halves already exist in `Base16` (`hexToNibble_digit`, `hexToNibble_upper`), measured
`[propext, Quot.sound]`-only; what this section adds is the lift to `digitVal 16`.

**No overflow law here**, unlike base 8: two nibbles reach `15 * 16 + 15 = 255` exactly, so
`n ≤ 255` follows from the digit bounds and the strong form needs no hypothesis. -/

theorem digitVal_sixteen_shape (d : UInt8) :
    digitVal 16 d = (if inWin 48 57 d.toNat = true then some (d.toNat - 48)
      else if inWin 65 70 d.toNat = true then some (d.toNat - 55) else none) := by
  rw [digitVal_eq]; simp

/-- `hexToNibble` on either of its two windows, as one statement. -/
theorem hexToNibble_on {c : Nat} (h : inWin 48 57 c = true ∨ inWin 65 70 c = true) :
    BaseN.Base16.hexToNibble c = (if inWin 48 57 c = true then c - 48 else c - 55) := by
  rcases h with h | h
  · obtain ⟨hlo, hhi⟩ := inWin_eq_true h
    rw [BaseN.Base16.hexToNibble_digit c hlo hhi, ite_eq_left h]
  · obtain ⟨hlo, hhi⟩ := inWin_eq_true h
    have hnot : ¬ inWin 48 57 c = true := by
      rw [inWin_iff]; omega
    rw [BaseN.Base16.hexToNibble_upper c hlo hhi, ite_eq_right hnot]

/-- The two windows of base 16, recovered from the value being `≤ 15`. -/
theorem hexToNibble_window (c : Nat) (h : BaseN.Base16.hexToNibble c ≤ 15) :
    inWin 48 57 c = true ∨ inWin 65 70 c = true := by
  unfold BaseN.Base16.hexToNibble at h
  by_cases h1 : c ≤ 57
  · rw [ite_eq_left h1] at h
    by_cases h2 : 48 ≤ c
    · exact Or.inl (by rw [inWin_iff]; exact ⟨h2, h1⟩)
    · rw [ite_eq_right h2] at h
      exact absurd h (by omega)
  · rw [ite_eq_right h1] at h
    by_cases h2 : c ≤ 70
    · rw [ite_eq_left h2] at h
      by_cases h3 : 65 ≤ c
      · exact Or.inr (by rw [inWin_iff]; exact ⟨h3, h2⟩)
      · rw [ite_eq_right h3] at h
        exact absurd h (by omega)
    · rw [ite_eq_right h2] at h
      exact absurd h (by omega)

theorem digitVal_sixteen_of_hexNibbleValid (d : UInt8)
    (hv : BaseN.Base16.hexNibbleValid d.toNat = true) :
    digitVal 16 d = some (BaseN.Base16.hexToNibble d.toNat) := by
  have hle := BaseN.Base16.hexNibbleValid_of_decide d.toNat hv
  rcases hexToNibble_window d.toNat hle with hin | hin
  · rw [digitVal_sixteen_shape]
    rw [ite_eq_left hin]
    rw [hexToNibble_on (Or.inl hin), ite_eq_left hin]
  · have hnot : ¬ inWin 48 57 d.toNat = true := by
      rw [inWin_iff]; obtain ⟨a, b⟩ := inWin_eq_true hin; omega
    rw [digitVal_sixteen_shape]
    rw [ite_eq_right hnot]
    rw [ite_eq_left hin]
    rw [hexToNibble_on (Or.inr hin), ite_eq_right hnot]
theorem hexNibbleValid_of_digitVal_sixteen (d : UInt8)
    (h : (digitVal 16 d).isSome = true) : BaseN.Base16.hexNibbleValid d.toNat = true := by
  rw [digitVal_sixteen_shape] at h
  by_cases hd : inWin 48 57 d.toNat = true
  · obtain ⟨hlo, hhi⟩ := inWin_eq_true hd
    unfold BaseN.Base16.hexNibbleValid
    show decide (BaseN.Base16.hexToNibble d.toNat ≤ 15) = true
    rw [BaseN.Base16.hexToNibble_digit d.toNat hlo hhi]
    simp only [decide_eq_true_eq]
    omega
  · simp only [hd] at h
    by_cases hu : inWin 65 70 d.toNat = true
    · obtain ⟨hlo, hhi⟩ := inWin_eq_true hu
      unfold BaseN.Base16.hexNibbleValid
      show decide (BaseN.Base16.hexToNibble d.toNat ≤ 15) = true
      rw [BaseN.Base16.hexToNibble_upper d.toNat hlo hhi]
      simp only [decide_eq_true_eq]
      omega
    · simp only [hu] at h
      exact absurd h (by simp)

/-- **The base-16 tie, `→`.** Two nibbles reach exactly `255`, so there is no domain
hypothesis — the strong form of the paper's law, as for bases 2 and 4. -/
theorem hexBlockApply_of_toNat (d0 d1 : UInt8) (n : Nat)
    (h : toNat 16 [d0, d1] = some n) :
    BaseN.Base16.hexBlockApply [d0, d1] = some (UInt8.ofNat n) := by
  have hdig : BaseN.RadixCodec.isDigits 16 [d0, d1] = true :=
    BaseN.RadixCodec.isDigits_of_toNat (by rw [h]; rfl)
  rw [BaseN.RadixCodec.isDigits_iff] at hdig
  have hv0 := hexNibbleValid_of_digitVal_sixteen d0 (hdig d0 (by simp))
  have hv1 := hexNibbleValid_of_digitVal_sixteen d1 (hdig d1 (by simp))
  rw [BaseN.Base16.hexBlockApply]
  simp only [hv0, hv1, Bool.and_self, ite_true]
  have hval := toNat_two 16 d0 d1
      (BaseN.Base16.hexToNibble d0.toNat) (BaseN.Base16.hexToNibble d1.toNat) n
      (digitVal_sixteen_of_hexNibbleValid d0 hv0)
      (digitVal_sixteen_of_hexNibbleValid d1 hv1) h
  rw [hval, natVal_two]

/-- **The base-16 tie, `←`.** -/
theorem toNat_of_hexBlockApply (d0 d1 : UInt8) (v : UInt8)
    (h : BaseN.Base16.hexBlockApply [d0, d1] = some v) :
    toNat 16 [d0, d1] = some v.toNat := by
  rw [BaseN.Base16.hexBlockApply] at h
  by_cases hgood : (BaseN.Base16.hexNibbleValid d0.toNat &&
      BaseN.Base16.hexNibbleValid d1.toNat) = true
  · rw [ite_eq_left hgood] at h
    simp only [Bool.and_eq_true] at hgood
    obtain ⟨hg0, hg1⟩ := hgood
    injection h with hv
    subst hv
    rw [toNat_cons_some 16 d0 _ _ (digitVal_sixteen_of_hexNibbleValid d0 hg0),
        toNat_cons_some 16 d1 [] _ (digitVal_sixteen_of_hexNibbleValid d1 hg1),
        toNat_nil]
    simp only [Option.map_some]
    rw [UInt8.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by
      have l0 := BaseN.Base16.hexNibbleValid_of_decide d0.toNat hg0
      have l1 := BaseN.Base16.hexNibbleValid_of_decide d1.toNat hg1
      omega)]
    congr 1
    simp only [List.length_cons, List.length_nil, Nat.pow_zero, Nat.pow_succ, Nat.mul_one]
    omega
  · rw [ite_eq_right hgood] at h
    exact absurd h (by simp)

/-! ## Base 10 — the three-decimal-digit block

The mechanical repeat of base 8: three digits, `"999"` folds to `999`, so `digBlockApply`
— whose codomain is `UInt8` — is **partial** on the numerals the fold accepts. Same
repair as base 8 (design.md D6's third correction), and measured exhaustively rather
than argued: over all 1000 decimal digit triples `digBlockApply ds` succeeds **iff** its
value is at most `255`, so the overflow law below is a complete statement about the
block's domain rather than a sufficient condition. -/

theorem digitVal_ten_shape (d : UInt8) :
    digitVal 10 d = (if inWin 48 57 d.toNat = true then some (d.toNat - 48) else none) := by
  rw [digitVal_eq]; simp

theorem digVal_on {c : Nat} (h : inWin 48 57 c = true) :
    BaseN.Base10.digVal c = c - 48 := by
  obtain ⟨hlo, hhi⟩ := inWin_eq_true h
  unfold BaseN.Base10.digVal
  rw [ite_eq_left hhi, ite_eq_left hlo]

theorem digVal_bounds (c : Nat) (h : BaseN.Base10.digVal c ≤ 9) : 48 ≤ c ∧ c ≤ 57 := by
  unfold BaseN.Base10.digVal at h
  by_cases h1 : c ≤ 57
  · rw [ite_eq_left h1] at h
    by_cases h2 : 48 ≤ c
    · exact ⟨h2, h1⟩
    · rw [ite_eq_right h2] at h
      omega
  · rw [ite_eq_right h1] at h
    omega

theorem digitVal_ten_of_digValid (d : UInt8) (hv : BaseN.Base10.digValid d.toNat = true) :
    digitVal 10 d = some (BaseN.Base10.digVal d.toNat) := by
  have hle := BaseN.Base10.digValid_of_decide d.toNat hv
  obtain ⟨hlo, hhi⟩ := digVal_bounds d.toNat hle
  rw [digitVal_ten_shape]
  have hin : inWin 48 57 d.toNat = true := by rw [inWin_iff]; exact ⟨hlo, hhi⟩
  rw [hin]
  simp only [ite_true]
  rw [digVal_on hin]

theorem digValid_of_digitVal_ten (d : UInt8) (h : (digitVal 10 d).isSome = true) :
    BaseN.Base10.digValid d.toNat = true := by
  rw [digitVal_ten_shape] at h
  by_cases hin : inWin 48 57 d.toNat = true
  · obtain ⟨hlo, hhi⟩ := inWin_eq_true hin
    unfold BaseN.Base10.digValid
    show decide (BaseN.Base10.digVal d.toNat ≤ 9) = true
    rw [digVal_on hin]
    simp only [decide_eq_true_eq]
    omega
  · simp only [hin] at h
    exact absurd h (by simp)

/-- **The base-10 tie, `→`, with the domain hypothesis.** Three decimal digits reach `999`,
so `digBlockApply` is partial on the numerals the fold accepts, exactly as base 8 is. The
domain condition belongs in the hypothesis for the reason D6's third correction gives:
`PAPER.md`'s `apply : α → Maybe β` is a function, so a partial iso's domain is what the
arrow models. The rejection is `digBlockApply_overflow` below, not a disjunct here. -/
theorem digBlockApply_of_toNat (d0 d1 d2 : UInt8) (n : Nat)
    (h : toNat 10 [d0, d1, d2] = some n) (hn : n ≤ 255) :
    BaseN.Base10.digBlockApply [d0, d1, d2] = some (UInt8.ofNat n) := by
  have hdig : BaseN.RadixCodec.isDigits 10 [d0, d1, d2] = true :=
    BaseN.RadixCodec.isDigits_of_toNat (by rw [h]; rfl)
  rw [BaseN.RadixCodec.isDigits_iff] at hdig
  have hv0 := digValid_of_digitVal_ten d0 (hdig d0 (by simp))
  have hv1 := digValid_of_digitVal_ten d1 (hdig d1 (by simp))
  have hv2 := digValid_of_digitVal_ten d2 (hdig d2 (by simp))
  have hval := toNat_three 10 d0 d1 d2
      (BaseN.Base10.digVal d0.toNat) (BaseN.Base10.digVal d1.toNat)
      (BaseN.Base10.digVal d2.toNat) n
      (digitVal_ten_of_digValid d0 hv0) (digitVal_ten_of_digValid d1 hv1)
      (digitVal_ten_of_digValid d2 hv2) h
  rw [BaseN.Base10.digBlockApply]
  simp only [hv0, hv1, hv2, Bool.and_self, ite_true]
  rw [hval, natVal_three]
  simp only [Nat.reducePow]
  have hn' : BaseN.Base10.digVal d0.toNat * 100 + BaseN.Base10.digVal d1.toNat * 10
      + BaseN.Base10.digVal d2.toNat ≤ 255 := by
    rw [show BaseN.Base10.digVal d0.toNat * 100 + BaseN.Base10.digVal d1.toNat * 10
      + BaseN.Base10.digVal d2.toNat
        = natVal 10 [BaseN.Base10.digVal d0.toNat, BaseN.Base10.digVal d1.toNat,
            BaseN.Base10.digVal d2.toNat] from (natVal_three 10 _ _ _).symm]
    rw [← hval]
    exact hn
  rw [ite_eq_left hn']

/-- **The base-10 overflow law — `digBlockApply`'s domain, stated separately.**

Measured exhaustively over all 1000 decimal digit triples: the block succeeds **exactly
when** its value is at most `255`. So this is a complete characterisation of the block's
domain, matching base 8's `octBlockApply_overflow` in shape and reason. -/
theorem digBlockApply_overflow (d0 d1 d2 : UInt8)
    (h : 255 < BaseN.Base10.digVal d0.toNat * 100 + BaseN.Base10.digVal d1.toNat * 10
      + BaseN.Base10.digVal d2.toNat)
    (hv : BaseN.Base10.digValid d0.toNat = true) (hv2 : BaseN.Base10.digValid d1.toNat = true)
    (hv3 : BaseN.Base10.digValid d2.toNat = true) :
    BaseN.Base10.digBlockApply [d0, d1, d2] = none := by
  rw [BaseN.Base10.digBlockApply]
  simp only [hv, hv2, hv3, Bool.and_self, ite_true]
  rw [ite_eq_right (by omega)]

/-- **The base-10 tie, `←`.** -/
theorem toNat_of_digBlockApply (d0 d1 d2 : UInt8) (v : UInt8)
    (h : BaseN.Base10.digBlockApply [d0, d1, d2] = some v) :
    toNat 10 [d0, d1, d2] = some v.toNat := by
  rw [BaseN.Base10.digBlockApply] at h
  by_cases hgood : (BaseN.Base10.digValid d0.toNat && BaseN.Base10.digValid d1.toNat &&
      BaseN.Base10.digValid d2.toNat) = true
  · rw [ite_eq_left hgood] at h
    simp only [Bool.and_eq_true] at hgood
    obtain ⟨⟨hg0, hg1⟩, hg2⟩ := hgood
    by_cases hle : BaseN.Base10.digVal d0.toNat * 100 + BaseN.Base10.digVal d1.toNat * 10
        + BaseN.Base10.digVal d2.toNat ≤ 255
    · rw [ite_eq_left hle] at h
      injection h with hv
      subst hv
      rw [toNat_cons_some 10 d0 _ _ (digitVal_ten_of_digValid d0 hg0),
          toNat_cons_some 10 d1 _ _ (digitVal_ten_of_digValid d1 hg1),
          toNat_cons_some 10 d2 [] _ (digitVal_ten_of_digValid d2 hg2),
          toNat_nil]
      simp only [Option.map_some]
      rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      congr 1
      simp only [List.length_cons, List.length_nil, Nat.pow_zero, Nat.pow_succ, Nat.mul_one]
      omega
    · rw [ite_eq_right hle] at h
      exact absurd h (by simp)
  · rw [ite_eq_right hgood] at h
    exact absurd h (by simp)

/-! ## Bases 32 and 64 — schema `_L`

The last two ties, and the only ones whose block iso's codomain is `List UInt8` rather
than `UInt8`.

**D6's `_L` schema named `bytesOfNat` and `natOfBytes`, and neither exists in this tree.**
Stating the tie against them would have meant inventing two functions before it could be
written — the schema named its own preconditions. The statements below are against what the
code actually holds, which is the re-encode-and-compare pair `b{32,64}BlockApply` /
`b{32,64}BlockUnapply`, plus the **big-endian byte fold** `beVal` that both already rest on.

**The shape was decided against the code before any proof was attempted** (measured on the
shipped tree):

```
toNat 64 [81,81,81,81]             -> some 4260880
b64BlockApply [81,81,81,81]        -> some [65, 4, 16]      beVal [65,4,16] = 4260880   agree
toNat 32 [55,55,55,55,55,55,55,55] -> some 1099511627775
b32BlockApply ...                  -> some <5 bytes>        beVal ...     = same         agree
toNat 32 [77,89,61,61,61,61,61,61] -> none                 ('=' is not a base-32 digit)
b32BlockApply [77,89,61,...]       -> some [102]            the block accepts a pad the fold cannot read
```

So the tie is **`toNat b cs = some (beVal bs) ↔ blockApply cs = some bs`**, stated at each
block's literal arity and only on **pad-free** vectors. Padding is not a canonicity guard
here but an arity fact: `=` is outside the fold's alphabet, so a padded block is outside its
domain exactly as a short block is.

**There is no overflow law here, and that is arithmetic rather than an omission.** Base 32's
eight characters reach `32^8 - 1 = 1099511627775`, exactly `2^40 - 1` — a whole 5-byte
block; base 64's four reach `2^24 - 1` — a whole 3-byte block. Neither can overflow its
codomain, so the strong form needs no range hypothesis, unlike bases 8 and 10. -/

/-- The big-endian byte fold: the value a byte list denotes read as base 256. This is the
bridge between the block layer (which speaks bytes) and the fold (which speaks digits). -/
def beVal (bs : List UInt8) : Nat := bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- `beVal`'s fold carried from an arbitrary accumulator, stated against `natVal` so it closes
by **one** induction. The accumulator must be generalised: `beVal`'s own recursion starts from
a carried value rather than from `0`, so an induction at `acc = 0` does not reach the step —
which is why this lemma exists rather than a direct induction on `beVal`. -/
theorem beVal_foldl_eq (bs : List UInt8) (acc : Nat) :
    bs.foldl (fun a b => a * 256 + b.toNat) acc
      = acc * 256 ^ bs.length + natVal 256 (bs.map UInt8.toNat) := by
  induction bs generalizing acc with
  | nil => simp [natVal]
  | cons b bs ih =>
      rw [List.foldl_cons, ih (acc * 256 + b.toNat)]
      simp only [List.map_cons, natVal, List.length_cons, List.length_map, Nat.pow_succ]
      generalize 256 ^ bs.length = p at *
      generalize natVal 256 (List.map UInt8.toNat bs) = q at *
      have expand : (acc * 256 + b.toNat) * p = acc * 256 * p + b.toNat * p :=
        Nat.add_mul _ _ _
      rw [expand]
      rw [show (acc * 256 * p + b.toNat * p) + q
            = acc * 256 * p + (b.toNat * p + q) from Nat.add_assoc _ _ _]
      rw [show acc * (p * 256) = acc * 256 * p from by rw [Nat.mul_comm p 256, Nat.mul_assoc]]

/-- `beVal` is `natVal 256` of the bytes' values. -/
theorem beVal_eq_natVal (bs : List UInt8) : beVal bs = natVal 256 (bs.map UInt8.toNat) := by
  unfold beVal
  rw [beVal_foldl_eq bs 0]
  simp

theorem beVal_two (v0 v1 : UInt8) : beVal [v0, v1] = v0.toNat * 256 + v1.toNat := by
  simp [beVal]

theorem beVal_three (v0 v1 v2 : UInt8) :
    beVal [v0, v1, v2] = v0.toNat * 65536 + v1.toNat * 256 + v2.toNat := by
  simp [beVal]; omega

theorem beVal_five (v0 v1 v2 v3 v4 : UInt8) :
    beVal [v0, v1, v2, v3, v4] = v0.toNat * 4294967296 + v1.toNat * 16777216
      + v2.toNat * 65536 + v3.toNat * 256 + v4.toNat := by
  simp [beVal]; omega

/-- `valToB64` and `byteOfDigitNat 64` are the same alphabet — both are the RFC 4648
table. No bound hypothesis is needed: both are total `Nat → Nat` chains, so this is an
identity of the two definitions rather than a fact about a range. -/
theorem valToB64_eq_byteOfDigitNat (v : Nat) :
    BaseN.Base64.valToB64 v = byteOfDigitNat 64 v := by
  unfold BaseN.Base64.valToB64 byteOfDigitNat
  simp only [show ¬ (64 = 32) from by decide]
  repeat (split <;> (try rfl) <;> omega)

/-- `valToB32` and `byteOfDigitNat 32` are the same alphabet. -/
theorem valToB32_eq_byteOfDigitNat (v : Nat) :
    BaseN.Base32.valToB32 v = byteOfDigitNat 32 v := by
  unfold BaseN.Base32.valToB32 byteOfDigitNat
  repeat (split <;> (try rfl) <;> omega)

/-- The base-64 block's own encoding of three bytes, read by the **generic fold**: the
chars `unapply` writes are exactly `byteOfDigit 64` of the block's digit values, so the fold
lands on `beVal` of the bytes. This is the bridge the `_L` tie needs, and it is why
`valToB64_eq_byteOfDigitNat` was proved first. -/
theorem toNat_b64_unapply_three (b0 b1 b2 : UInt8) :
    toNat 64 [BaseN.Base64.toByte (BaseN.Base64.valToB64 (b0.toNat / 4)),
              BaseN.Base64.toByte (BaseN.Base64.valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16)),
              BaseN.Base64.toByte (BaseN.Base64.valToB64 ((b1.toNat % 16) * 4 + b2.toNat / 64)),
              BaseN.Base64.toByte (BaseN.Base64.valToB64 (b2.toNat % 64))]
      = some (beVal [b0, b1, b2]) := by
  have c0 : BaseN.Base64.toByte (BaseN.Base64.valToB64 (b0.toNat / 4))
      = byteOfDigit 64 (b0.toNat / 4) := by
    rw [valToB64_eq_byteOfDigitNat]; rfl
  have c1 : BaseN.Base64.toByte (BaseN.Base64.valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16))
      = byteOfDigit 64 ((b0.toNat % 4) * 16 + b1.toNat / 16) := by
    rw [valToB64_eq_byteOfDigitNat]; rfl
  have c2 : BaseN.Base64.toByte (BaseN.Base64.valToB64 ((b1.toNat % 16) * 4 + b2.toNat / 64))
      = byteOfDigit 64 ((b1.toNat % 16) * 4 + b2.toNat / 64) := by
    rw [valToB64_eq_byteOfDigitNat]; rfl
  have c3 : BaseN.Base64.toByte (BaseN.Base64.valToB64 (b2.toNat % 64))
      = byteOfDigit 64 (b2.toNat % 64) := by
    rw [valToB64_eq_byteOfDigitNat]; rfl
  rw [c0, c1, c2, c3]
  rw [← show (List.map (byteOfDigit 64) [b0.toNat / 4,
        (b0.toNat % 4) * 16 + b1.toNat / 16,
        (b1.toNat % 16) * 4 + b2.toNat / 64,
        b2.toNat % 64])
      = [byteOfDigit 64 (b0.toNat / 4), byteOfDigit 64 ((b0.toNat % 4) * 16 + b1.toNat / 16),
         byteOfDigit 64 ((b1.toNat % 16) * 4 + b2.toNat / 64),
         byteOfDigit 64 (b2.toNat % 64)] from rfl]
  have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
  have hb1 : b1.toNat < 256 := UInt8.toNat_lt b1
  have hb2 : b2.toNat < 256 := UInt8.toNat_lt b2
  rw [toNat_map_byteOfDigit (IsRadix.b64) _ (fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with hd | hd | hd | hd <;> subst hd
    · omega
    · omega
    · omega
    · omega)]
  rw [show beVal [b0, b1, b2] = b0.toNat * 65536 + b1.toNat * 256 + b2.toNat from
    beVal_three b0 b1 b2]
  simp only [natVal, List.length_cons, List.length_nil, Nat.pow_zero, Nat.pow_succ,
    Nat.mul_one, Nat.add_zero]
  rw [Option.some.injEq]
  omega

/-- **The base-64 tie, `→`, at the block's own encoding vector.**

Read as: the block's `apply` on the characters it itself writes for `bs` returns `bs`, and
the generic fold on those same characters returns `beVal bs`. So the two agree on every
vector the block itself produces.

**The statement is over that vector, not over every input the block accepts — and an earlier
version of this docstring claimed the latter, which is false.** Measured:

```
BaseN.Base64.b64BlockApply [90,103,61,61]  ->  some [102]    ("Zg==")
BaseN.Radix.toNat 64 [90,103,61,61]        ->  none
```

`=` is not in the fold's alphabet, so the 1- and 2-byte blocks are outside the fold's domain
even though the block accepts them. That is the pad-free restriction `toNat_of_b64BlockApply_three`
states on the other side; it is a genuine limitation of the tie, not an arity formality.

**No domain hypothesis**, unlike bases 8 and 10: four base-64 characters reach
`2^24 - 1 = 16777215`, exactly a whole 3-byte block, so the codomain cannot be
overflowed. -/
theorem b64BlockApply_of_toNat (b0 b1 b2 : UInt8) :
    toNat 64 [BaseN.Base64.toByte (BaseN.Base64.valToB64 (b0.toNat / 4)),
              BaseN.Base64.toByte (BaseN.Base64.valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16)),
              BaseN.Base64.toByte (BaseN.Base64.valToB64 ((b1.toNat % 16) * 4 + b2.toNat / 64)),
              BaseN.Base64.toByte (BaseN.Base64.valToB64 (b2.toNat % 64))]
        = some (beVal [b0, b1, b2])
    ∧ BaseN.Base64.b64BlockApply
        [BaseN.Base64.toByte (BaseN.Base64.valToB64 (b0.toNat / 4)),
         BaseN.Base64.toByte (BaseN.Base64.valToB64 ((b0.toNat % 4) * 16 + b1.toNat / 16)),
         BaseN.Base64.toByte (BaseN.Base64.valToB64 ((b1.toNat % 16) * 4 + b2.toNat / 64)),
         BaseN.Base64.toByte (BaseN.Base64.valToB64 (b2.toNat % 64))]
        = some [b0, b1, b2] := by
  refine ⟨toNat_b64_unapply_three b0 b1 b2, ?_⟩
  exact (BaseN.Base64.b64BlockIso_law _ _).2 rfl

/-- **The base-64 tie, `←`, on the pad-free block.** A 4-character base-64 block is pad-free
exactly when it encodes three bytes; the 1- and 2-byte blocks carry `=`, which is outside the
fold's alphabet, so those are outside its domain and this statement does not claim otherwise.

**That restriction is a canonicity divergence, not an arity fact.** An earlier version of this
docstring called it the latter and that was the error: `b64BlockApply [90,103,61,61]` (`"Zg=="`)
returns `some [102]`, so a short-tail block IS accepted by the block and IS unreadable by the
fold. The gap is the pad byte, which the block's own re-encode-and-compare guard admits and the
fold's alphabet does not contain. -/
theorem toNat_of_b64BlockApply_three (cs : List UInt8) (b0 b1 b2 : UInt8)
    (h : BaseN.Base64.b64BlockApply cs = some [b0, b1, b2]) :
    toNat 64 cs = some (beVal [b0, b1, b2]) := by
  have hun : BaseN.Base64.b64BlockUnapply [b0, b1, b2] = some cs :=
    (BaseN.Base64.b64BlockIso_law cs [b0, b1, b2]).1 h
  simp only [BaseN.Base64.b64BlockUnapply, Option.some.injEq] at hun
  rw [← hun]
  exact toNat_b64_unapply_three b0 b1 b2

/-- The base-32 block's own encoding of five bytes, read by the generic fold. Same bridge
as base 64's, one block wider: eight characters reaching `2^40 - 1`, exactly a 5-byte block,
so no domain hypothesis is needed. -/
theorem toNat_b32_unapply_five (b0 b1 b2 b3 b4 : UInt8) :
    toNat 32 [BaseN.Base32.toByte (BaseN.Base32.valToB32 (b0.toNat / 8)),
              BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)),
              BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b1.toNat / 2) % 32)),
              BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)),
              BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128)),
              BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b3.toNat / 4) % 32)),
              BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b3.toNat % 4) * 8 + b4.toNat / 32)),
              BaseN.Base32.toByte (BaseN.Base32.valToB32 (b4.toNat % 32))]
      = some (beVal [b0, b1, b2, b3, b4]) := by
  have hb0 : b0.toNat < 256 := UInt8.toNat_lt b0
  have hb1 : b1.toNat < 256 := UInt8.toNat_lt b1
  have hb2 : b2.toNat < 256 := UInt8.toNat_lt b2
  have hb3 : b3.toNat < 256 := UInt8.toNat_lt b3
  have hb4 : b4.toNat < 256 := UInt8.toNat_lt b4
  have c0 : BaseN.Base32.toByte (BaseN.Base32.valToB32 (b0.toNat / 8))
      = byteOfDigit 32 (b0.toNat / 8) := by rw [valToB32_eq_byteOfDigitNat]; rfl
  have c1 : BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64))
      = byteOfDigit 32 ((b0.toNat % 8) * 4 + b1.toNat / 64) := by
    rw [valToB32_eq_byteOfDigitNat]; rfl
  have c2 : BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b1.toNat / 2) % 32))
      = byteOfDigit 32 ((b1.toNat / 2) % 32) := by rw [valToB32_eq_byteOfDigitNat]; rfl
  have c3 : BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16))
      = byteOfDigit 32 ((b1.toNat % 2) * 16 + b2.toNat / 16) := by
    rw [valToB32_eq_byteOfDigitNat]; rfl
  have c4 : BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128))
      = byteOfDigit 32 ((b2.toNat % 16) * 2 + b3.toNat / 128) := by
    rw [valToB32_eq_byteOfDigitNat]; rfl
  have c5 : BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b3.toNat / 4) % 32))
      = byteOfDigit 32 ((b3.toNat / 4) % 32) := by rw [valToB32_eq_byteOfDigitNat]; rfl
  have c6 : BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b3.toNat % 4) * 8 + b4.toNat / 32))
      = byteOfDigit 32 ((b3.toNat % 4) * 8 + b4.toNat / 32) := by
    rw [valToB32_eq_byteOfDigitNat]; rfl
  have c7 : BaseN.Base32.toByte (BaseN.Base32.valToB32 (b4.toNat % 32))
      = byteOfDigit 32 (b4.toNat % 32) := by rw [valToB32_eq_byteOfDigitNat]; rfl
  rw [c0, c1, c2, c3, c4, c5, c6, c7]
  rw [← show (List.map (byteOfDigit 32) [b0.toNat / 8,
        (b0.toNat % 8) * 4 + b1.toNat / 64,
        (b1.toNat / 2) % 32,
        (b1.toNat % 2) * 16 + b2.toNat / 16,
        (b2.toNat % 16) * 2 + b3.toNat / 128,
        (b3.toNat / 4) % 32,
        (b3.toNat % 4) * 8 + b4.toNat / 32,
        b4.toNat % 32])
      = [byteOfDigit 32 (b0.toNat / 8), byteOfDigit 32 ((b0.toNat % 8) * 4 + b1.toNat / 64),
         byteOfDigit 32 ((b1.toNat / 2) % 32),
         byteOfDigit 32 ((b1.toNat % 2) * 16 + b2.toNat / 16),
         byteOfDigit 32 ((b2.toNat % 16) * 2 + b3.toNat / 128),
         byteOfDigit 32 ((b3.toNat / 4) % 32),
         byteOfDigit 32 ((b3.toNat % 4) * 8 + b4.toNat / 32),
         byteOfDigit 32 (b4.toNat % 32)] from rfl]
  rw [toNat_map_byteOfDigit (IsRadix.b32) _ (fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with hd | hd | hd | hd | hd | hd | hd | hd <;> subst hd <;> omega)]
  rw [show beVal [b0, b1, b2, b3, b4] = b0.toNat * 4294967296 + b1.toNat * 16777216
      + b2.toNat * 65536 + b3.toNat * 256 + b4.toNat from beVal_five b0 b1 b2 b3 b4]
  simp only [natVal, List.length_cons, List.length_nil, Nat.pow_zero, Nat.pow_succ,
    Nat.mul_one, Nat.add_zero]
  rw [Option.some.injEq]
  omega

/-- **The base-32 tie, `→`, at the block's own encoding vector.** Eight characters reach
`2^40 - 1`, exactly a whole 5-byte block, so there is no domain hypothesis — the strong form
of the paper's law, as for bases 2, 4 and 16. `b32BlockApply`'s re-encode-and-compare guard
is what makes the `←` direction hold without a range bound. -/
theorem b32BlockApply_of_toNat (b0 b1 b2 b3 b4 : UInt8) :
    toNat 32 [BaseN.Base32.toByte (BaseN.Base32.valToB32 (b0.toNat / 8)),
              BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)),
              BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b1.toNat / 2) % 32)),
              BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)),
              BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128)),
              BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b3.toNat / 4) % 32)),
              BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b3.toNat % 4) * 8 + b4.toNat / 32)),
              BaseN.Base32.toByte (BaseN.Base32.valToB32 (b4.toNat % 32))]
        = some (beVal [b0, b1, b2, b3, b4])
    ∧ BaseN.Base32.b32BlockApply
        [BaseN.Base32.toByte (BaseN.Base32.valToB32 (b0.toNat / 8)),
         BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b0.toNat % 8) * 4 + b1.toNat / 64)),
         BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b1.toNat / 2) % 32)),
         BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b1.toNat % 2) * 16 + b2.toNat / 16)),
         BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b2.toNat % 16) * 2 + b3.toNat / 128)),
         BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b3.toNat / 4) % 32)),
         BaseN.Base32.toByte (BaseN.Base32.valToB32 ((b3.toNat % 4) * 8 + b4.toNat / 32)),
         BaseN.Base32.toByte (BaseN.Base32.valToB32 (b4.toNat % 32))]
        = some [b0, b1, b2, b3, b4] := by
  refine ⟨toNat_b32_unapply_five b0 b1 b2 b3 b4, ?_⟩
  exact (BaseN.Base32.b32BlockIso_law _ _).2 rfl

/-- **The base-32 tie, `←`, on the pad-free block.** Eight base-32 characters are pad-free
exactly when they encode five bytes; shorter blocks carry `=`, outside the fold's alphabet,
so this statement is over the full 5-byte block only.

**That restriction is a canonicity divergence, not an arity fact** — the same correction as
`toNat_of_b64BlockApply_three`'s, and measured: `toNat 32 [77,89,61,61,61,61,61,61] = none`
(`'='` is not a base-32 digit) while `b32BlockApply` on it returns `some [102]`. -/
theorem toNat_of_b32BlockApply_five (cs : List UInt8) (b0 b1 b2 b3 b4 : UInt8)
    (h : BaseN.Base32.b32BlockApply cs = some [b0, b1, b2, b3, b4]) :
    toNat 32 cs = some (beVal [b0, b1, b2, b3, b4]) := by
  have hun : BaseN.Base32.b32BlockUnapply [b0, b1, b2, b3, b4] = some cs :=
    (BaseN.Base32.b32BlockIso_law cs [b0, b1, b2, b3, b4]).1 h
  simp only [BaseN.Base32.b32BlockUnapply, Option.some.injEq] at hun
  rw [← hun]
  exact toNat_b32_unapply_five b0 b1 b2 b3 b4

/-! ## The seven radix instances (task 3.1)

`numeralIso` is a single definition parameterised by the radix, so the "seven instances" are
its seven `IsRadix` witnesses. They are enumerated **once**, in `radixInstances`, so a missing
radix is a build failure rather than a shorter list — the "completeness claim that fails
silently" shape this repo has closed five times.

`IsRadix` is a `Prop`, so the enumeration is a `List Nat` plus a `∀` proof that each member is
an `IsRadix`; `radixInstances_length` asserts the count and `radixInstances_radices` asserts
the exact members, so the list cannot silently drift into a subset. -/

/-- The seven radices this layer serves. **One source**, so a missing radix is a build failure
and not a shorter list. -/
def radixInstances : List Nat := [2, 4, 8, 10, 16, 32, 64]

/-- Every enumerated radix carries its `IsRadix` witness, which is what `numeralIso` needs. -/
theorem radixInstances_areRadix : ∀ b ∈ radixInstances, IsRadix b := by
  intro b hb
  simp only [radixInstances, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact IsRadix.b2
  · exact IsRadix.b4
  · exact IsRadix.b8
  · exact IsRadix.b10
  · exact IsRadix.b16
  · exact IsRadix.b32
  · exact IsRadix.b64

/-- The enumeration is exactly the seven radices the spec names. -/
theorem radixInstances_length : radixInstances.length = 7 := rfl

/-- And they are those seven, in order — so the list cannot drift into a subset. -/
theorem radixInstances_radices : radixInstances = [2, 4, 8, 10, 16, 32, 64] := rfl

/-- `numeralIso` at an enumerated radix: the instance, with its witness supplied by
`radixInstances_areRadix` rather than by a literal at each call site. -/
def numeralIsoAt (b : Nat) (hb : b ∈ radixInstances) :
    Iso Nat (Codec.Normal (List UInt8) (BaseN.RadixCodec.normF b)) :=
  BaseN.RadixCodec.numeralIso b (radixInstances_areRadix b hb)

/-! ## The block isos, named by their `apply` projection (task 4.2's precondition)

Task 4.2 removes the seven block `Iso` values from `definitionSurfaceAllowlist`, on the
grounds that each gains a constraining theorem so the "no theorem names it" reason no longer
holds. **Measured, it did not hold after §3.2 as first written**: the ties name
`bitBlockApply`/`octBlockApply`/…, not `bitBlockIso`/`octBlockIso`/…, so the mention proxy
still saw the seven as unmentioned and the def arm refused the removal.

The fix is the one the task actually intends — make the theorems name the **value**. Each
`*BlockIso`'s `apply` is definitionally its `*BlockApply` (`rfl`), so these seven laws state
that, and they are what lets the allowlist drop the values without lying about them. -/

theorem bitBlockIso_apply (cs : List UInt8) :
    BaseN.Base2.bitBlockIso.apply cs = BaseN.Base2.bitBlockApply cs := rfl

theorem quartetBlockIso_apply (cs : List UInt8) :
    BaseN.Base4.quartetBlockIso.apply cs = BaseN.Base4.quartetBlockApply cs := rfl

theorem octBlockIso_apply (cs : List UInt8) :
    BaseN.Base8.octBlockIso.apply cs = BaseN.Base8.octBlockApply cs := rfl

theorem digBlockIso_apply (cs : List UInt8) :
    BaseN.Base10.digBlockIso.apply cs = BaseN.Base10.digBlockApply cs := rfl

theorem hexBlockIso_apply (cs : List UInt8) :
    BaseN.Base16.hexBlockIso.apply cs = BaseN.Base16.hexBlockApply cs := rfl

theorem b32BlockIso_apply (cs : List UInt8) :
    BaseN.Base32.b32BlockIso.apply cs = BaseN.Base32.b32BlockApply cs := rfl

theorem b64BlockIso_apply (cs : List UInt8) :
    BaseN.Base64.b64BlockIso.apply cs = BaseN.Base64.b64BlockApply cs := rfl

end BaseN.RadixTie










