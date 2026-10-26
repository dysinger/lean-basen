/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# BaseN.Base4

Quaternary encoding: one quartet (2 bits) per `0`-`3` character, **four**
characters per byte, MSB-first (`v/64`, `(v/16)%4`, `(v/4)%4`, `v%4`).  Four
quartets always span exactly one byte, so decoding needs no overflow check.

Not an RFC encoding; semantics are defined by this package's spec: "one quartet
per `0-3` char, 4 chars per byte".  Alphabet is ASCII `0-3` (48-51), all `< 256`.

This module expresses the base as a `codec` `Codec (List UInt8)` value
(`quartetElem`), composed from `satisfy` (one guarded quartet digit), `count 4`
(four quartets per byte block), and an `iso` that folds the four quartet values
into their byte (`q₀·64 + q₁·16 + q₂·4 + q₃`, no overflow check).  The unbounded
run is the productive repetition triple `relQuartet`/`decodeQuartet`/
`encodeQuartet` over `quartetElem`, whose roundtrip law is the *inherited*
`decodeRepeat_spec`/`encodeRepeat_rel` — no bespoke `encode`/`decode`.
-/

import BaseN.Common

namespace BaseN.Base4

open Codec
open BaseN.Common

/-! ## Digit-level arithmetic (`Nat`) -/

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

/-- `quartetValid e = true` implies `quartetVal e ≤ 3`. -/
theorem quartetValid_of_decide (e : Nat) (h : quartetValid e = true) : quartetVal e ≤ 3 :=
  of_decide_eq_true (by simpa [quartetValid] using h)

/-- When `e` is a valid quartet digit, `valToQuartet (quartetVal e) = e`. -/
theorem valToQuartet_quartetVal_of_valid (e : Nat) (h : quartetValid e = true) :
    valToQuartet (quartetVal e) = e := by
  have hv : quartetVal e ≤ 3 := quartetValid_of_decide e h
  unfold quartetVal valToQuartet
  by_cases hle : e ≤ 51
  · by_cases hge : 48 ≤ e
    · have hv' : e - 48 = quartetVal e := by simp [quartetVal, hle, hge]
      have hb : e - 48 ≤ 3 := by omega
      simp [hle, hge]
    · have : quartetVal e = 4 := by simp [quartetVal, hle, hge]
      omega
  · have : quartetVal e = 4 := by simp [quartetVal, hle]
    omega

/-- The `i`-th quartet (0-indexed from MSB) of `v`. -/
def quartetAt (v : Nat) (i : Nat) : Nat := (v / 4 ^ (3 - i)) % 4

/-- The 4 MSB-first quartets of `v` (values `0`/`3`). -/
def quartetsOf (v : Nat) : List Nat :=
  [quartetAt v 0, quartetAt v 1, quartetAt v 2, quartetAt v 3]

/-- The value of 4 MSB-first quartets `q0..q3`. -/
def quartetsVal (q0 q1 q2 q3 : Nat) : Nat :=
  q0 * 64 + q1 * 16 + q2 * 4 + q3

/-- Each `quartetAt` of a byte is `≤ 3`. -/
theorem quartetAt_le (v : Nat) (i : Nat) : quartetAt v i ≤ 3 := by
  unfold quartetAt
  omega

/-- `quartetsVal (quartetsOf v) = v` for `v < 256`. -/
theorem quartetsVal_quartetsOf (v : Nat) (hv : v < 256) :
    quartetsVal (quartetAt v 0) (quartetAt v 1) (quartetAt v 2) (quartetAt v 3) = v := by
  unfold quartetsVal quartetAt
  simp only [Nat.reducePow, Nat.reduceSub]
  omega

/-- Uniqueness of the quaternary decomposition: equal sums of quartet quadruples
(each `≤ 3`) give equal quadruples. -/
theorem quartets_decompose_unique (a0 a1 a2 a3 b0 b1 b2 b3 : Nat)
    (_ha0 : a0 ≤ 3) (_ha1 : a1 ≤ 3) (_ha2 : a2 ≤ 3) (_ha3 : a3 ≤ 3)
    (_hb0 : b0 ≤ 3) (_hb1 : b1 ≤ 3) (_hb2 : b2 ≤ 3) (_hb3 : b3 ≤ 3)
    (h : quartetsVal a0 a1 a2 a3 = quartetsVal b0 b1 b2 b3) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  have ha0' : a0 = b0 := by
    have hm := congrArg (fun x => x / 64) h
    unfold quartetsVal at hm
    omega
  have ha1' : a1 = b1 := by
    have hm := congrArg (fun x => (x % 64) / 16) h
    unfold quartetsVal at hm
    omega
  have ha2' : a2 = b2 := by
    have hm := congrArg (fun x => (x % 16) / 4) h
    unfold quartetsVal at hm
    omega
  have ha3' : a3 = b3 := by
    have hm := congrArg (fun x => x % 4) h
    unfold quartetsVal at hm
    omega
  exact ⟨ha0', ha1', ha2', ha3'⟩

/-! ## The block isomorphism -/

/-- The quartet digit predicate over `UInt8`. -/
def quartetDigit (b : UInt8) : Bool := quartetValid b.toNat

/-- `toByte (valToQuartet d)` — the byte embedding, for `d ≤ 3`. -/
private theorem toByte_valToQuartet (b : Nat) (hb : b ≤ 3) :
    (toByte (valToQuartet b)).toNat = valToQuartet b := by
  unfold toByte
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToQuartet_lt_256 b hb)]

/-- `quartetVal ((toByte (valToQuartet d)).toNat) = d` for `d ≤ 3`. -/
theorem quartetVal_toByte_valToQuartet (d : Nat) (hd : d ≤ 3) :
    quartetVal (toByte (valToQuartet d)).toNat = d := by
  rw [toByte_valToQuartet d hd]
  exact quartetVal_valToQuartet d hd

/-- `apply`: read four quartet digits and fold them into their byte. -/
def quartetBlockApply (cs : List UInt8) : Option UInt8 :=
  match cs with
  | [d0, d1, d2, d3] =>
      if quartetValid d0.toNat && quartetValid d1.toNat && quartetValid d2.toNat && quartetValid d3.toNat then
        let n := quartetsVal (quartetVal d0.toNat) (quartetVal d1.toNat) (quartetVal d2.toNat) (quartetVal d3.toNat)
        some (UInt8.ofNat n)
      else none
  | _ => none

/-- `unapply`: write a byte as its four MSB-first quartet digits (always valid). -/
def quartetBlockUnapply (b : UInt8) : Option (List UInt8) :=
  some [toByte (valToQuartet (quartetAt b.toNat 0)),
        toByte (valToQuartet (quartetAt b.toNat 1)),
        toByte (valToQuartet (quartetAt b.toNat 2)),
        toByte (valToQuartet (quartetAt b.toNat 3))]

/-- Each digit byte of `quartetBlockUnapply b` is valid. -/
theorem quartetDigit_valid_of_byte (b : UInt8) :
    quartetValid (toByte (valToQuartet (quartetAt b.toNat 0))).toNat = true ∧
    quartetValid (toByte (valToQuartet (quartetAt b.toNat 1))).toNat = true ∧
    quartetValid (toByte (valToQuartet (quartetAt b.toNat 2))).toNat = true ∧
    quartetValid (toByte (valToQuartet (quartetAt b.toNat 3))).toNat = true := by
  have h0 := quartetAt_le b.toNat 0
  have h1 := quartetAt_le b.toNat 1
  have h2 := quartetAt_le b.toNat 2
  have h3 := quartetAt_le b.toNat 3
  constructor
  · rw [toByte_valToQuartet (quartetAt b.toNat 0) h0]; exact valToQuartet_valid (quartetAt b.toNat 0) h0
  constructor
  · rw [toByte_valToQuartet (quartetAt b.toNat 1) h1]; exact valToQuartet_valid (quartetAt b.toNat 1) h1
  constructor
  · rw [toByte_valToQuartet (quartetAt b.toNat 2) h2]; exact valToQuartet_valid (quartetAt b.toNat 2) h2
  · rw [toByte_valToQuartet (quartetAt b.toNat 3) h3]; exact valToQuartet_valid (quartetAt b.toNat 3) h3

/-- `apply` is a left inverse of `unapply`. -/
theorem quartetBlockApply_unapply (b : UInt8) :
    quartetBlockApply [toByte (valToQuartet (quartetAt b.toNat 0)),
                       toByte (valToQuartet (quartetAt b.toNat 1)),
                       toByte (valToQuartet (quartetAt b.toNat 2)),
                       toByte (valToQuartet (quartetAt b.toNat 3))] = some b := by
  have hbv : b.toNat < 256 := UInt8.toNat_lt b
  have h0 := quartetAt_le b.toNat 0
  have h1 := quartetAt_le b.toNat 1
  have h2 := quartetAt_le b.toNat 2
  have h3 := quartetAt_le b.toNat 3
  rw [quartetBlockApply]
  rw [quartetVal_toByte_valToQuartet (quartetAt b.toNat 0) h0,
      quartetVal_toByte_valToQuartet (quartetAt b.toNat 1) h1,
      quartetVal_toByte_valToQuartet (quartetAt b.toNat 2) h2,
      quartetVal_toByte_valToQuartet (quartetAt b.toNat 3) h3]
  have hvd := quartetDigit_valid_of_byte b
  rw [hvd.1, hvd.2.1, hvd.2.2.1, hvd.2.2.2]
  have hh : (true && true && true && true) = true := by decide
  rw [hh]
  have hsum : quartetsVal (quartetAt b.toNat 0) (quartetAt b.toNat 1) (quartetAt b.toNat 2) (quartetAt b.toNat 3) = b.toNat :=
    quartetsVal_quartetsOf b.toNat hbv
  rw [hsum]
  simp

/-- The inverse law of the quartet block: `apply` and `unapply` are mutual inverses. -/
theorem quartetBlockIso_law (cs : List UInt8) (b : UInt8) :
    quartetBlockApply cs = some b ↔ quartetBlockUnapply b = some cs := by
  constructor
  · intro h
    cases cs with
    | nil => simp [quartetBlockApply] at h
    | cons d0 rest =>
        cases rest with
        | nil => simp [quartetBlockApply] at h
        | cons d1 rest2 =>
            cases rest2 with
            | nil => simp [quartetBlockApply] at h
            | cons d2 rest3 =>
                cases rest3 with
                | nil => simp [quartetBlockApply] at h
                | cons d3 rest4 =>
                    cases rest4 with
                    | nil =>
                        rw [quartetBlockApply] at h
                        by_cases hv : quartetValid d0.toNat && quartetValid d1.toNat && quartetValid d2.toNat && quartetValid d3.toNat
                        · simp only [hv, ite_true] at h
                          have hb_eq : UInt8.ofNat (quartetsVal (quartetVal d0.toNat) (quartetVal d1.toNat) (quartetVal d2.toNat) (quartetVal d3.toNat)) = b := by
                            exact Option.some.inj h
                          have hv' : (((quartetValid d0.toNat = true ∧ quartetValid d1.toNat = true) ∧
                              quartetValid d2.toNat = true) ∧ quartetValid d3.toNat = true) := by
                            simpa only [Bool.and_eq_true_iff] using hv
                          have hvd0 : quartetValid d0.toNat = true := hv'.1.1.1
                          have hvd1 : quartetValid d1.toNat = true := hv'.1.1.2
                          have hvd2 : quartetValid d2.toNat = true := hv'.1.2
                          have hvd3 : quartetValid d3.toNat = true := hv'.2
                          have v0le := quartetValid_of_decide d0.toNat hvd0
                          have v1le := quartetValid_of_decide d1.toNat hvd1
                          have v2le := quartetValid_of_decide d2.toNat hvd2
                          have v3le := quartetValid_of_decide d3.toNat hvd3
                          have hb : b.toNat = quartetsVal (quartetVal d0.toNat) (quartetVal d1.toNat) (quartetVal d2.toNat) (quartetVal d3.toNat) := by
                            have hbt := congrArg UInt8.toNat hb_eq
                            rw [UInt8.toNat_ofNat'] at hbt
                            have hbnd : quartetsVal (quartetVal d0.toNat) (quartetVal d1.toNat) (quartetVal d2.toNat) (quartetVal d3.toNat) < 256 := by
                              unfold quartetsVal
                              omega
                            rw [Nat.mod_eq_of_lt hbnd] at hbt
                            exact hbt.symm
                          have hdev : quartetVal d0.toNat = quartetAt b.toNat 0 ∧ quartetVal d1.toNat = quartetAt b.toNat 1 ∧
                                      quartetVal d2.toNat = quartetAt b.toNat 2 ∧ quartetVal d3.toNat = quartetAt b.toNat 3 := by
                            have hbit0 := quartetAt_le b.toNat 0
                            have hbit1 := quartetAt_le b.toNat 1
                            have hbit2 := quartetAt_le b.toNat 2
                            have hbit3 := quartetAt_le b.toNat 3
                            have hb' : quartetsVal (quartetVal d0.toNat) (quartetVal d1.toNat) (quartetVal d2.toNat) (quartetVal d3.toNat)
                              = quartetsVal (quartetAt b.toNat 0) (quartetAt b.toNat 1) (quartetAt b.toNat 2) (quartetAt b.toNat 3) := by
                              rw [quartetsVal_quartetsOf b.toNat (UInt8.toNat_lt b)]
                              exact hb.symm
                            exact quartets_decompose_unique
                              (quartetVal d0.toNat) (quartetVal d1.toNat) (quartetVal d2.toNat) (quartetVal d3.toNat)
                              (quartetAt b.toNat 0) (quartetAt b.toNat 1) (quartetAt b.toNat 2) (quartetAt b.toNat 3)
                              v0le v1le v2le v3le
                              hbit0 hbit1 hbit2 hbit3
                              hb'
                          rw [quartetBlockUnapply]
                          have hd0 : d0.toNat = valToQuartet (quartetVal d0.toNat) :=
                            (valToQuartet_quartetVal_of_valid d0.toNat hvd0).symm
                          have hd1 : d1.toNat = valToQuartet (quartetVal d1.toNat) :=
                            (valToQuartet_quartetVal_of_valid d1.toNat hvd1).symm
                          have hd2 : d2.toNat = valToQuartet (quartetVal d2.toNat) :=
                            (valToQuartet_quartetVal_of_valid d2.toNat hvd2).symm
                          have hd3 : d3.toNat = valToQuartet (quartetVal d3.toNat) :=
                            (valToQuartet_quartetVal_of_valid d3.toNat hvd3).symm
                          rw [← hdev.1, ← hdev.2.1, ← hdev.2.2.1, ← hdev.2.2.2]
                          rw [← hd0, ← hd1, ← hd2, ← hd3]
                          simp [toByte]
                        · simp [hv] at h
                    | cons _ _ => simp [quartetBlockApply] at h
  · intro h
    rw [quartetBlockUnapply] at h
    cases h
    exact quartetBlockApply_unapply b

/-- The four-quartet block ↔ one byte partial isomorphism. -/
def quartetBlockIso : Iso (List UInt8) UInt8 :=
  { apply := quartetBlockApply, unapply := quartetBlockUnapply, law := quartetBlockIso_law }

/-- The base4 element: four quartet digit bytes grouped into one byte. -/
def quartetElem : Codec UInt8 := Codec.iso quartetBlockIso (count 4 (Codec.satisfy quartetDigit))

/-- `quartetElem` is productive, hence a `ConsumesByte` witness. -/
theorem quartetConsumesByte : ConsumesByte quartetElem := by
  unfold quartetElem
  rw [← productive_iff_consumesByte (Codec.iso quartetBlockIso (count 4 (Codec.satisfy quartetDigit)))]
  apply Productive_iso quartetBlockIso (count 4 (Codec.satisfy quartetDigit))
  rw [show 4 = 3 + 1 by rfl]
  exact Productive_count_satisfy_succ quartetDigit 3

/-- The base4 run value: the element + productivity witness. -/
def quartetRun : Run UInt8 := { elem := quartetElem, step := quartetConsumesByte }

/-- The base4 decoder. -/
def decodeQuartet {n : Nat} (s : Bytes n) : List (List UInt8 × Suffix n) :=
  decodeRepeat quartetElem quartetConsumesByte n s

/-- The base4 encoder. -/
def encodeQuartet (bs : List UInt8) : Option (Sigma fun n => Bytes n) :=
  encodeRepeat quartetElem bs

/-- The base4 relation. -/
def relQuartet : List UInt8 → (n : Nat) → Bytes n → Prop :=
  relRepeat (Rel quartetElem)

/-! ## Unambiguity and the inherited roundtrip law -/

/-- `quartetElem` is unambiguous. -/
theorem quartetElem_unambiguous : Unambiguous quartetElem := by
  unfold quartetElem
  apply Unambiguous_iso quartetBlockIso (count 4 (Codec.satisfy quartetDigit))
  exact count_satisfy_unambiguous quartetDigit 4

/-- `Rel quartetElem x s` pins the byte length: `n = 4`. -/
theorem Rel_quartetElem_len (x : UInt8) {n : Nat} (s : Bytes n) :
    Rel quartetElem x s → n = 4 := by
  intro h
  unfold quartetElem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, _, hc⟩
  exact Rel_count_satisfy_len quartetDigit 4 a s hc

/-- The base4 relation is unambiguous. -/
theorem relQuartet_unambiguous : relUnambiguous relQuartet := by
  intro a b n s ha hb
  dsimp [relQuartet] at ha hb
  induction a generalizing b n s with
  | nil =>
      rw [relRepeat_nil] at ha
      subst n
      cases b with
      | nil => rfl
      | cons y ys =>
          rw [relRepeat_cons] at hb
          rcases hb with ⟨m, hm, s₁, s₂, hs, hy, _⟩
          have hlen : m = 4 := Rel_quartetElem_len y s₁ hy
          have hm0 : m = 0 := by omega
          omega
  | cons x xs ih =>
      cases b with
      | nil =>
          rw [relRepeat_nil] at hb
          rw [relRepeat_cons] at ha
          rcases ha with ⟨mx, hmx, s₁x, s₂x, hsx, hx, hxs⟩
          have hlen : mx = 4 := Rel_quartetElem_len x s₁x hx
          subst n
          have hm0 : mx = 0 := by omega
          omega
      | cons y ys =>
          rw [relRepeat_cons] at ha hb
          rcases ha with ⟨mx, hmx, s₁x, s₂x, hsx, hx, hxs⟩
          rcases hb with ⟨my, hmy, s₁y, s₂y, hsy, hy, hys⟩
          have hlx : mx = 4 := Rel_quartetElem_len x s₁x hx
          have hly : my = 4 := Rel_quartetElem_len y s₁y hy
          subst mx
          subst my
          have hpre : s₁x = s₁y := by
            apply Bytes.ext
            intro i
            have hin : i.val < n := Nat.lt_of_lt_of_le i.isLt hmx
            have hx' : s ⟨i.val, hin⟩ = s₁x i := by
              rw [hsx]
              exact splice_prefix_read hmx s₁x s₂x ⟨i.val, hin⟩ i.isLt
            have hy' : s ⟨i.val, hin⟩ = s₁y i := by
              rw [hsy]
              exact splice_prefix_read hmy s₁y s₂y ⟨i.val, hin⟩ i.isLt
            exact hx'.symm.trans hy'
          have htaily : s₂x = s₂y := by
            rw [← bdrop_splice hmx s₁x s₂x, ← bdrop_splice hmy s₁y s₂y]
            congr 1
            rw [← hsx]
            rw [hsy]
          have hhead : x = y := by
            exact quartetElem_unambiguous s₁x hx (by rw [hpre]; exact hy)
          have htail : xs = ys := by
            exact ih s₂x hxs (by simpa [htaily] using hys)
          rw [hhead, htail]

/-- Full-consumption decode is unambiguous for `quartetElem`. -/
theorem quartetDecodeFull_unambiguous {x y : List UInt8} {n : Nat} (s : Bytes n) :
    (x, Suffix.empty n) ∈ decodeRepeat quartetElem quartetConsumesByte n s →
    (y, Suffix.empty n) ∈ decodeRepeat quartetElem quartetConsumesByte n s → x = y := by
  intro hx hy
  rcases (decodeRepeat_spec quartetElem quartetConsumesByte x n s (Suffix.empty n)).1 hx with ⟨s₀x, hsx, hrx⟩
  rcases (decodeRepeat_spec quartetElem quartetConsumesByte y n s (Suffix.empty n)).1 hy with ⟨s₀y, hsy, hry⟩
  have hs₀ : s₀x = s₀y := by
    have hpre : (Suffix.empty n).prepend s₀x = (Suffix.empty n).prepend s₀y := by
      exact hsx.symm.trans hsy
    exact prepend_prefix_eq (Suffix.empty n) s₀x s₀y hpre
  exact relQuartet_unambiguous s₀x hrx (by rw [hs₀]; exact hry)

/-- The base4 roundtrip law. `[propext, Quot.sound]`-only. -/
theorem roundtrip (bs : List UInt8) {n : Nat} {s : Bytes n} :
    encodeQuartet bs = some ⟨n, s⟩ → decodeFull quartetElem quartetConsumesByte n s = some bs := by
  intro he
  have hrel : relRepeat (Rel quartetElem) bs n s := encodeRepeat_rel quartetElem bs he
  have hmem : (bs, Suffix.empty n) ∈ decodeRepeat quartetElem quartetConsumesByte n s := by
    refine (decodeRepeat_spec quartetElem quartetConsumesByte bs n s (Suffix.empty n)).2 ⟨
      cast (congrArg Bytes (Nat.sub_zero n).symm) s, ?_, ?_⟩
    · exact (prepend_empty_eq s).symm
    · exact (relRepeat_cast (Rel quartetElem) bs (Nat.sub_zero n).symm s).2 hrel
  exact (decodeFull_spec quartetElem quartetConsumesByte (fun {x y} {m} (t : Bytes m) =>
    quartetDecodeFull_unambiguous (s := t)) s bs).2 hmem

/-! ## Conformance: canonical encoding, converse, injectivity -/

/-- `quartetElem` is functional: one byte relates to a unique 4-byte string. -/
theorem quartetElem_functional : Functional quartetElem := by
  unfold quartetElem
  exact Functional_iso quartetBlockIso (count 4 (Codec.satisfy quartetDigit))
    (Functional_count_satisfy quartetDigit 4)

/-- Every byte of a `quartetElem`-related string is a quartet digit. -/
theorem Rel_quartetElem_canonical {x : UInt8} {m : Nat} {t : Bytes m} :
    Rel quartetElem x t → ∀ i : Fin m, quartetDigit (t i) = true := by
  intro ht
  change Rel (Codec.iso quartetBlockIso (count 4 (Codec.satisfy quartetDigit))) x t at ht
  rw [Rel_iso] at ht
  rcases ht with ⟨a, _, hc⟩
  exact Rel_count_satisfy_forall quartetDigit 4 a t hc

/-- Canonical encoding (alphabet-only): every byte `encodeQuartet` produces is a
quartet digit. `[propext, Quot.sound]`-only. -/
theorem encodeQuartet_canonical (bs : List UInt8) {n : Nat} {s : Bytes n} :
    encodeQuartet bs = some ⟨n, s⟩ → ∀ i : Fin n, quartetDigit (s i) = true := by
  intro he
  have hrel : relRepeat (Rel quartetElem) bs n s := encodeRepeat_rel quartetElem bs he
  exact relRepeat_forall quartetDigit (fun x {m} t ht => Rel_quartetElem_canonical (t := t) ht) bs n s hrel

/-- Converse: a fully-decoded value re-encodes to exactly the input bytes. -/
theorem decode_encode_inverse {n : Nat} {s : Bytes n} (v : List UInt8) :
    decodeFull quartetElem quartetConsumesByte n s = some v → encodeQuartet v = some ⟨n, s⟩ := by
  intro hd
  have hmem : (v, Suffix.empty n) ∈ decodeRepeat quartetElem quartetConsumesByte n s :=
    decodeFull_some quartetElem quartetConsumesByte s v hd
  rcases (decodeRepeat_spec quartetElem quartetConsumesByte v n s (Suffix.empty n)).1 hmem with ⟨s₀, hs, hrel⟩
  have hne : s = cast (congrArg Bytes (Nat.sub_zero n)) s₀ := by
    rw [hs]
    exact prepend_empty_eq s₀
  have hrels : relRepeat (Rel quartetElem) v n s := by
    rw [hne]
    exact (relRepeat_cast (Rel quartetElem) v (Nat.sub_zero n) s₀).1 hrel
  exact encodeRepeat_of_rel quartetElem quartetElem_functional v s hrels

/-- `quartetBlockUnapply` is *total*, and its digits are exactly the 4 digits of the
byte: length 4, every one a `quartetDigit`. This is what makes `quartetElem`'s
encoder total — its only failure mode would be a produced digit failing
`satisfy`. -/
theorem quartetBlockUnapply_digits (b : UInt8) :
    ∃ ds, quartetBlockUnapply b = some ds ∧ ds.length = 4 ∧ ∀ d ∈ ds, quartetDigit d = true := by
  refine ⟨[toByte (valToQuartet (quartetAt b.toNat 0)), toByte (valToQuartet (quartetAt b.toNat 1)), toByte (valToQuartet (quartetAt b.toNat 2)), toByte (valToQuartet (quartetAt b.toNat 3))], rfl, rfl, ?_⟩
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  unfold quartetDigit
  rcases hd with h | h | h | h <;> subst h
  · exact (quartetDigit_valid_of_byte b).1
  · exact (quartetDigit_valid_of_byte b).2.1
  · exact (quartetDigit_valid_of_byte b).2.2.1
  · exact (quartetDigit_valid_of_byte b).2.2.2

/-- Every byte encodes through `quartetElem`: the element encoder is total. -/
theorem quartetElem_encode_ne_none (b : UInt8) : Codec.encode quartetElem b ≠ none := by
  obtain ⟨ds, hds, hlen, hpd⟩ := quartetBlockUnapply_digits b
  unfold quartetElem
  simp only [Codec.encode, quartetBlockIso, hds, Option.bind]
  rw [← hlen]
  exact count_satisfy_encode_ne_none quartetDigit ds hpd

/-- **Quartet encoding is total** — `encodeQuartet` never returns `none`.

This is the fact that upgrades the injectivity law to the spec's plain
`Option`-equality form (task 6.2): with totality in hand the `none`/`none` and
`some`/`none` cases of `encodeQuartet v = encodeQuartet v'` are refuted, leaving only
the both-succeed case, which is `encode_injective`.

`encodeRepeat` fails only when the element encoder does, so this is an induction
on the value list with `quartetElem_encode_ne_none` at each step.
`[propext, Quot.sound]`-only. -/
theorem encodeQuartet_ne_none (bs : List UInt8) : encodeQuartet bs ≠ none := by
  unfold encodeQuartet
  induction bs with
  | nil => simp [Codec.encodeRepeat]
  | cons b rest ih =>
      rw [Codec.encodeRepeat]
      have hb : Codec.encode quartetElem b ≠ none := quartetElem_encode_ne_none b
      cases h₁ : Codec.encode quartetElem b with
      | none => exact absurd h₁ hb
      | some e₁ =>
          cases h₂ : Codec.encodeRepeat quartetElem rest with
          | none => exact absurd h₂ ih
          | some e₂ => simp

/-- encoding is injective: a byte list has a unique quartet encoding (the
both-succeed form, which the spec's `Option`-equality law reduces to). -/
theorem encode_injective {v v' : List UInt8} {n : Nat} {s : Bytes n} :
    encodeQuartet v = some ⟨n, s⟩ → encodeQuartet v' = some ⟨n, s⟩ → v = v' := by
  intro hv hv'
  have hrelv : relRepeat (Rel quartetElem) v n s := encodeRepeat_rel quartetElem v hv
  have hrelv' : relRepeat (Rel quartetElem) v' n s := encodeRepeat_rel quartetElem v' hv'
  exact relQuartet_unambiguous s hrelv hrelv'

/-- **Quartet encoding is injective, in the spec's `Option`-equality form:**
`encodeQuartet v = encodeQuartet v' → v = v'` — exactly the `basen` spec's Scenario
"Encoding is injective" (`encode{X} v = encode{X} v' → v = v'`).

Because `encodeQuartet` is total (`encodeQuartet_ne_none`), the left side cannot be
`none`; destructure the common result and hand both successes to
`encode_injective`. `[propext, Quot.sound]`-only. -/
theorem encodeQuartet_injective_eq {v v' : List UInt8} (h : encodeQuartet v = encodeQuartet v') :
    v = v' := by
  cases hv : encodeQuartet v with
  | none => exact absurd hv (encodeQuartet_ne_none v)
  | some e =>
      rcases e with ⟨n, s⟩
      have hv' : encodeQuartet v' = some ⟨n, s⟩ := by rw [← h]; exact hv
      exact encode_injective hv hv'

/-- A fully-decoded value means every input byte is a quartet digit. `[propext,
Quot.sound]`-only. -/
theorem decodeFull_canonical {n : Nat} {s : Bytes n} {v : List UInt8} :
    decodeFull quartetElem quartetConsumesByte n s = some v → ∀ i : Fin n, quartetDigit (s i) = true := by
  intro hd
  have hmem : (v, Suffix.empty n) ∈ decodeRepeat quartetElem quartetConsumesByte n s :=
    decodeFull_some quartetElem quartetConsumesByte s v hd
  rcases (decodeRepeat_spec quartetElem quartetConsumesByte v n s (Suffix.empty n)).1 hmem with ⟨s₀, hs, hrel⟩
  have hne : s = cast (congrArg Bytes (Nat.sub_zero n)) s₀ := by
    rw [hs]
    exact prepend_empty_eq s₀
  have hrels : relRepeat (Rel quartetElem) v n s := by
    rw [hne]
    exact (relRepeat_cast (Rel quartetElem) v (Nat.sub_zero n) s₀).1 hrel
  exact relRepeat_forall quartetDigit (fun x {m} t ht => Rel_quartetElem_canonical (t := t) ht) v n s hrels

/-- **Base4: decode succeeds iff `s` is in `encodeQuartet`'s image, at that value.**
`decodeFull quartetElem quartetConsumesByte n s = some v ↔ ∃ v', encodeQuartet v' = some ⟨n, s⟩ ∧ v = v'`.

The base-4 analogue of `decodeFullB64_char`/`decodeFullB32_char` (task 7.1): the
decoder accepts a byte string exactly when it is a canonical encoding, and then
returns the unique value that encodes to it. Pure assembly over the already-proved
`decode_encode_inverse` (`→`) and `roundtrip` (`←`). `[propext, Quot.sound]`-only. -/
theorem decodeFull_B4_char {n : Nat} (s : Bytes n) (v : List UInt8) :
    decodeFull quartetElem quartetConsumesByte n s = some v ↔ ∃ v', encodeQuartet v' = some ⟨n, s⟩ ∧ v = v' := by
  constructor
  · intro h
    exact ⟨v, decode_encode_inverse v h, rfl⟩
  · rintro ⟨w, he, hv⟩
    rw [hv]
    exact roundtrip w he

/-- Rejection: a byte outside the quartet alphabet is rejected. -/
theorem rejects_invalid_byte (bad : UInt8) (hbad : quartetDigit bad = false) :
    decodeFull quartetElem quartetConsumesByte 1 (fun _ => bad) = none := by
  cases h : decodeFull quartetElem quartetConsumesByte 1 (fun _ => bad) with
  | none => rfl
  | some v =>
      have hall := decodeFull_canonical (n := 1) (s := fun _ => bad) (v := v) h
      have h0 : quartetDigit bad = true := by simpa using (hall ⟨0, by decide⟩)
      rw [hbad] at h0
      simp at h0

/-- Rejection: wrong arity (not a multiple of 4 digits) is rejected. -/
theorem rejects_bad_arity :
    decodeFull quartetElem quartetConsumesByte 1 (fun _ => 0x30) = none := by
  cases h : decodeFull quartetElem quartetConsumesByte 1 (fun _ => 0x30) with
  | none => rfl
  | some v =>
      have hmem : (v, Suffix.empty 1) ∈ decodeRepeat quartetElem quartetConsumesByte 1 (fun _ => 0x30) :=
        decodeFull_some quartetElem quartetConsumesByte (fun _ => 0x30) v h
      rcases (decodeRepeat_spec quartetElem quartetConsumesByte v 1 (fun _ => 0x30) (Suffix.empty 1)).1 hmem with ⟨s₀, hs, hrel⟩
      have hne : (fun _ => 0x30 : Bytes 1) = cast (congrArg Bytes (Nat.sub_zero 1)) s₀ := by
        rw [hs]
        exact prepend_empty_eq s₀
      have hrels : relRepeat (Rel quartetElem) v 1 (fun _ => 0x30) := by
        rw [hne]
        exact (relRepeat_cast (Rel quartetElem) v (Nat.sub_zero 1) s₀).1 hrel
      cases v with
      | nil =>
          rw [relRepeat_nil] at hrels
          omega
      | cons x xs =>
          rw [relRepeat_cons] at hrels
          rcases hrels with ⟨m, hm, s₁, s₂, _, hx, _⟩
          have hlen : m = 4 := Rel_quartetElem_len x s₁ hx
          omega

end BaseN.Base4
