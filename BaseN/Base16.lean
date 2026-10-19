/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# BaseN.Base16

RFC 4648 §8 hex encoding, expressed as a `codec` `Codec (List UInt8)` value.

The canonical alphabet is **uppercase** `0-9A-F` (the RFC's recommended form).
For the `Codec` value the digit relation is a **strict bijection** over the 16
uppercase digits (`hexToNibble` accepts exactly `0-9A-F`), so the `iso` law and
`Unambiguous` hold cleanly; a lowercase-accepting *decoder* is a decode-only
convenience that cannot be a strict `Iso` (it is intentionally not part of this
`Codec` value).  Two hex digits span `0..255` exactly, so decoding needs no
overflow check.

The element is `hexElem : Codec UInt8 := iso hexBlockIso (count 2 (satisfy hexDigit))`;
the unbounded run is the productive repetition triple `relHex`/`decodeHex`/
`encodeHex`, whose roundtrip is the inherited `decodeRepeat_spec`/
`encodeRepeat_rel` law — no bespoke `encode`/`decode`.
-/

import BaseN.Common

namespace BaseN.Base16

open Codec
open BaseN.Common

/-! ## Digit-level arithmetic (`Nat`) -/

/-- The uppercase-hex digit character (an ASCII byte value) for nibble `n`. -/
def nibbleToHex (n : Nat) : Nat :=
  if n ≤ 9 then 48 + n else 55 + n

/-- `hexToNibble e` — the nibble value of an uppercase hex digit, or `16` if invalid. -/
def hexToNibble (e : Nat) : Nat :=
  if e ≤ 57 then if 48 ≤ e then e - 48 else 16
  else if e ≤ 70 then if 65 ≤ e then e - 55 else 16
  else 16

/-- `hexNibbleValid e` — `true` iff `e` is an uppercase hex digit. -/
def hexNibbleValid (e : Nat) : Bool := decide (hexToNibble e ≤ 15)

/-- `toByte n` — the `UInt8` embedding. -/
def toByte (n : Nat) : UInt8 := UInt8.ofNat n

theorem hexToNibble_nibbleToHex (n : Nat) (hn : n ≤ 15) :
    hexToNibble (nibbleToHex n) = n := by
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

theorem nibbleToHex_valid (n : Nat) (hn : n ≤ 15) : hexNibbleValid (nibbleToHex n) = true := by
  unfold hexNibbleValid
  apply decide_eq_true
  rw [hexToNibble_nibbleToHex n hn]
  exact hn

theorem nibbleToHex_lt_256 (n : Nat) (hn : n ≤ 15) : nibbleToHex n < 256 := by
  unfold nibbleToHex
  by_cases h9 : n ≤ 9 <;> simp [h9] <;> omega

/-- `hexNibbleValid e = true` implies `hexToNibble e ≤ 15`. -/
theorem hexNibbleValid_of_decide (e : Nat) (h : hexNibbleValid e = true) : hexToNibble e ≤ 15 :=
  of_decide_eq_true (by simpa [hexNibbleValid] using h)

/-- When `e` is a valid uppercase hex digit, `nibbleToHex (hexToNibble e) = e`. -/
theorem nibbleToHex_hexToNibble_of_valid (e : Nat) (h : hexNibbleValid e = true) :
    nibbleToHex (hexToNibble e) = e := by
  have hv : hexToNibble e ≤ 15 := hexNibbleValid_of_decide e h
  unfold hexToNibble nibbleToHex
  by_cases hle : e ≤ 57
  · by_cases hge : 48 ≤ e
    · have hv' : e - 48 = hexToNibble e := by simp [hexToNibble, hle, hge]
      have hb : e - 48 ≤ 15 := by omega
      have hb9 : e - 48 ≤ 9 := by omega
      simp [hle, hge, hb9]
    · have : hexToNibble e = 16 := by simp [hexToNibble, hle, hge]
      omega
  · by_cases hle70 : e ≤ 70
    · by_cases hge65 : 65 ≤ e
      · have hv' : e - 55 = hexToNibble e := by simp [hexToNibble, hle, hle70, hge65]
        have hb : e - 55 ≤ 15 := by omega
        have hb9 : ¬ e - 55 ≤ 9 := by omega
        simp [hle, hle70, hge65, hb9]
        omega
      · have : hexToNibble e = 16 := by simp [hexToNibble, hle, hle70, hge65]
        omega
    · have : hexToNibble e = 16 := by simp [hexToNibble, hle, hle70]
      omega

/-! ## The block isomorphism -/

/-- The hex digit predicate over `UInt8`: holds iff `b` is an uppercase hex digit. -/
def hexDigit (b : UInt8) : Bool := hexNibbleValid b.toNat

/-- `(toByte (nibbleToHex n)).toNat = nibbleToHex n`. -/
private theorem toByte_nibbleToHex (n : Nat) (hn : n ≤ 15) :
    (toByte (nibbleToHex n)).toNat = nibbleToHex n := by
  unfold toByte
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (nibbleToHex_lt_256 n hn)]

/-- `hexToNibble ((toByte (nibbleToHex n)).toNat) = n` for `n ≤ 15`. -/
theorem hexToNibble_toByte_nibbleToHex (n : Nat) (hn : n ≤ 15) :
    hexToNibble (toByte (nibbleToHex n)).toNat = n := by
  rw [toByte_nibbleToHex n hn]
  exact hexToNibble_nibbleToHex n hn

/-- `apply`: read two hex digits and fold them into their byte. -/
def hexBlockApply (cs : List UInt8) : Option UInt8 :=
  match cs with
  | [hi, lo] =>
      if hexNibbleValid hi.toNat && hexNibbleValid lo.toNat then
        let n := hexToNibble hi.toNat * 16 + hexToNibble lo.toNat
        some (UInt8.ofNat n)
      else none
  | _ => none

/-- `unapply`: write a byte as its two uppercase hex digits (always valid). -/
def hexBlockUnapply (b : UInt8) : Option (List UInt8) :=
  some [toByte (nibbleToHex (b.toNat / 16)), toByte (nibbleToHex (b.toNat % 16))]

/-- Each digit byte of `hexBlockUnapply b` is valid. -/
theorem hexDigit_valid_of_byte (b : UInt8) :
    hexNibbleValid (toByte (nibbleToHex (b.toNat / 16))).toNat = true ∧
    hexNibbleValid (toByte (nibbleToHex (b.toNat % 16))).toNat = true := by
  have hbv : b.toNat < 256 := UInt8.toNat_lt b
  have hhi : b.toNat / 16 ≤ 15 := by omega
  have hlo : b.toNat % 16 ≤ 15 := by omega
  constructor
  · rw [toByte_nibbleToHex (b.toNat / 16) hhi]; exact nibbleToHex_valid (b.toNat / 16) hhi
  · rw [toByte_nibbleToHex (b.toNat % 16) hlo]; exact nibbleToHex_valid (b.toNat % 16) hlo

/-- `apply` is a left inverse of `unapply`. -/
theorem hexBlockApply_unapply (b : UInt8) :
    hexBlockApply [toByte (nibbleToHex (b.toNat / 16)), toByte (nibbleToHex (b.toNat % 16))] = some b := by
  have hbv : b.toNat < 256 := UInt8.toNat_lt b
  have hhi : b.toNat / 16 ≤ 15 := by omega
  have hlo : b.toNat % 16 ≤ 15 := by omega
  rw [hexBlockApply]
  rw [hexToNibble_toByte_nibbleToHex (b.toNat / 16) hhi, hexToNibble_toByte_nibbleToHex (b.toNat % 16) hlo]
  have hvd := hexDigit_valid_of_byte b
  rw [hvd.1, hvd.2]
  have hh : (true && true) = true := by decide
  rw [hh]
  have hsum : b.toNat / 16 * 16 + b.toNat % 16 = b.toNat := by
    have h := Nat.div_add_mod b.toNat 16
    rw [Nat.mul_comm] at h
    exact h
  rw [hsum]
  simp

/-- Uniqueness of the hex decomposition: `hi*16 + lo = ehi*16 + elo` (each ≤ 15). -/
theorem hex_decompose_unique (a0 a1 b0 b1 : Nat)
    (_ha0 : a0 ≤ 15) (_ha1 : a1 ≤ 15) (_hb0 : b0 ≤ 15) (_hb1 : b1 ≤ 15)
    (h : a0 * 16 + a1 = b0 * 16 + b1) :
    a0 = b0 ∧ a1 = b1 := by
  have ha0' : a0 = b0 := by
    have hm := congrArg (fun x => x / 16) h
    omega
  have ha1' : a1 = b1 := by
    have hm := congrArg (fun x => x % 16) h
    omega
  exact ⟨ha0', ha1'⟩

/-- The inverse law of the hex block: `apply` and `unapply` are mutual inverses. -/
theorem hexBlockIso_law (cs : List UInt8) (b : UInt8) :
    hexBlockApply cs = some b ↔ hexBlockUnapply b = some cs := by
  constructor
  · intro h
    cases cs with
    | nil => simp [hexBlockApply] at h
    | cons hi rest =>
        cases rest with
        | nil => simp [hexBlockApply] at h
        | cons lo rest2 =>
            cases rest2 with
            | nil =>
                rw [hexBlockApply] at h
                by_cases hv : hexNibbleValid hi.toNat && hexNibbleValid lo.toNat
                · simp only [hv, ite_true] at h
                  have hb_eq : UInt8.ofNat (hexToNibble hi.toNat * 16 + hexToNibble lo.toNat) = b := by
                    exact Option.some.inj h
                  have hv' : hexNibbleValid hi.toNat = true ∧ hexNibbleValid lo.toNat = true := by
                    simpa only [Bool.and_eq_true_iff] using hv
                  have hvd0 : hexNibbleValid hi.toNat = true := hv'.1
                  have hvd1 : hexNibbleValid lo.toNat = true := hv'.2
                  have v0le := hexNibbleValid_of_decide hi.toNat hvd0
                  have v1le := hexNibbleValid_of_decide lo.toNat hvd1
                  have hb : b.toNat = hexToNibble hi.toNat * 16 + hexToNibble lo.toNat := by
                    have hbt := congrArg UInt8.toNat hb_eq
                    rw [UInt8.toNat_ofNat'] at hbt
                    have hbnd : hexToNibble hi.toNat * 16 + hexToNibble lo.toNat < 256 := by omega
                    rw [Nat.mod_eq_of_lt hbnd] at hbt
                    exact hbt.symm
                  have hsum : b.toNat = b.toNat / 16 * 16 + b.toNat % 16 := by
                    have h := Nat.div_add_mod b.toNat 16
                    rw [Nat.mul_comm] at h
                    exact h.symm
                  have hdev : hexToNibble hi.toNat = b.toNat / 16 ∧ hexToNibble lo.toNat = b.toNat % 16 := by
                    exact hex_decompose_unique (hexToNibble hi.toNat) (hexToNibble lo.toNat) (b.toNat / 16) (b.toNat % 16)
                      v0le v1le (by omega) (by omega) (hb.symm.trans hsum)
                  rw [hexBlockUnapply]
                  have hd0 : hi.toNat = nibbleToHex (hexToNibble hi.toNat) :=
                    (nibbleToHex_hexToNibble_of_valid hi.toNat hvd0).symm
                  have hd1 : lo.toNat = nibbleToHex (hexToNibble lo.toNat) :=
                    (nibbleToHex_hexToNibble_of_valid lo.toNat hvd1).symm
                  rw [← hdev.1, ← hdev.2]
                  rw [← hd0, ← hd1]
                  simp [toByte]
                · simp [hv] at h
            | cons _ _ => simp [hexBlockApply] at h
  · intro h
    rw [hexBlockUnapply] at h
    cases h
    exact hexBlockApply_unapply b

/-- The two-hex block ↔ one byte partial isomorphism. -/
def hexBlockIso : Iso (List UInt8) UInt8 :=
  { apply := hexBlockApply, unapply := hexBlockUnapply, law := hexBlockIso_law }

/-- The base16 element: two uppercase hex digit bytes grouped into one byte. -/
def hexElem : Codec UInt8 := Codec.iso hexBlockIso (count 2 (Codec.satisfy hexDigit))

/-- `hexElem` is productive, hence a `ConsumesByte` witness. -/
theorem hexConsumesByte : ConsumesByte hexElem := by
  unfold hexElem
  rw [← productive_iff_consumesByte (Codec.iso hexBlockIso (count 2 (Codec.satisfy hexDigit)))]
  apply Productive_iso hexBlockIso (count 2 (Codec.satisfy hexDigit))
  rw [show 2 = 1 + 1 by rfl]
  exact Productive_count_satisfy_succ hexDigit 1

/-- The base16 decoder. -/
def decodeHex {n : Nat} (s : Bytes n) : List (List UInt8 × Suffix n) :=
  decodeRepeat hexElem hexConsumesByte n s

/-- The base16 encoder. -/
def encodeHex (bs : List UInt8) : Option (Sigma fun n => Bytes n) :=
  encodeRepeat hexElem bs

/-- The base16 relation. -/
def relHex : List UInt8 → (n : Nat) → Bytes n → Prop :=
  relRepeat (Rel hexElem)

/-! ## Unambiguity and the inherited roundtrip law -/

/-- `hexElem` is unambiguous. -/
theorem hexElem_unambiguous : Unambiguous hexElem := by
  unfold hexElem
  apply Unambiguous_iso hexBlockIso (count 2 (Codec.satisfy hexDigit))
  exact count_satisfy_unambiguous hexDigit 2

/-- `Rel hexElem x s` pins the byte length: `n = 2`. -/
theorem Rel_hexElem_len (x : UInt8) {n : Nat} (s : Bytes n) :
    Rel hexElem x s → n = 2 := by
  intro h
  unfold hexElem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, _, hc⟩
  exact Rel_count_satisfy_len hexDigit 2 a s hc

/-- The base16 relation is unambiguous. -/
theorem relHex_unambiguous : relUnambiguous relHex := by
  intro a b n s ha hb
  dsimp [relHex] at ha hb
  induction a generalizing b n s with
  | nil =>
      rw [relRepeat_nil] at ha
      subst n
      cases b with
      | nil => rfl
      | cons y ys =>
          rw [relRepeat_cons] at hb
          rcases hb with ⟨m, hm, s₁, s₂, hs, hy, _⟩
          have hlen : m = 2 := Rel_hexElem_len y s₁ hy
          have hm0 : m = 0 := by omega
          omega
  | cons x xs ih =>
      cases b with
      | nil =>
          rw [relRepeat_nil] at hb
          rw [relRepeat_cons] at ha
          rcases ha with ⟨mx, hmx, s₁x, s₂x, hsx, hx, hxs⟩
          have hlen : mx = 2 := Rel_hexElem_len x s₁x hx
          subst n
          have hm0 : mx = 0 := by omega
          omega
      | cons y ys =>
          rw [relRepeat_cons] at ha hb
          rcases ha with ⟨mx, hmx, s₁x, s₂x, hsx, hx, hxs⟩
          rcases hb with ⟨my, hmy, s₁y, s₂y, hsy, hy, hys⟩
          have hlx : mx = 2 := Rel_hexElem_len x s₁x hx
          have hly : my = 2 := Rel_hexElem_len y s₁y hy
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
            exact hexElem_unambiguous s₁x hx (by rw [hpre]; exact hy)
          have htail : xs = ys := by
            exact ih s₂x hxs (by simpa [htaily] using hys)
          rw [hhead, htail]

/-- Full-consumption decode is unambiguous for `hexElem`. -/
theorem hexDecodeFull_unambiguous {x y : List UInt8} {n : Nat} (s : Bytes n) :
    (x, Suffix.empty n) ∈ decodeRepeat hexElem hexConsumesByte n s →
    (y, Suffix.empty n) ∈ decodeRepeat hexElem hexConsumesByte n s → x = y := by
  intro hx hy
  rcases (decodeRepeat_spec hexElem hexConsumesByte x n s (Suffix.empty n)).1 hx with ⟨s₀x, hsx, hrx⟩
  rcases (decodeRepeat_spec hexElem hexConsumesByte y n s (Suffix.empty n)).1 hy with ⟨s₀y, hsy, hry⟩
  have hs₀ : s₀x = s₀y := by
    have hpre : (Suffix.empty n).prepend s₀x = (Suffix.empty n).prepend s₀y := by
      exact hsx.symm.trans hsy
    exact prepend_prefix_eq (Suffix.empty n) s₀x s₀y hpre
  exact relHex_unambiguous s₀x hrx (by rw [hs₀]; exact hry)

/-- The base16 roundtrip law. `[propext, Quot.sound]`-only. -/
theorem roundtrip (bs : List UInt8) {n : Nat} {s : Bytes n} :
    encodeHex bs = some ⟨n, s⟩ → decodeFull hexElem hexConsumesByte n s = some bs := by
  intro he
  have hrel : relRepeat (Rel hexElem) bs n s := encodeRepeat_rel hexElem bs he
  have hmem : (bs, Suffix.empty n) ∈ decodeRepeat hexElem hexConsumesByte n s := by
    refine (decodeRepeat_spec hexElem hexConsumesByte bs n s (Suffix.empty n)).2 ⟨
      cast (congrArg Bytes (Nat.sub_zero n).symm) s, ?_, ?_⟩
    · exact (prepend_empty_eq s).symm
    · exact (relRepeat_cast (Rel hexElem) bs (Nat.sub_zero n).symm s).2 hrel
  exact (decodeFull_spec hexElem hexConsumesByte (fun {x y} {m} (t : Bytes m) =>
    hexDecodeFull_unambiguous (s := t)) s bs).2 hmem

end BaseN.Base16
