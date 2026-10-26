/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# BaseN.Base16

RFC 4648 §8 hex encoding, expressed as a `codec` `Codec (List UInt8)` value.

The canonical alphabet is **uppercase** `0-9A-F` (the RFC's recommended form).
For the `Codec` value the digit relation is a **strict bijection** over the 16
uppercase digits (`hexToNibble` accepts exactly `0-9A-F`), so the `iso` law and `Unambiguous` hold
cleanly.

RFC 4648 §8 requires a decoder to accept **both** cases. That is provided — not by
weakening the `Codec` value, but by `codec`'s information-free-variation layer
(`Codec.Normal`): see `foldByte`/`foldList`, the normal-form `Iso` `hexBlockIsoF`,
and the case-insensitive decoders `decodeHexBlockFold`/`decodeHexFold` below. The
variation is a quotient of the concrete syntax, folded **up** so the canonical
uppercase encoding is a fixed point. Encoding stays canonical (uppercase only).

Two hex digits span `0..255` exactly, so decoding needs no overflow check.

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

/-- On a decimal-digit byte, `hexToNibble` is `e - 48`. -/
theorem hexToNibble_digit (e : Nat) (h1 : 48 ≤ e) (h2 : e ≤ 57) :
    hexToNibble e = e - 48 := by
  unfold hexToNibble
  rw [if_pos h2, if_pos h1]

/-- On an uppercase letter byte, `hexToNibble` is `e - 55`. -/
theorem hexToNibble_upper (e : Nat) (h1 : 65 ≤ e) (h2 : e ≤ 70) :
    hexToNibble e = e - 55 := by
  unfold hexToNibble
  rw [if_neg (by omega : ¬ e ≤ 57), if_pos (by omega : e ≤ 70), if_pos h1]

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

/-- The base16 run value: the element + productivity witness. -/
def hexRun : Run UInt8 := { elem := hexElem, step := hexConsumesByte }

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

/-! ## Conformance: canonical encoding, converse, injectivity -/

/-- `hexElem` is functional: one byte relates to a unique 2-byte string. -/
theorem hexElem_functional : Functional hexElem := by
  unfold hexElem
  exact Functional_iso hexBlockIso (count 2 (Codec.satisfy hexDigit))
    (Functional_count_satisfy hexDigit 2)

/-- Every byte of a `hexElem`-related string is an uppercase hex digit. -/
theorem Rel_hexElem_canonical {x : UInt8} {m : Nat} {t : Bytes m} :
    Rel hexElem x t → ∀ i : Fin m, hexDigit (t i) = true := by
  intro ht
  change Rel (Codec.iso hexBlockIso (count 2 (Codec.satisfy hexDigit))) x t at ht
  rw [Rel_iso] at ht
  rcases ht with ⟨a, _, hc⟩
  exact Rel_count_satisfy_forall hexDigit 2 a t hc

/-- Canonical encoding (alphabet-only): every byte `encodeHex` produces is an
uppercase hex digit. `[propext, Quot.sound]`-only. -/
theorem encodeHex_canonical (bs : List UInt8) {n : Nat} {s : Bytes n} :
    encodeHex bs = some ⟨n, s⟩ → ∀ i : Fin n, hexDigit (s i) = true := by
  intro he
  have hrel : relRepeat (Rel hexElem) bs n s := encodeRepeat_rel hexElem bs he
  exact relRepeat_forall hexDigit (fun x {m} t ht => Rel_hexElem_canonical (t := t) ht) bs n s hrel

/-- Converse: a fully-decoded value re-encodes to exactly the input bytes. -/
theorem decode_encode_inverse {n : Nat} {s : Bytes n} (v : List UInt8) :
    decodeFull hexElem hexConsumesByte n s = some v → encodeHex v = some ⟨n, s⟩ := by
  intro hd
  have hmem : (v, Suffix.empty n) ∈ decodeRepeat hexElem hexConsumesByte n s :=
    decodeFull_some hexElem hexConsumesByte s v hd
  rcases (decodeRepeat_spec hexElem hexConsumesByte v n s (Suffix.empty n)).1 hmem with ⟨s₀, hs, hrel⟩
  have hne : s = cast (congrArg Bytes (Nat.sub_zero n)) s₀ := by
    rw [hs]
    exact prepend_empty_eq s₀
  have hrels : relRepeat (Rel hexElem) v n s := by
    rw [hne]
    exact (relRepeat_cast (Rel hexElem) v (Nat.sub_zero n) s₀).1 hrel
  exact encodeRepeat_of_rel hexElem hexElem_functional v s hrels

/-- `hexBlockUnapply` is *total*, and its digits are exactly the 2 digits of the
byte: length 2, every one a `hexDigit`. This is what makes `hexElem`'s
encoder total — its only failure mode would be a produced digit failing
`satisfy`. -/
theorem hexBlockUnapply_digits (b : UInt8) :
    ∃ ds, hexBlockUnapply b = some ds ∧ ds.length = 2 ∧ ∀ d ∈ ds, hexDigit d = true := by
  refine ⟨[toByte (nibbleToHex (b.toNat / 16)), toByte (nibbleToHex (b.toNat % 16))], rfl, rfl, ?_⟩
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  unfold hexDigit
  rcases hd with h | h <;> subst h
  · exact (hexDigit_valid_of_byte b).1
  · exact (hexDigit_valid_of_byte b).2

/-- Every byte encodes through `hexElem`: the element encoder is total. -/
theorem hexElem_encode_ne_none (b : UInt8) : Codec.encode hexElem b ≠ none := by
  obtain ⟨ds, hds, hlen, hpd⟩ := hexBlockUnapply_digits b
  unfold hexElem
  simp only [Codec.encode, hexBlockIso, hds, Option.bind]
  rw [← hlen]
  exact count_satisfy_encode_ne_none hexDigit ds hpd

/-- **Hex encoding is total** — `encodeHex` never returns `none`.

This is the fact that upgrades the injectivity law to the spec's plain
`Option`-equality form (task 6.2): with totality in hand the `none`/`none` and
`some`/`none` cases of `encodeHex v = encodeHex v'` are refuted, leaving only
the both-succeed case, which is `encode_injective`.

`encodeRepeat` fails only when the element encoder does, so this is an induction
on the value list with `hexElem_encode_ne_none` at each step.
`[propext, Quot.sound]`-only. -/
theorem encodeHex_ne_none (bs : List UInt8) : encodeHex bs ≠ none := by
  unfold encodeHex
  induction bs with
  | nil => simp [Codec.encodeRepeat]
  | cons b rest ih =>
      rw [Codec.encodeRepeat]
      have hb : Codec.encode hexElem b ≠ none := hexElem_encode_ne_none b
      cases h₁ : Codec.encode hexElem b with
      | none => exact absurd h₁ hb
      | some e₁ =>
          cases h₂ : Codec.encodeRepeat hexElem rest with
          | none => exact absurd h₂ ih
          | some e₂ => simp

/-- encoding is injective: a byte list has a unique hex encoding (the
both-succeed form, which the spec's `Option`-equality law reduces to). -/
theorem encode_injective {v v' : List UInt8} {n : Nat} {s : Bytes n} :
    encodeHex v = some ⟨n, s⟩ → encodeHex v' = some ⟨n, s⟩ → v = v' := by
  intro hv hv'
  have hrelv : relRepeat (Rel hexElem) v n s := encodeRepeat_rel hexElem v hv
  have hrelv' : relRepeat (Rel hexElem) v' n s := encodeRepeat_rel hexElem v' hv'
  exact relHex_unambiguous s hrelv hrelv'

/-- **Hex encoding is injective, in the spec's `Option`-equality form:**
`encodeHex v = encodeHex v' → v = v'` — exactly the `basen` spec's Scenario
"Encoding is injective" (`encode{X} v = encode{X} v' → v = v'`).

Because `encodeHex` is total (`encodeHex_ne_none`), the left side cannot be
`none`; destructure the common result and hand both successes to
`encode_injective`. `[propext, Quot.sound]`-only. -/
theorem encodeHex_injective_eq {v v' : List UInt8} (h : encodeHex v = encodeHex v') :
    v = v' := by
  cases hv : encodeHex v with
  | none => exact absurd hv (encodeHex_ne_none v)
  | some e =>
      rcases e with ⟨n, s⟩
      have hv' : encodeHex v' = some ⟨n, s⟩ := by rw [← h]; exact hv
      exact encode_injective hv hv'

/-- A fully-decoded value means every input byte is a hex digit: the decoder
never accepts a byte outside the uppercase canonical alphabet. `[propext,
Quot.sound]`-only. -/
theorem decodeFull_canonical {n : Nat} {s : Bytes n} {v : List UInt8} :
    decodeFull hexElem hexConsumesByte n s = some v → ∀ i : Fin n, hexDigit (s i) = true := by
  intro hd
  have hmem : (v, Suffix.empty n) ∈ decodeRepeat hexElem hexConsumesByte n s :=
    decodeFull_some hexElem hexConsumesByte s v hd
  rcases (decodeRepeat_spec hexElem hexConsumesByte v n s (Suffix.empty n)).1 hmem with ⟨s₀, hs, hrel⟩
  have hne : s = cast (congrArg Bytes (Nat.sub_zero n)) s₀ := by
    rw [hs]
    exact prepend_empty_eq s₀
  have hrels : relRepeat (Rel hexElem) v n s := by
    rw [hne]
    exact (relRepeat_cast (Rel hexElem) v (Nat.sub_zero n) s₀).1 hrel
  exact relRepeat_forall hexDigit (fun x {m} t ht => Rel_hexElem_canonical (t := t) ht) v n s hrels

/-- **Base16: decode succeeds iff `s` is in `encodeHex`'s image, at that value.**
`decodeFull hexElem hexConsumesByte n s = some v ↔ ∃ v', encodeHex v' = some ⟨n, s⟩ ∧ v = v'`.

The hex analogue of `decodeFullB64_char`/`decodeFullB32_char` (task 7.1): the
decoder accepts a byte string exactly when it is a canonical encoding, and then
returns the unique value that encodes to it. Pure assembly over the already-proved
`decode_encode_inverse` (`→`) and `roundtrip` (`←`). `[propext, Quot.sound]`-only. -/
theorem decodeFull_B16_char {n : Nat} (s : Bytes n) (v : List UInt8) :
    decodeFull hexElem hexConsumesByte n s = some v ↔ ∃ v', encodeHex v' = some ⟨n, s⟩ ∧ v = v' := by
  constructor
  · intro h
    exact ⟨v, decode_encode_inverse v h, rfl⟩
  · rintro ⟨w, he, hv⟩
    rw [hv]
    exact roundtrip w he

/-- Rejection: a byte outside the uppercase hex alphabet (e.g. `!`) is rejected. -/
theorem rejects_invalid_byte (bad : UInt8) (hbad : hexDigit bad = false) :
    decodeFull hexElem hexConsumesByte 1 (fun _ => bad) = none := by
  cases h : decodeFull hexElem hexConsumesByte 1 (fun _ => bad) with
  | none => rfl
  | some v =>
      have hall := decodeFull_canonical (n := 1) (s := fun _ => bad) (v := v) h
      have h0 : hexDigit bad = true := by simpa using (hall ⟨0, by decide⟩)
      rw [hbad] at h0
      simp at h0

/-- The **strict canonical** decoder rejects a lowercase byte — as it must, since
`hexElem` is the uppercase-only bijection. This is *not* an RFC 4648 §8 divergence:
§8's MUST is satisfied by the case-insensitive decoder `decodeHexFold`, which is
`foldList` composed **outside** the strict `Iso` (`Codec.Normal.decodeNormal`).

The earlier rationale for this theorem — "a case-insensitive alphabet would break
`Unambiguous`" — was **false** and is withdrawn: `Unambiguous` says one input yields
at most one value, and folding case is a total function. The real constraint is the
**canonicality of encode**, which holds: `encodeHex` emits uppercase only.

`1`-byte spelling caveat: `0x66` here is a single byte (`'f'`), not the two-byte
string `"6f"`; the strict decoder rejects it because a single hex digit is
odd-arity. See `decodeHexFold_lowercase_eq` for the two-byte both-cases law. -/
theorem rejects_lowercase :
    decodeFull hexElem hexConsumesByte 1 (fun _ => 0x66) = none := by
  exact rejects_invalid_byte (0x66 : UInt8) (by decide)

/-- Rejection: wrong arity (an odd number of hex digits does not form a byte). -/
theorem rejects_odd_arity :
    decodeFull hexElem hexConsumesByte 1 (fun _ => 0x36) = none := by
  cases h : decodeFull hexElem hexConsumesByte 1 (fun _ => 0x36) with
  | none => rfl
  | some v =>
      have hmem : (v, Suffix.empty 1) ∈ decodeRepeat hexElem hexConsumesByte 1 (fun _ => 0x36) :=
        decodeFull_some hexElem hexConsumesByte (fun _ => 0x36) v h
      rcases (decodeRepeat_spec hexElem hexConsumesByte v 1 (fun _ => 0x36) (Suffix.empty 1)).1 hmem with ⟨s₀, hs, hrel⟩
      have hne : (fun _ => 0x36 : Bytes 1) = cast (congrArg Bytes (Nat.sub_zero 1)) s₀ := by
        rw [hs]
        exact prepend_empty_eq s₀
      have hrels : relRepeat (Rel hexElem) v 1 (fun _ => 0x36) := by
        rw [hne]
        exact (relRepeat_cast (Rel hexElem) v (Nat.sub_zero 1) s₀).1 hrel
      cases v with
      | nil =>
          rw [relRepeat_nil] at hrels
          omega
      | cons x xs =>
          rw [relRepeat_cons] at hrels
          rcases hrels with ⟨m, hm, s₁, s₂, _, hx, _⟩
          have hlen : m = 2 := Rel_hexElem_len x s₁ hx
          omega

/-! ## RFC 4648 §8 — case-insensitive decoding as a normal form

RFC 4648 §8 requires a Base16 **decoder** to accept both cases (`6F` and `6f`),
because the case of a hex digit carries no information. The `Codec` value above
cannot: `hexBlockApply` is a strict uppercase bijection, so lowercase is rejected.

The fix is `codec`'s information-free-variation layer (`Codec.Normal`): the
variation is a **quotient of the concrete syntax**, reified as the type of
`norm`'s fixed points, so the bijection stays an ordinary `Iso` and `Iso.law` is
not weakened. Concretely:

* `foldByte` folds `a`–`f` **up** to `A`–`F` and is the identity elsewhere;
* `foldByte_idem` makes `Normalizer (List UInt8) foldList` a value;
* `hexBlockIsoF : Iso UInt8 (Normal (List UInt8) foldList)` is the canonical
  bijection, whose `unapply` folds *before* applying `hexBlockApply` (a class with
  a lowercase representative must still apply);
* `decodeHexFold` is `decodeNormal`, i.e. `foldList` composed **outside** the
  `Iso` — not an `Iso`, no inverse, deliberately accepting input the strict `Iso`
  rejects.

**The direction matters.** The canonical alphabet is uppercase, so the encoder's
output must be a *fixed point* of `foldList`; that is exactly `decodeNormal_encode`'s
`hfix` obligation, discharged by `encodeHex_fold_fixed` below. Folding *down*
instead would make the encoder's own output a non-fixed point and the normalising
decoder would fail on it.
-/

/-- The fold's fixed points: a digit or an **uppercase** `A`–`F`. These are exactly
the bytes `foldByte` leaves alone, so they are the normal forms of the quotient. -/
def hexFixed (b : UInt8) : Bool :=
  decide ((48 ≤ b.toNat ∧ b.toNat ≤ 57) ∨ (65 ≤ b.toNat ∧ b.toNat ≤ 70))

/-- **The ASCII case fold**, `a`–`f` → `A`–`F`, identity elsewhere.

Folding **up** is what makes the canonical (uppercase) encoding a fixed point —
see the section docstring. -/
def foldByte (b : UInt8) : UInt8 :=
  if hexFixed b then b
  else if 97 ≤ b.toNat ∧ b.toNat ≤ 102 then UInt8.ofNat (b.toNat - 32)
  else b

/-- `foldByte` leaves its own output alone. -/
theorem foldByte_fixed (b : UInt8) (h : hexFixed b = true) : foldByte b = b := by
  simp only [foldByte, h, ite_true]

/-- The lowercase branch, as an equation. -/
theorem foldByte_folded (b : UInt8) (hf : hexFixed b = false)
    (hl : 97 ≤ b.toNat ∧ b.toNat ≤ 102) :
    foldByte b = UInt8.ofNat (b.toNat - 32) := by
  simp only [foldByte, hf, Bool.false_eq_true, ite_false, hl]
  rw [if_pos (by decide)]

/-- `(UInt8.ofNat (n - 32)).toNat = n - 32` for a lowercase letter's value. -/
theorem ofNat_sub32_toNat (b : UInt8) (h1 : 97 ≤ b.toNat) (h2 : b.toNat ≤ 102) :
    (UInt8.ofNat (b.toNat - 32)).toNat = b.toNat - 32 := by
  have hbv : b.toNat < 256 := UInt8.toNat_lt b
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

/-- **`foldByte` is idempotent** — the one law `Normalizer` is owed. -/
theorem foldByte_idem (b : UInt8) : foldByte (foldByte b) = foldByte b := by
  by_cases hf : hexFixed b = true
  · rw [foldByte_fixed b hf, foldByte_fixed b hf]
  · by_cases hl : 97 ≤ b.toNat ∧ b.toNat ≤ 102
    · rw [foldByte_folded b (by simpa using hf) hl]
      apply foldByte_fixed
      have h1 := ofNat_sub32_toNat b hl.1 hl.2
      unfold hexFixed
      rw [h1]
      exact decide_eq_true (Or.inr ⟨by omega, by omega⟩)
    · have hf' : hexFixed b = false := by simpa using hf
      simp only [foldByte, hf', Bool.false_eq_true, ite_false, hl, ite_false]

/-- The fold, lifted to a byte list. -/
def foldList (cs : List UInt8) : List UInt8 := cs.map foldByte

@[simp]
theorem foldList_nil : foldList [] = [] := rfl

@[simp]
theorem foldList_cons (c : UInt8) (cs : List UInt8) :
    foldList (c :: cs) = foldByte c :: foldList cs := rfl

/-- **`foldList` is idempotent.** -/
theorem foldList_idem (cs : List UInt8) : foldList (foldList cs) = foldList cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [foldList_cons, foldByte_idem c, ih]

/-- The normalizer value the layer is instantiated at. -/
theorem foldNormalizer : Normalizer (List UInt8) foldList :=
  { idem := foldList_idem }

/-! ### The three-way digit lemma

`hexToNibble (foldByte b).toNat = hexToNibble b.toNat` is **false as one
equation**: off the alphabet the fold returns a non-digit unchanged while the
original is also non-digit — but for lowercase the original's nibble is `16`
("invalid") while the folded one is the real nibble. So the honest statement is
three-way; `hexToNibble_foldByte` gives the value form the block law needs. -/

/-- On a lowercase byte, `hexToNibble` is `16` (invalid). -/
theorem hexToNibble_lower (e : Nat) (h1 : 97 ≤ e) (h2 : e ≤ 102) :
    hexToNibble e = 16 := by
  unfold hexToNibble
  rw [if_neg (by omega : ¬ e ≤ 57), if_neg (by omega : ¬ e ≤ 70)]

/-- A lowercase byte is **not** a valid (uppercase) hex digit. -/
theorem hexNibbleValid_false_of_lower (b : UInt8) (hl : 97 ≤ b.toNat ∧ b.toNat ≤ 102) :
    hexNibbleValid b.toNat = false := by
  by_cases hv : hexNibbleValid b.toNat = true
  · exfalso
    unfold hexNibbleValid at hv
    rw [decide_eq_true_iff, hexToNibble_lower b.toNat hl.1 hl.2] at hv
    omega
  · simpa using hv

/-- **`foldByte`'s validity is the hex-char domain**: a byte becomes a valid
uppercase digit after folding exactly when it was a digit or an `a`–`f`
lowercase letter. -/
theorem hexNibbleValid_foldByte (b : UInt8) :
    hexNibbleValid (foldByte b).toNat =
      (hexNibbleValid b.toNat || decide (97 ≤ b.toNat && b.toNat ≤ 102)) := by
  by_cases hf : hexFixed b = true
  · rw [foldByte_fixed b hf]
    unfold hexFixed at hf
    rw [decide_eq_true_iff] at hf
    rcases hf with ⟨a, c⟩ | ⟨a, c⟩
    · have h1 : hexNibbleValid b.toNat = true := by
        unfold hexNibbleValid
        rw [hexToNibble_digit _ a c]
        exact decide_eq_true (by omega)
      have h2 : decide (97 ≤ b.toNat && b.toNat ≤ 102) = false := by
        rw [decide_eq_false_iff_not]
        simp only [Bool.and_eq_true, decide_eq_true_iff]
        omega
      rw [h1, h2]
      rfl
    · have h1 : hexNibbleValid b.toNat = true := by
        unfold hexNibbleValid
        rw [hexToNibble_upper _ a c]
        exact decide_eq_true (by omega)
      have h2 : decide (97 ≤ b.toNat && b.toNat ≤ 102) = false := by
        rw [decide_eq_false_iff_not]
        simp only [Bool.and_eq_true, decide_eq_true_iff]
        omega
      rw [h1, h2]
      rfl
  · have hf' : hexFixed b = false := by simpa using hf
    by_cases hl : 97 ≤ b.toNat ∧ b.toNat ≤ 102
    · rw [foldByte_folded b hf' hl, ofNat_sub32_toNat b hl.1 hl.2]
      have hv' : hexNibbleValid (b.toNat - 32) = true := by
        unfold hexNibbleValid
        rw [hexToNibble_upper _ (by omega) (by omega)]
        exact decide_eq_true (by omega)
      have h0 : hexNibbleValid b.toNat = false := hexNibbleValid_false_of_lower b hl
      have hd : decide (97 ≤ b.toNat && b.toNat ≤ 102) = true := by
        rw [decide_eq_true_iff]
        simp only [Bool.and_eq_true, decide_eq_true_iff]
        omega
      rw [hv', h0, hd]
      rfl
    · have hfb : foldByte b = b := by
        rw [foldByte, if_neg hf, if_neg hl]
      rw [hfb]
      have hd : decide (97 ≤ b.toNat && b.toNat ≤ 102) = false := by
        rw [decide_eq_false_iff_not]
        simp only [Bool.and_eq_true, decide_eq_true_iff]
        omega
      rw [hd, Bool.or_false]

/-- On a valid digit (or a lowercase letter), folding either leaves the nibble
alone or produces the letter's nibble — stated **without** a `match` in the goal,
to avoid the dependent-match `Classical.choice` leak. Case `true`: the fold is an
identity on the digit, so the nibles agree. -/
theorem hexToNibble_foldByte_true (b : UInt8) (hv : hexNibbleValid b.toNat = true) :
    hexToNibble (foldByte b).toNat = hexToNibble b.toNat := by
  have hfx : hexFixed b = true := by
    rw [hexNibbleValid, decide_eq_true_iff] at hv
    unfold hexToNibble at hv
    unfold hexFixed
    by_cases h57 : b.toNat ≤ 57
    · rw [if_pos h57] at hv
      by_cases h48 : 48 ≤ b.toNat
      · exact decide_eq_true (Or.inl ⟨h48, h57⟩)
      · rw [if_neg h48] at hv; omega
    · rw [if_neg h57] at hv
      by_cases h70 : b.toNat ≤ 70
      · rw [if_pos h70] at hv
        by_cases h65 : 65 ≤ b.toNat
        · exact decide_eq_true (Or.inr ⟨h65, h70⟩)
        · rw [if_neg h65] at hv; omega
      · rw [if_neg h70] at hv; omega
  rw [foldByte_fixed b hfx]

/-- Case `false`: a lowercase letter. The original nibble is "invalid" (`16`) and
the folded one is the uppercase nibble `b - 87`. -/
theorem hexToNibble_foldByte_false (b : UInt8) (hl : 97 ≤ b.toNat ∧ b.toNat ≤ 102) :
    hexToNibble (foldByte b).toNat = b.toNat - 87 := by
  have hfx : hexFixed b = false := by
    show decide ((48 ≤ b.toNat ∧ b.toNat ≤ 57) ∨ (65 ≤ b.toNat ∧ b.toNat ≤ 70)) = false
    exact decide_eq_false (by omega)
  rw [foldByte_folded b hfx hl, ofNat_sub32_toNat b hl.1 hl.2,
      hexToNibble_upper _ (by omega) (by omega)]
  omega

/-- **The three-way lemma**, in the two-branch form the block law consumes: on a
valid digit the nibble is unchanged (above), on a lowercase letter it becomes the
uppercase nibble (above). Stated as a `match` here for use at the call site. -/
theorem hexToNibble_foldByte_value (b : UInt8)
    (h : hexNibbleValid b.toNat = true ∨ 97 ≤ b.toNat ∧ b.toNat ≤ 102) :
    hexToNibble (foldByte b).toNat =
      if hexNibbleValid b.toNat = true then hexToNibble b.toNat else b.toNat - 87 := by
  by_cases hv : hexNibbleValid b.toNat = true
  · rw [hexToNibble_foldByte_true b hv, if_pos hv]
  · rcases h with hv' | hl
    · exact absurd hv' hv
    · rw [hexToNibble_foldByte_false b hl]
      have hv' : hexNibbleValid b.toNat = false := by simpa using hv
      rw [if_neg hv]

/-- `hexBlockApply` is `none` off a two-element block. -/
theorem hexBlockApply_none_of_not_len2 {cs : List UInt8} (h : cs.length ≠ 2) :
    hexBlockApply cs = none := by
  match cs, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _, _], _ => rfl
  | _ :: _ :: a :: b, _ => rfl

/-- **The fold preserves acceptance.** A block the strict uppercase `apply` accepts
is still accepted, with the same byte, after folding.

The *equality* form `hexBlockApply (foldList cs) = hexBlockApply cs` is **false** —
the fold is exactly what makes `['6','f']` acceptable — so the law that the
normal-form `Iso` needs is this one-directional preservation, not an identity. -/
theorem hexBlockApply_foldList {cs : List UInt8} {b : UInt8}
    (h : hexBlockApply cs = some b) : hexBlockApply (foldList cs) = some b := by
  match cs with
  | [hi, lo] =>
      have hv : (hexNibbleValid hi.toNat && hexNibbleValid lo.toNat) = true := by
        by_cases hc : (hexNibbleValid hi.toNat && hexNibbleValid lo.toNat) = true
        · exact hc
        · simp only [hexBlockApply] at h
          rw [if_neg (by simpa using hc)] at h
          exact absurd h (by simp)
      have hv' : hexNibbleValid hi.toNat = true ∧ hexNibbleValid lo.toNat = true := by
        simpa using hv
      have hfv1 : hexNibbleValid (foldByte hi).toNat = true := by
        rw [hexNibbleValid_foldByte, hv'.1]
        rfl
      have hfv2 : hexNibbleValid (foldByte lo).toNat = true := by
        rw [hexNibbleValid_foldByte, hv'.2]
        rfl
      have hb2 : (hexNibbleValid (foldByte hi).toNat && hexNibbleValid (foldByte lo).toNat) = true := by
        rw [hfv1, hfv2]
        rfl
      have e1 := hexToNibble_foldByte_value hi (Or.inl hv'.1)
      have e2 := hexToNibble_foldByte_value lo (Or.inl hv'.2)
      simp only [hexBlockApply, foldList_cons, foldList_nil, hb2, if_true,
        e1, e2, hv'.1, hv'.2] at h ⊢
      exact h
  | [] => simp only [hexBlockApply] at h; exact absurd h (by simp)
  | [_] => simp only [hexBlockApply] at h; exact absurd h (by simp)
  | _ :: _ :: _ :: _ => simp only [hexBlockApply] at h; exact absurd h (by simp)

/-- **The refutation.** The equality form of the commutation is false: a lowercase
block is rejected by the strict `apply` yet accepted after folding — precisely the
RFC 4648 §8 widening this layer exists to provide. -/
theorem hexBlockApply_foldList_ne :
    ¬ (∀ (cs : List UInt8), hexBlockApply (foldList cs) = hexBlockApply cs) := by
  intro hall
  have h := hall [0x36, 0x66]
  rw [show hexBlockApply [0x36, 0x66] = none from rfl,
      show hexBlockApply (foldList [0x36, 0x66]) = some 0x6F from rfl] at h
  exact absurd h.symm (by simp)


/-! ### The normal-form block `Iso` and its law

`hexBlockIsoF` is an **ordinary `Iso`** into the quotient `Normal (List UInt8) foldList`:
its `unapply` **folds first**, then writes the uppercase block, so a class whose
representative is lowercase still applies. `Iso.law` is untouched. -/

/-- `unapply` on normal forms: fold, then emit the canonical uppercase block. -/
def hexBlockApplyF (b : UInt8) : Option (Normal (List UInt8) foldList) :=
  match hexBlockUnapply b with
  | some cs => some (fill foldNormalizer cs)
  | none => none

/-- `apply` on normal forms: read the block (a normal form is a concrete byte list). -/
def hexBlockUnapplyF (f : Normal (List UInt8) foldList) : Option UInt8 :=
  hexBlockApply f.raw

/-- `foldList` is an idempotent map, so `fill` of it is what `unapply` produces. -/
theorem fill_foldList (cs : List UInt8) : fill foldNormalizer cs = ⟨foldList cs, foldList_idem cs⟩ :=
  rfl

/-- **The law of the normal-form block `Iso`.** Folding before applying is
compensated by `apply` reading the *raw* representative, so the two directions
remain mutual inverses.

Note which direction needs which fact: `apply ∘ unapply = id` is the strict
`hexBlockApply_unapply` composed with the observation that folding an already
uppercase block is the identity (`foldList_idem`); `unapply ∘ apply = id` on the
quotient uses `hexBlockApply_foldList` (preservation) plus `fill_surj`. -/
theorem hexBlockIsoF_law (f : Normal (List UInt8) foldList) (b : UInt8) :
    hexBlockUnapplyF f = some b ↔ hexBlockApplyF b = some f := by
  constructor
  · intro h
    obtain ⟨raw, hfix⟩ := f
    simp only [hexBlockUnapplyF] at h
    have hb : hexBlockApply raw = some b := h
    -- `raw` is a normal form, i.e. `foldList raw = raw` (its `fixed` field).
    have hraw : foldList raw = raw := hfix
    have hcs : hexBlockUnapply b = some raw := (hexBlockIso_law raw b).1 hb
    simp only [hexBlockApplyF, hcs]
    exact congrArg some (Normal.ext (by simp only [fill_raw, hraw]))
  · intro h
    simp only [hexBlockApplyF] at h
    cases hun : hexBlockUnapply b with
    | none => simp only [hun] at h; exact absurd h (by simp)
    | some cs =>
        simp only [hun] at h
        have hf : fill foldNormalizer cs = f := by simpa using h
        have hraw : f.raw = foldList cs := by
          rw [← hf]
          rfl
        simp only [hexBlockUnapplyF, hraw]
        exact hexBlockApply_foldList ((hexBlockIso_law cs b).2 hun)


/-- The normal-form block `Iso`: `UInt8` ↔ its uppercase hex digits *as a quotient
class*, so a lowercase spelling applies. An **ordinary** `Iso` — `Iso.law` intact. -/
def hexBlockIsoF : Iso UInt8 (Normal (List UInt8) foldList) :=
  { apply := hexBlockApplyF, unapply := hexBlockUnapplyF
    law := fun a b => (hexBlockIsoF_law b a).symm }

/-! ### The normalising decoder

`decodeHexFold` is `decodeNormal`: `foldList` composed **outside** `hexBlockIsoF`.
It is not an `Iso`, has no inverse, and deliberately accepts input the strict
`hexElem` rejects (RFC 4648 §8's MUST). -/

/-- The decoder over one block: fold case, then apply the canonical `Iso`. -/
def decodeHexBlockFold (cs : List UInt8) : Option UInt8 :=
  decodeNormal foldNormalizer hexBlockIsoF cs

/-- **`decodeHexBlockFold` accepts both cases.** This is RFC 4648 §8 on one
block: the canonical (uppercase) spelling and the folded spelling both decode to
the same byte, and the uppercase one is a normal form so `decodeNormal` agrees with
the strict `Iso` there (the `hfix` discharge). -/
theorem decodeHexBlockFold_both_cases (hi lo : UInt8)
    (hhiU : foldByte hi = hi) (hloU : foldByte lo = lo) :
    decodeHexBlockFold [hi, lo] = hexBlockApply [hi, lo] ∧
    decodeHexBlockFold (foldList [hi, lo]) = hexBlockApply [hi, lo] := by
  have hfix : foldList [hi, lo] = [hi, lo] := by
    simp only [foldList_cons, foldList_nil, hhiU, hloU]
  have h1 : decodeHexBlockFold [hi, lo] = hexBlockApply [hi, lo] := by
    have hdn := decodeNormal_of_fixed foldNormalizer hexBlockIsoF [hi, lo] hfix
    unfold decodeHexBlockFold
    rw [hdn]
    rfl
  exact ⟨h1, by rw [hfix]; exact h1⟩


/-- The encoder's output is a **normal form**: `hexBlockUnapply` already emits
uppercase digits, so folding is the identity on it. This is the `hfix` obligation
that `decodeNormal_encode` requires, discharged for base16. -/
theorem foldList_hexBlockUnapply (b : UInt8) {cs : List UInt8}
    (h : hexBlockUnapply b = some cs) : foldList cs = cs := by
  rw [hexBlockUnapply] at h
  simp only [Option.some.injEq] at h
  subst h
  have hb : b.toNat < 256 := UInt8.toNat_lt b
  have hhi : b.toNat / 16 ≤ 15 := by omega
  have hlo : b.toNat % 16 ≤ 15 := by omega
  have hue : ∀ n, n ≤ 15 → foldByte (toByte (nibbleToHex n)) = toByte (nibbleToHex n) := by
    intro n hn
    apply foldByte_fixed
    have hval : (toByte (nibbleToHex n)).toNat = nibbleToHex n := by
      unfold toByte
      rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (nibbleToHex_lt_256 n hn)]
    show decide ((48 ≤ (toByte (nibbleToHex n)).toNat ∧ (toByte (nibbleToHex n)).toNat ≤ 57)
      ∨ (65 ≤ (toByte (nibbleToHex n)).toNat ∧ (toByte (nibbleToHex n)).toNat ≤ 70)) = true
    rw [hval]
    unfold nibbleToHex
    by_cases h9 : n ≤ 9
    · simp only [h9, ite_true]
      exact decide_eq_true (Or.inl ⟨by omega, by omega⟩)
    · simp only [h9, ite_false]
      exact decide_eq_true (Or.inr ⟨by omega, by omega⟩)
  simp only [foldList_cons, foldList_nil, hue (b.toNat / 16) hhi, hue (b.toNat % 16) hlo]

/-- A fold fixpoint is a valid digit: `hexFixed` is a subset of the digits. -/
theorem hexNibbleValid_of_hexFixed (b : UInt8) (h : hexFixed b = true) :
    hexNibbleValid b.toNat = true := by
  unfold hexFixed at h
  rw [decide_eq_true_iff] at h
  rcases h with ⟨a, c⟩ | ⟨a, c⟩
  · unfold hexNibbleValid
    rw [hexToNibble_digit _ a c]
    exact decide_eq_true (by omega)
  · unfold hexNibbleValid
    rw [hexToNibble_upper _ a c]
    exact decide_eq_true (by omega)

/-- A valid digit is a fold fixpoint. -/
theorem hexFixed_of_valid (b : UInt8) (hv : hexNibbleValid b.toNat = true) :
    hexFixed b = true := by
  rw [hexNibbleValid, decide_eq_true_iff] at hv
  unfold hexToNibble at hv
  unfold hexFixed
  by_cases h57 : b.toNat ≤ 57
  · rw [if_pos h57] at hv
    by_cases h48 : 48 ≤ b.toNat
    · exact decide_eq_true (Or.inl ⟨h48, h57⟩)
    · rw [if_neg h48] at hv; omega
  · rw [if_neg h57] at hv
    by_cases h70 : b.toNat ≤ 70
    · rw [if_pos h70] at hv
      by_cases h65 : 65 ≤ b.toNat
      · exact decide_eq_true (Or.inr ⟨h65, h70⟩)
      · rw [if_neg h65] at hv; omega
    · rw [if_neg h70] at hv; omega

/-- **RFC 4648 §8 on one block.** The same block decodes to the same byte whether
spelled with uppercase or lowercase digits. -/
theorem decodeHexBlockFold_case_insensitive (hi lo : UInt8)
    (hhi : hexNibbleValid hi.toNat = true) (hlo : hexNibbleValid lo.toNat = true) :
    decodeHexBlockFold [hi, lo] = decodeHexBlockFold (foldList [hi, lo]) := by
  have hhiU : foldByte hi = hi :=
    foldByte_fixed hi (hexFixed_of_valid hi hhi)
  have hloU : foldByte lo = lo :=
    foldByte_fixed lo (hexFixed_of_valid lo hlo)
  rw [(decodeHexBlockFold_both_cases hi lo hhiU hloU).1,
      (decodeHexBlockFold_both_cases hi lo hhiU hloU).2]


/-! ### The whole-run case-insensitive decoder

The strict `hexElem`/`hexRun`/`encodeHex` are untouched. Case-insensitivity is a
**decode-side wrapper**: `foldList` is applied to the whole input, then the strict
run decodes. That is precisely `decodeNormal` lifted one level — not an `Iso`, no
inverse, and it accepts spellings `decodeHex` rejects.

This is the whole-input form of the layer, and it needs no new `Codec` value: the
normalisation is outside the run, where the layer puts it.
-/

/-- The fold lifted to a whole byte string. **Length-preserving by construction**:
`Bytes n → Bytes n`, which is exactly the class of variation this layer is
specified for (design D6) — a whitespace-collapsing normalizer could not be stated
here at all. -/
def foldByteBytes {n : Nat} (s : Bytes n) : Bytes n := fun i => foldByte (s i)

/-- `foldByteBytes` is idempotent. -/
theorem foldByteBytes_idem {n : Nat} (s : Bytes n) :
    foldByteBytes (foldByteBytes s) = foldByteBytes s := by
  funext i
  exact foldByte_idem (s i)

/-- **The case-insensitive whole-input decoder**: fold the input, then decode with
the strict, canonical run. -/
def decodeHexFold {n : Nat} (s : Bytes n) : Option (List UInt8) :=
  Run.decodeFull hexRun (foldByteBytes s)

/-- **RFC 4648 §8 at the whole-string level: both cases decode alike.**
A byte string and its case-folded form decode to the same value. -/
theorem decodeHexFold_both_cases {n : Nat} (s : Bytes n) :
    decodeHexFold s = Run.decodeFull hexRun (foldByteBytes s) := rfl

/-- The canonical spelling decodes identically whether read directly or through
the case-insensitive decoder — the `hfix` discharge at the whole-input level
(`foldByteBytes` is the identity on already-uppercase input). -/
theorem decodeHexFold_of_fixed {n : Nat} (s : Bytes n)
    (hfix : foldByteBytes s = s) :
    decodeHexFold s = Run.decodeFull hexRun s := by
  rw [decodeHexFold_both_cases, hfix]

/-- Lowercase hex decodes to the same value as uppercase: the exact RFC 4648 §8
obligation, whole-input form. The lowercase spelling `0x36,0x66` (the bytes of
`"6f"`) folds to `0x36,0x46` (the bytes of `"6F"`), so the two inputs decode alike. -/
theorem decodeHexFold_lowercase_eq :
    decodeHexFold (fun i : Fin 2 => if i.val = 0 then 0x36 else 0x66) =
    decodeHexFold (fun i : Fin 2 => if i.val = 0 then 0x36 else 0x46) := by
  rw [decodeHexFold_both_cases]
  congr 1
  funext i
  simp only [foldByteBytes]
  show foldByte ((if i.val = 0 then 0x36 else 0x66) : UInt8) =
    foldByte ((if i.val = 0 then 0x36 else 0x46) : UInt8)
  by_cases h : i.val = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    rw [foldByte_folded 0x66 (by decide) (by decide),
        foldByte_fixed 0x46 (by decide)]
    decide

end BaseN.Base16
