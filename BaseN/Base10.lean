/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# BaseN.Base10

Decimal encoding, **byte-oriented** and **sign-free**: each byte encodes as
**three zero-padded decimal digits** (`000`-`255`), MSB-first (`v/100`,
`(v/10)%10`, `v%10`).  Three decimal digits span `0..999`, exceeding a byte, so
decoding rejects a triple with value `> 255`.

Not an RFC encoding; semantics are defined by this package's spec.  The
three-digit fixed width is what makes `decode (encode bs) = some bs` hold
unconditionally.  Alphabet is ASCII `0-9` (48-57), all `< 256`.

This module expresses the base as a `codec` `Codec (List UInt8)` value
(`digElem`), composed from `satisfy` (one guarded decimal digit), `count 3`
(three digits per byte block), and an `iso` that folds the three digit values
into their byte (`v₀·100 + v₁·10 + v₂`, rejecting a block value `> 255`).  The
unbounded run is the productive repetition triple `relDig`/`decodeDig`/
`encodeDig`, whose roundtrip is the inherited `decodeRepeat_spec`/
`encodeRepeat_rel` law.
-/

import BaseN.Common

namespace BaseN.Base10

open Codec
open BaseN.Common

/-! ## Digit-level arithmetic (`Nat`) -/

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

/-- `digValid e = true` implies `digVal e ≤ 9`. -/
theorem digValid_of_decide (e : Nat) (h : digValid e = true) : digVal e ≤ 9 :=
  of_decide_eq_true (by simpa [digValid] using h)

/-- When `e` is a valid decimal digit, `valToDig (digVal e) = e`. -/
theorem valToDig_digVal_of_valid (e : Nat) (h : digValid e = true) :
    valToDig (digVal e) = e := by
  have hv : digVal e ≤ 9 := digValid_of_decide e h
  unfold digVal valToDig
  by_cases hle : e ≤ 57
  · by_cases hge : 48 ≤ e
    · have hv' : e - 48 = digVal e := by simp [digVal, hle, hge]
      have hb : e - 48 ≤ 9 := by omega
      simp [hle, hge]
    · have : digVal e = 10 := by simp [digVal, hle, hge]
      omega
  · have : digVal e = 10 := by simp [digVal, hle]
    omega

/-- The reconstruction identity: `(v/100)*100 + ((v/10)%10)*10 + v%10 = v`. -/
theorem dig_sum_eq (v : Nat) :
    (v / 100) * 100 + ((v / 10) % 10) * 10 + v % 10 = v := by
  have hdiv100 := Nat.div_add_mod v 100
  have hdiv10 := Nat.div_add_mod v 10
  omega

/-- Uniqueness of the decimal decomposition: equal sums of digit triples (each
digit `≤ 9`) give equal triples. -/
theorem dig_decompose_unique (a b c d e f : Nat)
    (_ha : a ≤ 9) (_hb : b ≤ 9) (_hc : c ≤ 9) (_hd : d ≤ 9) (_he : e ≤ 9) (_hf : f ≤ 9)
    (h : a * 100 + b * 10 + c = d * 100 + e * 10 + f) :
    a = d ∧ b = e ∧ c = f := by
  have ha_d : a = d := by
    have hm := congrArg (fun x => x / 100) h
    omega
  have hbe : b = e := by
    have hm := congrArg (fun x => (x % 100) / 10) h
    omega
  have hcf : c = f := by omega
  exact ⟨ha_d, hbe, hcf⟩

/-! ## The block isomorphism -/

/-- The decimal digit predicate over `UInt8`. -/
def digDigit (b : UInt8) : Bool := digValid b.toNat

/-- `apply`: read three digit bytes and fold them into their byte (rejecting an
invalid digit or a block value `> 255`). -/
def digBlockApply (cs : List UInt8) : Option UInt8 :=
  match cs with
  | [d0, d1, d2] =>
      if digValid d0.toNat && digValid d1.toNat && digValid d2.toNat then
        let n := digVal d0.toNat * 100 + digVal d1.toNat * 10 + digVal d2.toNat
        if n ≤ 255 then some (UInt8.ofNat n) else none
      else none
  | _ => none

/-- `unapply`: write a byte as its three decimal digit bytes (always valid). -/
def digBlockUnapply (b : UInt8) : Option (List UInt8) :=
  some [toByte (valToDig (b.toNat / 100)),
        toByte (valToDig ((b.toNat / 10) % 10)),
        toByte (valToDig (b.toNat % 10))]

/-- A single byte's digits are always valid. -/
theorem digDigit_valid_of_byte (b : UInt8) :
    digValid (toByte (valToDig (b.toNat / 100))).toNat = true ∧
    digValid (toByte (valToDig ((b.toNat / 10) % 10))).toNat = true ∧
    digValid (toByte (valToDig (b.toNat % 10))).toNat = true := by
  have hbv : b.toNat < 256 := UInt8.toNat_lt b
  have h0 : b.toNat / 100 ≤ 9 := by omega
  have h1 : (b.toNat / 10) % 10 ≤ 9 := by omega
  have h2 : b.toNat % 10 ≤ 9 := by omega
  constructor
  · rw [show (toByte (valToDig (b.toNat / 100))).toNat = (UInt8.ofNat (valToDig (b.toNat / 100))).toNat by rfl]
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToDig_lt_256 (b.toNat / 100) h0)]
    exact valToDig_valid (b.toNat / 100) h0
  constructor
  · rw [show (toByte (valToDig ((b.toNat / 10) % 10))).toNat = (UInt8.ofNat (valToDig ((b.toNat / 10) % 10))).toNat by rfl]
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToDig_lt_256 ((b.toNat / 10) % 10) h1)]
    exact valToDig_valid ((b.toNat / 10) % 10) h1
  · rw [show (toByte (valToDig (b.toNat % 10))).toNat = (UInt8.ofNat (valToDig (b.toNat % 10))).toNat by rfl]
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToDig_lt_256 (b.toNat % 10) h2)]
    exact valToDig_valid (b.toNat % 10) h2

/-- `digVal ((toByte (valToDig d)).toNat) = d` for `d ≤ 9`. -/
theorem digVal_toByte_valToDig (d : Nat) (hd : d ≤ 9) :
    digVal (toByte (valToDig d)).toNat = d := by
  rw [show (toByte (valToDig d)).toNat = (UInt8.ofNat (valToDig d)).toNat by rfl]
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToDig_lt_256 d hd)]
  exact digVal_valToDig d hd

/-- `apply` is a left inverse of `unapply`. -/
theorem digBlockApply_unapply (b : UInt8) :
    digBlockApply [toByte (valToDig (b.toNat / 100)),
                   toByte (valToDig ((b.toNat / 10) % 10)),
                   toByte (valToDig (b.toNat % 10))] = some b := by
  have hbv : b.toNat < 256 := UInt8.toNat_lt b
  rw [digBlockApply]
  rw [digVal_toByte_valToDig (b.toNat / 100) (by omega),
      digVal_toByte_valToDig ((b.toNat / 10) % 10) (by omega),
      digVal_toByte_valToDig (b.toNat % 10) (by omega)]
  have hd := digDigit_valid_of_byte b
  rw [hd.1, hd.2.1, hd.2.2]
  have hh : (true && true && true) = true := by decide
  rw [hh]
  have hsum : b.toNat / 100 * 100 + (b.toNat / 10) % 10 * 10 + b.toNat % 10 = b.toNat :=
    dig_sum_eq b.toNat
  rw [hsum]
  have hle : b.toNat ≤ 255 := by omega
  simp only [hle, ite_true]
  simp

/-- The inverse law of the decimal block. -/
theorem digBlockIso_law (cs : List UInt8) (b : UInt8) :
    digBlockApply cs = some b ↔ digBlockUnapply b = some cs := by
  constructor
  · intro h
    cases cs with
    | nil => simp [digBlockApply] at h
    | cons d0 rest =>
        cases rest with
        | nil => simp [digBlockApply] at h
        | cons d1 rest2 =>
            cases rest2 with
            | nil => simp [digBlockApply] at h
            | cons d2 rest3 =>
                cases rest3 with
                | nil =>
                    rw [digBlockApply] at h
                    by_cases hv : digValid d0.toNat && digValid d1.toNat && digValid d2.toNat
                    · simp only [hv, ite_true] at h
                      by_cases hl : digVal d0.toNat * 100 + digVal d1.toNat * 10 + digVal d2.toNat ≤ 255
                      · simp only [hl, ite_true] at h
                        have hb_eq : UInt8.ofNat (digVal d0.toNat * 100 + digVal d1.toNat * 10 + digVal d2.toNat) = b := by
                          exact Option.some.inj h
                        have hv' : ((digValid d0.toNat = true ∧ digValid d1.toNat = true) ∧ digValid d2.toNat = true) := by
                          simpa only [Bool.and_eq_true_iff] using hv
                        have hvd0 : digValid d0.toNat = true := hv'.1.1
                        have hvd1 : digValid d1.toNat = true := hv'.1.2
                        have hvd2 : digValid d2.toNat = true := hv'.2
                        have v0le := digValid_of_decide d0.toNat hvd0
                        have v1le := digValid_of_decide d1.toNat hvd1
                        have v2le := digValid_of_decide d2.toNat hvd2
                        have hd0 : d0.toNat = valToDig (digVal d0.toNat) :=
                          (valToDig_digVal_of_valid d0.toNat hvd0).symm
                        have hd1 : d1.toNat = valToDig (digVal d1.toNat) :=
                          (valToDig_digVal_of_valid d1.toNat hvd1).symm
                        have hd2 : d2.toNat = valToDig (digVal d2.toNat) :=
                          (valToDig_digVal_of_valid d2.toNat hvd2).symm
                        have hb : b.toNat = digVal d0.toNat * 100 + digVal d1.toNat * 10 + digVal d2.toNat := by
                          have hbt := congrArg UInt8.toNat hb_eq
                          rw [UInt8.toNat_ofNat'] at hbt
                          rw [Nat.mod_eq_of_lt] at hbt
                          · exact hbt.symm
                          · omega
                        have hsplit : digVal d0.toNat = b.toNat / 100 ∧
                                      digVal d1.toNat = (b.toNat / 10) % 10 ∧
                                      digVal d2.toNat = b.toNat % 10 := by
                          exact dig_decompose_unique
                            (digVal d0.toNat) (digVal d1.toNat) (digVal d2.toNat)
                            (b.toNat / 100) ((b.toNat / 10) % 10) (b.toNat % 10)
                            v0le v1le v2le (by omega) (by omega) (by omega)
                            (hb.symm.trans (dig_sum_eq b.toNat).symm)
                        rw [digBlockUnapply]
                        rw [← hsplit.1, ← hsplit.2.1, ← hsplit.2.2]
                        rw [← hd0, ← hd1, ← hd2]
                        simp [toByte]
                      · simp only [hl, ite_false] at h
                        cases h
                    · simp [hv] at h
                | cons _ _ => simp [digBlockApply] at h
  · intro h
    rw [digBlockUnapply] at h
    cases h
    exact digBlockApply_unapply b

/-- The three-decimal-digit block ↔ one byte partial isomorphism. -/
def digBlockIso : Iso (List UInt8) UInt8 :=
  { apply := digBlockApply, unapply := digBlockUnapply, law := digBlockIso_law }

/-- The base10 element: three decimal digit bytes grouped into one byte. -/
def digElem : Codec UInt8 := Codec.iso digBlockIso (count 3 (Codec.satisfy digDigit))

/-- `digElem` is productive. -/
theorem digConsumesByte : ConsumesByte digElem := by
  unfold digElem
  rw [← productive_iff_consumesByte (Codec.iso digBlockIso (count 3 (Codec.satisfy digDigit)))]
  apply Productive_iso digBlockIso (count 3 (Codec.satisfy digDigit))
  rw [show 3 = 2 + 1 by rfl]
  exact Productive_count_satisfy_succ digDigit 2

/-- The base10 run value: the element + productivity witness. -/
def digRun : Run UInt8 := { elem := digElem, step := digConsumesByte }

/-- The base10 decoder. -/
def decodeDig {n : Nat} (s : Bytes n) : List (List UInt8 × Suffix n) :=
  decodeRepeat digElem digConsumesByte n s

/-- The base10 encoder. -/
def encodeDig (bs : List UInt8) : Option (Sigma fun n => Bytes n) :=
  encodeRepeat digElem bs

/-- The base10 relation. -/
def relDig : List UInt8 → (n : Nat) → Bytes n → Prop :=
  relRepeat (Rel digElem)

/-! ## Unambiguity and the inherited roundtrip law -/

/-- `digElem` is unambiguous. -/
theorem digElem_unambiguous : Unambiguous digElem := by
  unfold digElem
  apply Unambiguous_iso digBlockIso (count 3 (Codec.satisfy digDigit))
  exact count_satisfy_unambiguous digDigit 3

/-- `Rel digElem x s` pins the byte length: `n = 3`. -/
theorem Rel_digElem_len (x : UInt8) {n : Nat} (s : Bytes n) :
    Rel digElem x s → n = 3 := by
  intro h
  unfold digElem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, _, hc⟩
  exact Rel_count_satisfy_len digDigit 3 a s hc

/-- The base10 relation is unambiguous. -/
theorem relDig_unambiguous : relUnambiguous relDig := by
  intro a b n s ha hb
  dsimp [relDig] at ha hb
  induction a generalizing b n s with
  | nil =>
      rw [relRepeat_nil] at ha
      subst n
      cases b with
      | nil => rfl
      | cons y ys =>
          rw [relRepeat_cons] at hb
          rcases hb with ⟨m, hm, s₁, s₂, hs, hy, _⟩
          have hlen : m = 3 := Rel_digElem_len y s₁ hy
          have hm0 : m = 0 := by omega
          omega
  | cons x xs ih =>
      cases b with
      | nil =>
          rw [relRepeat_nil] at hb
          rw [relRepeat_cons] at ha
          rcases ha with ⟨mx, hmx, s₁x, s₂x, hsx, hx, hxs⟩
          have hlen : mx = 3 := Rel_digElem_len x s₁x hx
          subst n
          have hm0 : mx = 0 := by omega
          omega
      | cons y ys =>
          rw [relRepeat_cons] at ha hb
          rcases ha with ⟨mx, hmx, s₁x, s₂x, hsx, hx, hxs⟩
          rcases hb with ⟨my, hmy, s₁y, s₂y, hsy, hy, hys⟩
          have hlx : mx = 3 := Rel_digElem_len x s₁x hx
          have hly : my = 3 := Rel_digElem_len y s₁y hy
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
            exact digElem_unambiguous s₁x hx (by rw [hpre]; exact hy)
          have htail : xs = ys := by
            exact ih s₂x hxs (by simpa [htaily] using hys)
          rw [hhead, htail]

/-- Full-consumption decode is unambiguous for `digElem`. -/
theorem digDecodeFull_unambiguous {x y : List UInt8} {n : Nat} (s : Bytes n) :
    (x, Suffix.empty n) ∈ decodeRepeat digElem digConsumesByte n s →
    (y, Suffix.empty n) ∈ decodeRepeat digElem digConsumesByte n s → x = y := by
  intro hx hy
  rcases (decodeRepeat_spec digElem digConsumesByte x n s (Suffix.empty n)).1 hx with ⟨s₀x, hsx, hrx⟩
  rcases (decodeRepeat_spec digElem digConsumesByte y n s (Suffix.empty n)).1 hy with ⟨s₀y, hsy, hry⟩
  have hs₀ : s₀x = s₀y := by
    have hpre : (Suffix.empty n).prepend s₀x = (Suffix.empty n).prepend s₀y := by
      exact hsx.symm.trans hsy
    exact prepend_prefix_eq (Suffix.empty n) s₀x s₀y hpre
  exact relDig_unambiguous s₀x hrx (by rw [hs₀]; exact hry)

/-- The base10 roundtrip law. `[propext, Quot.sound]`-only. -/
theorem roundtrip (bs : List UInt8) {n : Nat} {s : Bytes n} :
    encodeDig bs = some ⟨n, s⟩ → decodeFull digElem digConsumesByte n s = some bs := by
  intro he
  have hrel : relRepeat (Rel digElem) bs n s := encodeRepeat_rel digElem bs he
  have hmem : (bs, Suffix.empty n) ∈ decodeRepeat digElem digConsumesByte n s := by
    refine (decodeRepeat_spec digElem digConsumesByte bs n s (Suffix.empty n)).2 ⟨
      cast (congrArg Bytes (Nat.sub_zero n).symm) s, ?_, ?_⟩
    · exact (prepend_empty_eq s).symm
    · exact (relRepeat_cast (Rel digElem) bs (Nat.sub_zero n).symm s).2 hrel
  exact (decodeFull_spec digElem digConsumesByte (fun {x y} {m} (t : Bytes m) =>
    digDecodeFull_unambiguous (s := t)) s bs).2 hmem

/-! ## Conformance: canonical encoding, converse, injectivity -/

/-- `digElem` is functional: one byte relates to a unique 3-byte string. -/
theorem digElem_functional : Functional digElem := by
  unfold digElem
  exact Functional_iso digBlockIso (count 3 (Codec.satisfy digDigit))
    (Functional_count_satisfy digDigit 3)

/-- Every byte of a `digElem`-related string is a decimal digit. -/
theorem Rel_digElem_canonical {x : UInt8} {m : Nat} {t : Bytes m} :
    Rel digElem x t → ∀ i : Fin m, digDigit (t i) = true := by
  intro ht
  change Rel (Codec.iso digBlockIso (count 3 (Codec.satisfy digDigit))) x t at ht
  rw [Rel_iso] at ht
  rcases ht with ⟨a, _, hc⟩
  exact Rel_count_satisfy_forall digDigit 3 a t hc

/-- Canonical encoding (alphabet-only): every byte `encodeDig` produces is a decimal
digit. `[propext, Quot.sound]`-only. -/
theorem encodeDig_canonical (bs : List UInt8) {n : Nat} {s : Bytes n} :
    encodeDig bs = some ⟨n, s⟩ → ∀ i : Fin n, digDigit (s i) = true := by
  intro he
  have hrel : relRepeat (Rel digElem) bs n s := encodeRepeat_rel digElem bs he
  exact relRepeat_forall digDigit (fun x {m} t ht => Rel_digElem_canonical (t := t) ht) bs n s hrel

/-- Converse: a fully-decoded value re-encodes to exactly the input bytes. -/
theorem decode_encode_inverse {n : Nat} {s : Bytes n} (v : List UInt8) :
    decodeFull digElem digConsumesByte n s = some v → encodeDig v = some ⟨n, s⟩ := by
  intro hd
  have hmem : (v, Suffix.empty n) ∈ decodeRepeat digElem digConsumesByte n s :=
    decodeFull_some digElem digConsumesByte s v hd
  rcases (decodeRepeat_spec digElem digConsumesByte v n s (Suffix.empty n)).1 hmem with ⟨s₀, hs, hrel⟩
  have hne : s = cast (congrArg Bytes (Nat.sub_zero n)) s₀ := by
    rw [hs]
    exact prepend_empty_eq s₀
  have hrels : relRepeat (Rel digElem) v n s := by
    rw [hne]
    exact (relRepeat_cast (Rel digElem) v (Nat.sub_zero n) s₀).1 hrel
  exact encodeRepeat_of_rel digElem digElem_functional v s hrels

/-- `digBlockUnapply` is *total*, and its digits are exactly the 3 digits of the
byte: length 3, every one a `digDigit`. This is what makes `digElem`'s
encoder total — its only failure mode would be a produced digit failing
`satisfy`. -/
theorem digBlockUnapply_digits (b : UInt8) :
    ∃ ds, digBlockUnapply b = some ds ∧ ds.length = 3 ∧ ∀ d ∈ ds, digDigit d = true := by
  refine ⟨[toByte (valToDig (b.toNat / 100)), toByte (valToDig ((b.toNat / 10) % 10)), toByte (valToDig (b.toNat % 10))], rfl, rfl, ?_⟩
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  unfold digDigit
  rcases hd with h | h | h <;> subst h
  · exact (digDigit_valid_of_byte b).1
  · exact (digDigit_valid_of_byte b).2.1
  · exact (digDigit_valid_of_byte b).2.2

/-- Every byte encodes through `digElem`: the element encoder is total. -/
theorem digElem_encode_ne_none (b : UInt8) : Codec.encode digElem b ≠ none := by
  obtain ⟨ds, hds, hlen, hpd⟩ := digBlockUnapply_digits b
  unfold digElem
  simp only [Codec.encode, digBlockIso, hds, Option.bind]
  rw [← hlen]
  exact count_satisfy_encode_ne_none digDigit ds hpd

/-- **Decimal encoding is total** — `encodeDig` never returns `none`.

This is the fact that upgrades the injectivity law to the spec's plain
`Option`-equality form (task 6.2): with totality in hand the `none`/`none` and
`some`/`none` cases of `encodeDig v = encodeDig v'` are refuted, leaving only
the both-succeed case, which is `encode_injective`.

`encodeRepeat` fails only when the element encoder does, so this is an induction
on the value list with `digElem_encode_ne_none` at each step.
`[propext, Quot.sound]`-only. -/
theorem encodeDig_ne_none (bs : List UInt8) : encodeDig bs ≠ none := by
  unfold encodeDig
  induction bs with
  | nil => simp [Codec.encodeRepeat]
  | cons b rest ih =>
      rw [Codec.encodeRepeat]
      have hb : Codec.encode digElem b ≠ none := digElem_encode_ne_none b
      cases h₁ : Codec.encode digElem b with
      | none => exact absurd h₁ hb
      | some e₁ =>
          cases h₂ : Codec.encodeRepeat digElem rest with
          | none => exact absurd h₂ ih
          | some e₂ => simp

/-- encoding is injective: a byte list has a unique decimal encoding (the
both-succeed form, which the spec's `Option`-equality law reduces to). -/
theorem encode_injective {v v' : List UInt8} {n : Nat} {s : Bytes n} :
    encodeDig v = some ⟨n, s⟩ → encodeDig v' = some ⟨n, s⟩ → v = v' := by
  intro hv hv'
  have hrelv : relRepeat (Rel digElem) v n s := encodeRepeat_rel digElem v hv
  have hrelv' : relRepeat (Rel digElem) v' n s := encodeRepeat_rel digElem v' hv'
  exact relDig_unambiguous s hrelv hrelv'

/-- **Decimal encoding is injective, in the spec's `Option`-equality form:**
`encodeDig v = encodeDig v' → v = v'` — exactly the `basen` spec's Scenario
"Encoding is injective" (`encode{X} v = encode{X} v' → v = v'`).

Because `encodeDig` is total (`encodeDig_ne_none`), the left side cannot be
`none`; destructure the common result and hand both successes to
`encode_injective`. `[propext, Quot.sound]`-only. -/
theorem encodeDig_injective_eq {v v' : List UInt8} (h : encodeDig v = encodeDig v') :
    v = v' := by
  cases hv : encodeDig v with
  | none => exact absurd hv (encodeDig_ne_none v)
  | some e =>
      rcases e with ⟨n, s⟩
      have hv' : encodeDig v' = some ⟨n, s⟩ := by rw [← h]; exact hv
      exact encode_injective hv hv'

/-- A fully-decoded value means every input byte is a decimal digit. `[propext,
Quot.sound]`-only. -/
theorem decodeFull_canonical {n : Nat} {s : Bytes n} {v : List UInt8} :
    decodeFull digElem digConsumesByte n s = some v → ∀ i : Fin n, digDigit (s i) = true := by
  intro hd
  have hmem : (v, Suffix.empty n) ∈ decodeRepeat digElem digConsumesByte n s :=
    decodeFull_some digElem digConsumesByte s v hd
  rcases (decodeRepeat_spec digElem digConsumesByte v n s (Suffix.empty n)).1 hmem with ⟨s₀, hs, hrel⟩
  have hne : s = cast (congrArg Bytes (Nat.sub_zero n)) s₀ := by
    rw [hs]
    exact prepend_empty_eq s₀
  have hrels : relRepeat (Rel digElem) v n s := by
    rw [hne]
    exact (relRepeat_cast (Rel digElem) v (Nat.sub_zero n) s₀).1 hrel
  exact relRepeat_forall digDigit (fun x {m} t ht => Rel_digElem_canonical (t := t) ht) v n s hrels

/-- **Base10: decode succeeds iff `s` is in `encodeDig`'s image, at that value.**
`decodeFull digElem digConsumesByte n s = some v ↔ ∃ v', encodeDig v' = some ⟨n, s⟩ ∧ v = v'`.

The decimal analogue of `decodeFullB64_char`/`decodeFullB32_char` (task 7.1): the
decoder accepts a byte string exactly when it is a canonical encoding, and then
returns the unique value that encodes to it. Pure assembly over the already-proved
`decode_encode_inverse` (`→`) and `roundtrip` (`←`). `[propext, Quot.sound]`-only. -/
theorem decodeFull_B10_char {n : Nat} (s : Bytes n) (v : List UInt8) :
    decodeFull digElem digConsumesByte n s = some v ↔ ∃ v', encodeDig v' = some ⟨n, s⟩ ∧ v = v' := by
  constructor
  · intro h
    exact ⟨v, decode_encode_inverse v h, rfl⟩
  · rintro ⟨w, he, hv⟩
    rw [hv]
    exact roundtrip w he

/-- Rejection: a byte outside the decimal alphabet is rejected. -/
theorem rejects_invalid_byte (bad : UInt8) (hbad : digDigit bad = false) :
    decodeFull digElem digConsumesByte 1 (fun _ => bad) = none := by
  cases h : decodeFull digElem digConsumesByte 1 (fun _ => bad) with
  | none => rfl
  | some v =>
      have hall := decodeFull_canonical (n := 1) (s := fun _ => bad) (v := v) h
      have h0 : digDigit bad = true := by simpa using (hall ⟨0, by decide⟩)
      rw [hbad] at h0
      simp at h0

/-- Rejection: wrong arity (not a multiple of 3 decimal digits) is rejected. -/
theorem rejects_bad_arity :
    decodeFull digElem digConsumesByte 1 (fun _ => 0x30) = none := by
  cases h : decodeFull digElem digConsumesByte 1 (fun _ => 0x30) with
  | none => rfl
  | some v =>
      have hmem : (v, Suffix.empty 1) ∈ decodeRepeat digElem digConsumesByte 1 (fun _ => 0x30) :=
        decodeFull_some digElem digConsumesByte (fun _ => 0x30) v h
      rcases (decodeRepeat_spec digElem digConsumesByte v 1 (fun _ => 0x30) (Suffix.empty 1)).1 hmem with ⟨s₀, hs, hrel⟩
      have hne : (fun _ => 0x30 : Bytes 1) = cast (congrArg Bytes (Nat.sub_zero 1)) s₀ := by
        rw [hs]
        exact prepend_empty_eq s₀
      have hrels : relRepeat (Rel digElem) v 1 (fun _ => 0x30) := by
        rw [hne]
        exact (relRepeat_cast (Rel digElem) v (Nat.sub_zero 1) s₀).1 hrel
      cases v with
      | nil =>
          rw [relRepeat_nil] at hrels
          omega
      | cons x xs =>
          rw [relRepeat_cons] at hrels
          rcases hrels with ⟨m, hm, s₁, s₂, _, hx, _⟩
          have hlen : m = 3 := Rel_digElem_len x s₁ hx
          omega

/-- Rejection: a decimal triple that overflows a byte (`> 255`) is rejected;
`256` (`2·100 + 5·10 + 6 = 256`) is the canonical overflow vector. -/
theorem rejects_overflow :
    decodeFull digElem digConsumesByte 3 (fun i : Fin 3 => [0x32, 0x35, 0x36][i]) = none := by
  unfold decodeFull
  rw [WellFounded.fix_eq]
  simp only
  rw [Codec.decodeFullStep.eq_def]
  simp
  rfl

end BaseN.Base10
