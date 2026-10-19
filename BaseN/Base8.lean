/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# BaseN.Base8

Octal encoding: each byte encodes as **three** zero-padded octal digits
(`000`-`377`), MSB-first (`v/64`, `(v/8)%8`, `v%8`).  Three octal digits span
`0..511`, exceeding a byte, so decoding rejects a triple with value `> 255`.

This is not an RFC encoding (RFC 4648 covers only 16/32/64); its semantics are
defined by this package's spec: "three octal digits per byte", matching
`fstar-basen`'s `Data.BaseN.Base08`.  Digit math is `Nat`-level; the alphabet is
ASCII `0-7` (48-55), all `< 256`.

This module expresses the base as a `codec` `Codec (List UInt8)` value
(`octElem`), composed from `satisfy` (one guarded octal digit), `count 3`
(three digits per byte block), and an `iso` that folds the three digit values
into their byte (`v₀·64 + v₁·8 + v₂`, rejecting a block value `> 255`).  The
unbounded run is the productive repetition triple `relOct`/`decodeOct`/
`encodeOct` over `octElem`, whose roundtrip law is the *inherited*
`decodeRepeat_spec`/`encodeRepeat_rel` — no bespoke `encode`/`decode` and no
fresh induction.
-/

import Codec.Combinators

namespace BaseN.Base8

open Codec

/-! ## Digit-level arithmetic (`Nat`) -/

/-- `valToOct d` — the octal digit character (ASCII byte value) for `d ∈ {0..7}`. -/
def valToOct (d : Nat) : Nat := 48 + d

/-- `octToVal e` — the octal value of a digit, or `8` if invalid (`0-7`). -/
def octToVal (e : Nat) : Nat :=
  if e ≤ 55 then if 48 ≤ e then e - 48 else 8 else 8

/-- `octValid e` — `true` iff `e` is an octal digit. -/
def octValid (e : Nat) : Bool := decide (octToVal e ≤ 7)

/-- `octToVal (valToOct d) = d` — the digit ↔ value bijection. -/
theorem octToVal_valToOct (d : Nat) (hd : d ≤ 7) :
    octToVal (valToOct d) = d := by
  unfold octToVal valToOct
  have h1 : 48 + d ≤ 55 := by omega
  have h2 : 48 ≤ 48 + d := by omega
  simp only [h1, ite_true, h2, ite_true]
  omega

/-- `valToOct d` is a valid octal digit. -/
theorem valToOct_valid (d : Nat) (hd : d ≤ 7) : octValid (valToOct d) = true := by
  unfold octValid
  apply decide_eq_true
  rw [octToVal_valToOct d hd]
  exact hd

/-- `valToOct d < 256` — every octal digit is a single byte. -/
theorem valToOct_lt_256 (d : Nat) (hd : d ≤ 7) : valToOct d < 256 := by
  unfold valToOct
  omega

/-- `octValid e = true` implies `octToVal e ≤ 7`. -/
theorem octValid_of_decide (e : Nat) (h : octValid e = true) : octToVal e ≤ 7 :=
  of_decide_eq_true (by simpa [octValid] using h)

/-- When `e` is a valid octal digit, `valToOct (octToVal e) = e` (the digit value
round-trips through its character). -/
theorem valToOct_octToVal_of_valid (e : Nat) (h : octValid e = true) :
    valToOct (octToVal e) = e := by
  have hv : octToVal e ≤ 7 := octValid_of_decide e h
  unfold octToVal valToOct
  by_cases hle : e ≤ 55
  · by_cases hge : 48 ≤ e
    · have hv' : e - 48 = octToVal e := by simp [octToVal, hle, hge]
      have hb : e - 48 ≤ 7 := by omega
      simp [hle, hge]
    · have : octToVal e = 8 := by simp [octToVal, hle, hge]
      omega
  · have : octToVal e = 8 := by simp [octToVal, hle]
    omega

/-- The reconstruction identity: `(v/64)*64 + ((v/8)%8)*8 + v%8 = v`. -/
theorem oct_sum_eq (v : Nat) :
    (v / 64) * 64 + ((v / 8) % 8) * 8 + v % 8 = v := by
  have hdiv64 := Nat.div_add_mod v 64
  have hdiv8 := Nat.div_add_mod v 8
  omega

/-- Uniqueness of the octal decomposition: equal sums of digit triples (each
digit `≤ 7`) give equal triples. -/
theorem oct_decompose_unique (a b c d e f : Nat)
    (_ha : a ≤ 7) (hb : b ≤ 7) (hc : c ≤ 7) (_hd : d ≤ 7) (he : e ≤ 7) (hf : f ≤ 7)
    (h : a * 64 + b * 8 + c = d * 64 + e * 8 + f) :
    a = d ∧ b = e ∧ c = f := by
  have ha_d : a = d := by
    have hm := congrArg (fun x => x / 64) h
    have hmod : b * 8 + c < 64 := by omega
    have hmod' : e * 8 + f < 64 := by omega
    have hm' : (a * 64 + b * 8 + c) / 64 = a := by omega
    have hm'' : (d * 64 + e * 8 + f) / 64 = d := by omega
    rw [hm', hm''] at hm
    exact hm
  have hbe : b = e := by
    have hm := congrArg (fun x => (x % 64) / 8) h
    have hmod : b * 8 + c < 64 := by omega
    have hmod' : e * 8 + f < 64 := by omega
    have hc8 : c < 8 := by omega
    have hf8 : f < 8 := by omega
    have hm' : ((a * 64 + b * 8 + c) % 64) / 8 = b := by omega
    have hm'' : ((d * 64 + e * 8 + f) % 64) / 8 = e := by omega
    rw [hm', hm''] at hm
    exact hm
  have hcf : c = f := by omega
  exact ⟨ha_d, hbe, hcf⟩

/-! ## Generic productivity lemmas (composition preserves `Productive`) -/

/-- `iso` preserves productivity. -/
theorem Productive_iso {α β : Type} (i : Iso α β) (d : Codec α) (h : Productive d) :
    Productive (Codec.iso i d) := by
  intro x n s hrel
  rw [Rel_iso] at hrel
  rcases hrel with ⟨a, _, hda⟩
  exact h a s hda

/-- `seq` is productive when the left component is. -/
theorem Productive_seq_left {α β : Type} (d₁ : Codec α) (d₂ : Codec β)
    (h : Productive d₁) : Productive (Codec.seq d₁ d₂) := by
  intro x n s hrel
  rw [Rel_seq] at hrel
  rcases hrel with ⟨m, hm, s₁, _s₂, _, hr₁, _⟩
  have hmpos : m ≠ 0 := h _ s₁ hr₁
  omega

/-- `count (k+1) p` is productive when `p` is. -/
theorem Productive_count_succ {α : Type} (p : Codec α) (k : Nat) (h : Productive p) :
    Productive (count (k + 1) p) := by
  rw [count]
  exact Productive_iso (Iso.cons) (Codec.seq p (count k p))
        (Productive_seq_left p (count k p) h)

/-- `satisfy p` is productive. -/
theorem Productive_satisfy (p : UInt8 → Bool) : Productive (Codec.satisfy p) :=
  (productive_iff_consumesByte (Codec.satisfy p)).2 (satisfyConsumesByte p)

/-- `count (k+1) (satisfy p)` is productive. -/
theorem Productive_count_satisfy_succ (p : UInt8 → Bool) (k : Nat) :
    Productive (count (k + 1) (Codec.satisfy p)) :=
  Productive_count_succ (Codec.satisfy p) k (Productive_satisfy p)

/-! ## The block isomorphism -/

/-- The octal digit predicate over `UInt8`: holds iff `b` is an octal digit byte. -/
def octDigit (b : UInt8) : Bool := octValid b.toNat

/-- `apply`: read three digit bytes and fold them into their byte (rejecting an
invalid digit or a block value `> 255`). -/
def octBlockApply (cs : List UInt8) : Option UInt8 :=
  match cs with
  | [d0, d1, d2] =>
      if octValid d0.toNat && octValid d1.toNat && octValid d2.toNat then
        let n := octToVal d0.toNat * 64 + octToVal d1.toNat * 8 + octToVal d2.toNat
        if n ≤ 255 then some (UInt8.ofNat n) else none
      else none
  | _ => none

/-- `unapply`: write a byte as its three octal digit bytes (always valid). -/
def octBlockUnapply (b : UInt8) : Option (List UInt8) :=
  some [UInt8.ofNat (valToOct (b.toNat / 64)),
        UInt8.ofNat (valToOct ((b.toNat / 8) % 8)),
        UInt8.ofNat (valToOct (b.toNat % 8))]

/-- A single byte's digits are always valid, and reconstruct to the byte. -/
theorem octDigit_valid_of_byte (b : UInt8) :
    octValid (UInt8.ofNat (valToOct (b.toNat / 64))).toNat = true ∧
    octValid (UInt8.ofNat (valToOct ((b.toNat / 8) % 8))).toNat = true ∧
    octValid (UInt8.ofNat (valToOct (b.toNat % 8))).toNat = true := by
  have hbv : b.toNat < 256 := UInt8.toNat_lt b
  have h39 : b.toNat / 64 ≤ 7 := by omega
  have h40 : (b.toNat / 8) % 8 ≤ 7 := by omega
  have h41 : b.toNat % 8 ≤ 7 := by omega
  constructor
  · rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToOct_lt_256 (b.toNat / 64) h39)]
    exact valToOct_valid (b.toNat / 64) h39
  constructor
  · rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToOct_lt_256 ((b.toNat / 8) % 8) h40)]
    exact valToOct_valid ((b.toNat / 8) % 8) h40
  · rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToOct_lt_256 (b.toNat % 8) h41)]
    exact valToOct_valid (b.toNat % 8) h41

/-- `octToVal ((UInt8.ofNat (valToOct d)).toNat) = d` for `d ≤ 7` — the digit
value round-trips through its byte embedding. -/
theorem octToVal_ofNat_valToOct (d : Nat) (hd : d ≤ 7) :
    octToVal (UInt8.ofNat (valToOct d)).toNat = d := by
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToOct_lt_256 d hd)]
  exact octToVal_valToOct d hd

/-- `apply` is a left inverse of `unapply` on the byte domain: applying the
three digit bytes of `b` reconstructs `b`. -/
theorem octBlockApply_unapply (b : UInt8) :
    octBlockApply [UInt8.ofNat (valToOct (b.toNat / 64)),
                   UInt8.ofNat (valToOct ((b.toNat / 8) % 8)),
                   UInt8.ofNat (valToOct (b.toNat % 8))] = some b := by
  have hbv : b.toNat < 256 := UInt8.toNat_lt b
  rw [octBlockApply]
  rw [octToVal_ofNat_valToOct (b.toNat / 64) (by omega),
      octToVal_ofNat_valToOct ((b.toNat / 8) % 8) (by omega),
      octToVal_ofNat_valToOct (b.toNat % 8) (by omega)]
  have hbv64 : b.toNat / 64 ≤ 7 := by omega
  have hbv8 : (b.toNat / 8) % 8 ≤ 7 := by omega
  have hbv0 : b.toNat % 8 ≤ 7 := by omega
  -- the digit validity is automatic (each valToOct of a ≤7 digit is valid)
  have hd0 : octValid (UInt8.ofNat (valToOct (b.toNat / 64))).toNat = true := by
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToOct_lt_256 (b.toNat / 64) hbv64)]
    exact valToOct_valid (b.toNat / 64) hbv64
  have hd1 : octValid (UInt8.ofNat (valToOct ((b.toNat / 8) % 8))).toNat = true := by
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToOct_lt_256 ((b.toNat / 8) % 8) hbv8)]
    exact valToOct_valid ((b.toNat / 8) % 8) hbv8
  have hd2 : octValid (UInt8.ofNat (valToOct (b.toNat % 8))).toNat = true := by
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (valToOct_lt_256 (b.toNat % 8) hbv0)]
    exact valToOct_valid (b.toNat % 8) hbv0
  rw [hd0, hd1, hd2]
  have hh : ((true && true && true) = true) := by decide
  rw [hh]
  have hsum : b.toNat / 64 * 64 + (b.toNat / 8) % 8 * 8 + b.toNat % 8 = b.toNat :=
    oct_sum_eq b.toNat
  rw [hsum]
  have hle : b.toNat ≤ 255 := by omega
  simp only [hle, ite_true]
  rw [UInt8.ofNat_toNat]

/-- The inverse law of the octal block: `apply` and `unapply` are mutual
inverses on the valid triples / byte domain. -/
theorem octBlockIso_law (cs : List UInt8) (b : UInt8) :
    octBlockApply cs = some b ↔ octBlockUnapply b = some cs := by
  constructor
  · -- forward: apply cs = some b → unapply b = some cs
    intro h
    cases cs with
    | nil => simp [octBlockApply] at h
    | cons d0 rest =>
        cases rest with
        | nil => simp [octBlockApply] at h
        | cons d1 rest2 =>
            cases rest2 with
            | nil => simp [octBlockApply] at h
            | cons d2 rest3 =>
                cases rest3 with
                | nil =>
                    rw [octBlockApply] at h
                    by_cases hv : octValid d0.toNat && octValid d1.toNat && octValid d2.toNat
                    · simp only [hv, ite_true] at h
                      by_cases hl : octToVal d0.toNat * 64 + octToVal d1.toNat * 8 + octToVal d2.toNat ≤ 255
                      · simp only [hl, ite_true] at h
                        have hb_eq : UInt8.ofNat (octToVal d0.toNat * 64 + octToVal d1.toNat * 8 + octToVal d2.toNat) = b := by
                          exact Option.some.inj h
                        have hvd0 : octValid d0.toNat = true :=
                          (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).1
                        have hvd1 : octValid d1.toNat = true :=
                          (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).2
                        have hvd2 : octValid d2.toNat = true := (Bool.and_eq_true_iff.mp hv).2
                        have v0le : octToVal d0.toNat ≤ 7 := octValid_of_decide d0.toNat hvd0
                        have v1le : octToVal d1.toNat ≤ 7 := octValid_of_decide d1.toNat hvd1
                        have v2le : octToVal d2.toNat ≤ 7 := octValid_of_decide d2.toNat hvd2
                        have hd0 : d0.toNat = valToOct (octToVal d0.toNat) := by
                          exact (valToOct_octToVal_of_valid d0.toNat hvd0).symm
                        have hd1 : d1.toNat = valToOct (octToVal d1.toNat) := by
                          exact (valToOct_octToVal_of_valid d1.toNat hvd1).symm
                        have hd2 : d2.toNat = valToOct (octToVal d2.toNat) := by
                          exact (valToOct_octToVal_of_valid d2.toNat hvd2).symm
                        have hb : b.toNat = octToVal d0.toNat * 64 + octToVal d1.toNat * 8 + octToVal d2.toNat := by
                          have hbt := congrArg UInt8.toNat hb_eq
                          rw [UInt8.toNat_ofNat'] at hbt
                          rw [Nat.mod_eq_of_lt] at hbt
                          · exact hbt.symm
                          · omega
                        have hsplit : octToVal d0.toNat = b.toNat / 64 ∧
                                      octToVal d1.toNat = (b.toNat / 8) % 8 ∧
                                      octToVal d2.toNat = b.toNat % 8 := by
                          apply oct_decompose_unique
                          · exact v0le
                          · exact v1le
                          · exact v2le
                          · omega
                          · omega
                          · omega
                          -- the equation: v0*64+v1*8+v2 = (b/64)*64 + ((b/8)%8)*8 + b%8
                          exact hb.symm.trans (oct_sum_eq b.toNat).symm
                        rw [octBlockUnapply]
                        rw [← hsplit.1, ← hsplit.2.1, ← hsplit.2.2]
                        rw [← hd0, ← hd1, ← hd2]
                        simp
                      · simp only [hl, ite_false] at h
                        cases h
                    · simp [hv] at h
                | cons _ _ => simp [octBlockApply] at h
  · -- backward: unapply b = some cs → apply cs = some b
    intro h
    rw [octBlockUnapply] at h
    cases h
    exact octBlockApply_unapply b

/-- The three-digit block ↔ one byte partial isomorphism. -/
def octBlockIso : Iso (List UInt8) UInt8 :=
  { apply := octBlockApply, unapply := octBlockUnapply, law := octBlockIso_law }

/-- The base8 element: three octal digit bytes grouped into one byte. -/
def octElem : Codec UInt8 := Codec.iso octBlockIso (count 3 (Codec.satisfy octDigit))

/-- `octElem` is productive, hence a `ConsumesByte` witness. -/
theorem octConsumesByte : ConsumesByte octElem := by
  unfold octElem
  rw [← productive_iff_consumesByte (Codec.iso octBlockIso (count 3 (Codec.satisfy octDigit)))]
  apply Productive_iso octBlockIso (count 3 (Codec.satisfy octDigit))
  rw [show 3 = 2 + 1 by rfl]
  exact Productive_count_satisfy_succ octDigit 2

/-- The base8 decoder: productive repetition over `octElem`. -/
def decodeOct {n : Nat} (s : Bytes n) : List (List UInt8 × Suffix n) :=
  decodeRepeat octElem octConsumesByte n s

/-- The base8 encoder: repeat `octElem` over the byte list. -/
def encodeOct (bs : List UInt8) : Option (Sigma fun n => Bytes n) :=
  encodeRepeat octElem bs

/-- The base8 relation: `relRepeat` over `Rel octElem`. -/
def relOct : List UInt8 → (n : Nat) → Bytes n → Prop :=
  relRepeat (Rel octElem)

/-! ## Unambiguity and the inherited roundtrip law -/

/-- `satisfy p` is unambiguous: the byte it relates is the unique content of the
single-byte string. -/
theorem Unambiguous_satisfy (p : UInt8 → Bool) :
    Unambiguous (Codec.satisfy p) := by
  intro x y n s hx hy
  rw [Rel_satisfy] at hx hy
  rcases hx with ⟨hpx, hn, hxs⟩
  rcases hy with ⟨hpy, hn', hys⟩
  subst n
  have hxs' : s = single x := by simpa using hxs
  have hys' : s = single y := by simpa using hys
  rw [hys'] at hxs'
  have hxy : single y ⟨0, Nat.zero_lt_one⟩ = single x ⟨0, Nat.zero_lt_one⟩ :=
    congrFun hxs' ⟨0, Nat.zero_lt_one⟩
  simp [single] at hxy
  exact hxy.symm

/-- `Rel (count k (satisfy p)) xs s` pins the byte length: `n = k`. -/
theorem Rel_count_satisfy_len (p : UInt8 → Bool) (k : Nat) (xs : List UInt8)
    {n : Nat} (s : Bytes n) :
    Rel (count k (Codec.satisfy p)) xs s → n = k := by
  induction k generalizing xs n s with
  | zero =>
      intro h
      rw [Rel_count_zero] at h
      exact h.2
  | succ k ih =>
      intro h
      rw [count, Rel_iso] at h
      rcases h with ⟨a, ha, hseq⟩
      rw [Rel_seq] at hseq
      rcases hseq with ⟨m, hm, s₁, s₂, hs, hr₁, hr₂⟩
      rw [Rel_satisfy] at hr₁
      rcases hr₁ with ⟨_, hn1, _⟩
      subst hn1
      have htail : n - 1 = k := ih a.2 s₂ hr₂
      omega

/-- `count k (satisfy p)` is unambiguous: the list of bytes is uniquely
determined by the byte string. -/
theorem count_satisfy_unambiguous (p : UInt8 → Bool) (k : Nat) :
    Unambiguous (count k (Codec.satisfy p)) := by
  intro xs ys n s hx hy
  induction k generalizing xs ys n s with
  | zero =>
      rw [Rel_count_zero] at hx hy
      exact hx.1.trans hy.1.symm
  | succ k ih =>
      rw [count, Rel_iso] at hx hy
      rcases hx with ⟨ax, hax, hseqx⟩
      rcases hy with ⟨ay, hay, hseqy⟩
      rw [Rel_seq] at hseqx hseqy
      rcases hseqx with ⟨mx, hmx, s₁x, s₂x, hsx, hr₁x, hr₂x⟩
      rcases hseqy with ⟨my, hmy, s₁y, s₂y, hsy, hr₁y, hr₂y⟩
      rw [Rel_satisfy] at hr₁x hr₁y
      rcases hr₁x with ⟨_, hnx, hs₁x⟩
      rcases hr₁y with ⟨_, hny, hs₁y⟩
      subst mx
      subst my
      -- After `subst`, `s₁x : Bytes 1` and `hs₁x : s₁x = single ax.fst` (the
      -- `1 = 1` cast in `Rel_satisfy` is defeq to identity).
      have hs₁x' : s₁x = single ax.1 := by simpa using hs₁x
      have hs₁y' : s₁y = single ay.1 := by simpa using hs₁y
      rw [Iso.cons] at hax hay
      dsimp at hax hay
      have hax' : ax.1 :: ax.2 = xs := Option.some.inj hax
      have hay' : ay.1 :: ay.2 = ys := Option.some.inj hay
      -- Read index 0 to extract the head byte equality.
      have h0lt : 0 < n := by omega
      have hx0 : s ⟨0, h0lt⟩ = ax.1 := by
        rw [hsx]
        rw [splice_prefix_read hmx s₁x s₂x ⟨0, h0lt⟩ (by simp)]
        rw [hs₁x']
        rfl
      have hy0 : s ⟨0, h0lt⟩ = ay.1 := by
        rw [hsy]
        rw [splice_prefix_read hmy s₁y s₂y ⟨0, h0lt⟩ (by simp)]
        rw [hs₁y']
        rfl
      have hhead : ax.1 = ay.1 := by
        rw [← hx0, ← hy0]
      -- Drop the prefix to recover the tails (same type `Bytes (n - 1)`).
      have htailEq : s₂x = s₂y := by
        rw [← bdrop_splice hmx s₁x s₂x, ← bdrop_splice hmy s₁y s₂y]
        congr 1
        rw [← hsx]
        rw [hsy]
      have htail : ax.2 = ay.2 := by
        exact ih s₂x hr₂x (by simpa [htailEq] using hr₂y)
      -- Reassemble the lists.
      rw [← hax', ← hay']
      rw [hhead, htail]

/-- `iso` preserves unambiguity: if `d` is unambiguous, so is `iso i d`. -/
theorem Unambiguous_iso {α β : Type} (i : Iso α β) (d : Codec α) (h : Unambiguous d) :
    Unambiguous (Codec.iso i d) := by
  intro x y n s hx hy
  rw [Rel_iso] at hx hy
  rcases hx with ⟨ax, hax, hx⟩
  rcases hy with ⟨ay, hay, hy⟩
  have ha : ax = ay := h s hx hy
  subst ha
  have hxy : some x = some y := by rw [← hax, hay]
  exact Option.some.inj hxy

/-- `octElem` is unambiguous: the decoded byte is uniquely determined. -/
theorem octElem_unambiguous : Unambiguous octElem := by
  unfold octElem
  apply Unambiguous_iso octBlockIso (count 3 (Codec.satisfy octDigit))
  exact count_satisfy_unambiguous octDigit 3

/-- `Rel octElem x s` pins the byte length: `n = 3`. -/
theorem Rel_octElem_len (x : UInt8) {n : Nat} (s : Bytes n) :
    Rel octElem x s → n = 3 := by
  intro h
  unfold octElem at h
  rw [Rel_iso] at h
  rcases h with ⟨a, _, hc⟩
  exact Rel_count_satisfy_len octDigit 3 a s hc

/-- The base8 relation is unambiguous: a byte list is uniquely determined by
its encoded byte string (via the productive `octElem` step, which consumes
exactly 3 bytes). -/
theorem relOct_unambiguous : relUnambiguous relOct := by
  intro a b n s ha hb
  dsimp [relOct] at ha hb
  induction a generalizing b n s with
  | nil =>
      rw [relRepeat_nil] at ha
      subst n
      cases b with
      | nil => rfl
      | cons y ys =>
          rw [relRepeat_cons] at hb
          rcases hb with ⟨m, hm, s₁, s₂, hs, hy, _⟩
          have hlen : m = 3 := Rel_octElem_len y s₁ hy
          have hm0 : m = 0 := by omega
          omega
  | cons x xs ih =>
      cases b with
      | nil =>
          rw [relRepeat_nil] at hb
          rw [relRepeat_cons] at ha
          rcases ha with ⟨mx, hmx, s₁x, s₂x, hsx, hx, hxs⟩
          have hlen : mx = 3 := Rel_octElem_len x s₁x hx
          subst n
          have hm0 : mx = 0 := by omega
          omega
      | cons y ys =>
          rw [relRepeat_cons] at ha hb
          rcases ha with ⟨mx, hmx, s₁x, s₂x, hsx, hx, hxs⟩
          rcases hb with ⟨my, hmy, s₁y, s₂y, hsy, hy, hys⟩
          have hlx : mx = 3 := Rel_octElem_len x s₁x hx
          have hly : my = 3 := Rel_octElem_len y s₁y hy
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
            exact octElem_unambiguous s₁x hx (by rw [hpre]; exact hy)
          have htail : xs = ys := by
            exact ih s₂x hxs (by simpa [htaily] using hys)
          rw [hhead, htail]

/-- Full-consumption decode is unambiguous for `octElem`: two full-consumption
results over the same input byte string agree. -/
theorem octDecodeFull_unambiguous {x y : List UInt8} {n : Nat} (s : Bytes n) :
    (x, Suffix.empty n) ∈ decodeRepeat octElem octConsumesByte n s →
    (y, Suffix.empty n) ∈ decodeRepeat octElem octConsumesByte n s → x = y := by
  intro hx hy
  rcases (decodeRepeat_spec octElem octConsumesByte x n s (Suffix.empty n)).1 hx with ⟨s₀x, hsx, hrx⟩
  rcases (decodeRepeat_spec octElem octConsumesByte y n s (Suffix.empty n)).1 hy with ⟨s₀y, hsy, hry⟩
  have hs₀ : s₀x = s₀y := by
    have hpre : (Suffix.empty n).prepend s₀x = (Suffix.empty n).prepend s₀y := by
      exact hsx.symm.trans hsy
    exact prepend_prefix_eq (Suffix.empty n) s₀x s₀y hpre
  exact relOct_unambiguous s₀x hrx (by rw [hs₀]; exact hry)

/-- The base8 roundtrip law: a byte list encoded by `octElem` decodes fully back
to itself. This is the inherited `decodeRepeat_spec`/`encodeRepeat_rel` roundtrip
(the `Codec (List UInt8)` analogue of `Codec.roundtrip`), gated by the
`octDecodeFull_unambiguous` uniqueness fact. `[propext, Quot.sound]`-only. -/
theorem roundtrip (bs : List UInt8) {n : Nat} {s : Bytes n} :
    encodeOct bs = some ⟨n, s⟩ → decodeFull octElem octConsumesByte n s = some bs := by
  intro he
  have hrel : relRepeat (Rel octElem) bs n s := encodeRepeat_rel octElem bs he
  have hmem : (bs, Suffix.empty n) ∈ decodeRepeat octElem octConsumesByte n s := by
    refine (decodeRepeat_spec octElem octConsumesByte bs n s (Suffix.empty n)).2 ⟨
      cast (congrArg Bytes (Nat.sub_zero n).symm) s, ?_, ?_⟩
    · exact (prepend_empty_eq s).symm
    · exact (relRepeat_cast (Rel octElem) bs (Nat.sub_zero n).symm s).2 hrel
  exact (decodeFull_spec octElem octConsumesByte (fun {x y} {m} (t : Bytes m) =>
    octDecodeFull_unambiguous (s := t)) s bs).2 hmem

end BaseN.Base8
