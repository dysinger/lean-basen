/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Combinators

/-!
# BaseN.Common — generic fixed-width leaf lemmas

The uniform-leaf recipe (established in `BaseN.Base8`) decomposes into a *generic*
part — productivity and unambiguity lemmas over `satisfy`/`count`/`iso`/`seq` that
hold for any byte predicate and any block width — and a *per-base* part (digit
arithmetic, the block `Iso`, and the `Rel <elem> …` length-pinning).  This module
holds the generic part so each base reuses it verbatim rather than re-deriving it.

Everything here is `[propext, Quot.sound]`-only, stdlib-only (no mathlib, no
`norm_num`/`Classical.choice`).
-/

namespace BaseN.Common

open Codec

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

/-! ## Generic unambiguity lemmas -/

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

/-- `satisfy p` is functional: a `p`-byte relates to a unique (length-1) string. -/
theorem Functional_satisfy (p : UInt8 → Bool) : Functional (Codec.satisfy p) := by
  intro x n₁ n₂ s₁ s₂ h₁ h₂
  rw [Rel_satisfy] at h₁ h₂
  rcases h₁ with ⟨_, hn₁, hs₁⟩
  rcases h₂ with ⟨_, hn₂, hs₂⟩
  subst n₁; subst n₂
  have hs₁' : s₁ = single x := by simpa using hs₁
  have hs₂' : s₂ = single x := by simpa using hs₂
  rw [hs₁', hs₂']

/-- `count k (satisfy p)` is functional: a list value relates to a unique `Bytes k`. -/
theorem Functional_count_satisfy (p : UInt8 → Bool) (k : Nat) :
    Functional (count k (Codec.satisfy p)) := by
  intro xs n₁ n₂ s₁ s₂ h₁ h₂
  induction k generalizing xs n₁ n₂ s₁ s₂ with
  | zero =>
      rw [Rel_count_zero] at h₁ h₂
      rcases h₁ with ⟨hx₁, hn₁⟩; rcases h₂ with ⟨hx₂, hn₂⟩
      subst n₁; subst n₂
      apply Sigma.ext
      · rfl
      · apply heq_of_eq; apply Bytes.ext; intro i; exact Fin.elim0 i
  | succ k ih =>
      rw [count, Rel_iso] at h₁ h₂
      rcases h₁ with ⟨a₁, ha₁, hseq₁⟩
      rcases h₂ with ⟨a₂, ha₂, hseq₂⟩
      rw [Rel_seq] at hseq₁ hseq₂
      rcases hseq₁ with ⟨m₁, hm₁, s₁₁, s₁₂, hsp₁, hr₁₁, hr₁₂⟩
      rcases hseq₂ with ⟨m₂, hm₂, s₂₁, s₂₂, hsp₂, hr₂₁, hr₂₂⟩
      rw [Rel_satisfy] at hr₁₁ hr₂₁
      rcases hr₁₁ with ⟨_, hn₁₁, hs₁₁⟩
      rcases hr₂₁ with ⟨_, hn₂₁, hs₂₁⟩
      subst m₁; subst m₂
      have hx : a₁.1 :: a₁.2 = xs := by simpa [Iso.cons] using ha₁
      have hy : a₂.1 :: a₂.2 = xs := by simpa [Iso.cons] using ha₂
      have hhead : a₁.1 = a₂.1 := (List.cons.inj (hx.trans hy.symm)).1
      have htail : a₁.2 = a₂.2 := (List.cons.inj (hx.trans hy.symm)).2
      have hpre : s₁₁ = s₂₁ := by
        have hs₁₁' : s₁₁ = single a₁.1 := by simpa using hs₁₁
        have hs₂₁' : s₂₁ = single a₂.1 := by simpa using hs₂₁
        rw [hs₁₁', hs₂₁', hhead]
      have htail' : (⟨n₁ - 1, s₁₂⟩ : Sigma fun k => Bytes k) = ⟨n₂ - 1, s₂₂⟩ :=
        ih a₁.2 s₁₂ s₂₂ hr₁₂ (by simpa [htail] using hr₂₂)
      have hfst : n₁ - 1 = n₂ - 1 := by simpa using (congrArg Sigma.fst htail')
      have hn : n₁ = n₂ := by omega
      subst n₂
      have hb : s₁₂ = s₂₂ := by
        cases htail'
        rfl
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        rw [hsp₁, hsp₂]
        rw [hpre, hb]

/-- `iso` preserves functionality: a functional inner description yields a
functional iso-description (`i.unapply` being a total function makes the
pre-image unique). -/
theorem Functional_iso {α β : Type} (i : Iso α β) (d : Codec α) (hd : Functional d) :
    Functional (Codec.iso i d) := by
  intro b n₁ n₂ s₁ s₂ h₁ h₂
  rw [Rel_iso] at h₁ h₂
  rcases h₁ with ⟨a₁, ha₁, hr₁⟩
  rcases h₂ with ⟨a₂, ha₂, hr₂⟩
  have hu₁ : i.unapply b = some a₁ := (i.law a₁ b).1 ha₁
  have hu₂ : i.unapply b = some a₂ := (i.law a₂ b).1 ha₂
  have ha : a₁ = a₂ := Option.some.inj (hu₁.symm.trans hu₂)
  subst a₂
  exact hd a₁ s₁ s₂ hr₁ hr₂

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

/-- Every byte of a `count k (satisfy p)`-related string satisfies `p` (the
*backward* direction of the alphabet-only encoding property): if the relation
holds, each of the `k` bytes is a `p`-byte. This is the primitive the
canonical-encoding and rejection theorems descend through. -/
theorem Rel_count_satisfy_forall (p : UInt8 → Bool) (k : Nat) (xs : List UInt8)
    {n : Nat} (s : Bytes n) :
    Rel (count k (Codec.satisfy p)) xs s → ∀ i : Fin n, p (s i) = true := by
  intro h
  induction k generalizing xs n s with
  | zero =>
      rw [Rel_count_zero] at h
      rcases h with ⟨_, hn⟩
      subst n
      intro i
      exact Fin.elim0 i
  | succ k ih =>
      rw [count, Rel_iso] at h
      rcases h with ⟨a, ha, hseq⟩
      rw [Rel_seq] at hseq
      rcases hseq with ⟨m, hm, s₁, s₂, hs, hr₁, hr₂⟩
      rw [Rel_satisfy] at hr₁
      rcases hr₁ with ⟨hp1, hn1, hs1⟩
      subst m
      intro i
      have hs1' : s₁ = single a.1 := by simpa using hs1
      by_cases hi : i.val < 1
      · have hle : i.val = 0 := by omega
        have hbv : s ⟨i.val, i.isLt⟩ = a.1 := by
          rw [hs]
          rw [splice_prefix_read (by omega : 1 ≤ n) s₁ s₂ ⟨i.val, i.isLt⟩ (by omega)]
          rw [hs1']
          rfl
        rw [hbv]
        exact hp1
      · have hbv : s ⟨i.val, i.isLt⟩ = s₂ ⟨i.val - 1, by omega⟩ := by
          rw [hs]
          rw [splice_apply]
          unfold concat
          rw [cast_fin_symm]
          · dsimp
            simp [hi]
          · omega
        rw [hbv]
        exact ih a.2 s₂ hr₂ ⟨i.val - 1, by omega⟩

/-- `Rel (count k (satisfy p)) xs s` forces `xs.length = k` (the mirror of
`Rel_count_satisfy_len`, which pins the byte length `n = k`). Together they give
`n = xs.length`, the fact the content-extraction lemma needs for `List` indexing. -/
theorem Rel_count_satisfy_length (p : UInt8 → Bool) (k : Nat) (xs : List UInt8)
    {n : Nat} (s : Bytes n) :
    Rel (count k (Codec.satisfy p)) xs s → xs.length = k := by
  intro h
  induction k generalizing xs n s with
  | zero =>
      rw [Rel_count_zero] at h
      rcases h with ⟨hxs, _⟩
      rw [hxs]
      rfl
  | succ k ih =>
      rw [count] at h
      rw [Rel_iso] at h
      rcases h with ⟨a, ha, hseq⟩
      have hxssplit : a.1 :: a.2 = xs := by
        unfold Iso.cons at ha
        cases ha
        rfl
      rw [Rel_seq] at hseq
      rcases hseq with ⟨m, _hm, s₁, s₂, _hs, _hr₁, hr₂⟩
      rw [← hxssplit]
      simp
      exact ih a.2 s₂ hr₂

/-- **Content extraction**: `Rel (count k (satisfy p)) xs s` pins `s` to the byte image
of `xs` exactly (`List.ofFn s = xs`). The `Rel_count_satisfy_forall` predicate form
only gives `p (s i) = true`; this sharper form recovers the actual bytes, which is
what the padded-base block/tail split needs to separate a full-block run from a
terminal tail at the pad boundary. `[propext, Quot.sound]`-only. -/
theorem Rel_count_satisfy_ofFn (p : UInt8 → Bool) (k : Nat) (xs : List UInt8)
    {n : Nat} (s : Bytes n)
    (h : Rel (count k (Codec.satisfy p)) xs s) :
    List.ofFn s = xs := by
  induction k generalizing xs n s with
  | zero =>
      rw [Rel_count_zero] at h
      rcases h with ⟨hxs, hn⟩
      subst xs
      subst n
      simp
  | succ k ih =>
      rw [count] at h
      rw [Rel_iso] at h
      rcases h with ⟨a, ha, hseq⟩
      have hxssplit : a.1 :: a.2 = xs := by
        unfold Iso.cons at ha
        cases ha
        rfl
      rw [Rel_seq] at hseq
      rcases hseq with ⟨m, hm, s₁, s₂, hs, hr₁, hr₂⟩
      rw [Rel_satisfy] at hr₁
      rcases hr₁ with ⟨_hp, hn1, hs1⟩
      cases hn1
      have hs1' : s₁ = single a.1 := by simpa using hs1
      have htail : List.ofFn s₂ = a.2 := ih a.2 s₂ hr₂
      rw [← hxssplit]
      rw [hs]
      change List.ofFn (splice hm s₁ s₂) = a.1 :: a.2
      rw [← htail]
      rw [hs1']
      change List.ofFn (splice hm (single a.1) s₂) = a.1 :: List.ofFn s₂
      apply List.ext_getElem?
      intro i
      simp only [List.getElem?_ofFn]
      by_cases hi : i < n
      · simp [hi]
        by_cases h1 : i < 1
        · have hb : (splice hm (single a.1) s₂) ⟨i, hi⟩ = a.1 := by
            rw [splice_prefix_read hm (single a.1) s₂ ⟨i, hi⟩ (by omega)]
            rfl
          have iz : i = 0 := by omega
          subst i
          simp
          exact hb
        · have hb : (splice hm (single a.1) s₂) ⟨i, hi⟩ = s₂ ⟨i - 1, by omega⟩ := by
            rw [splice_apply]
            unfold concat
            rw [cast_fin_symm]
            · dsimp
              simp [show ¬ i < 1 by omega]
            · omega
          rw [hb]
          rw [List.getElem?_cons]
          have hne : i ≠ 0 := by omega
          simp [hne, show i - 1 < n - 1 by omega]
      · simp [hi]
        omega
theorem relRepeat_forall {α : Type} {R : α → {m : Nat} → Bytes m → Prop}
    (p : UInt8 → Bool)
    (hstep : ∀ x {m : Nat} (s : Bytes m), R x s → ∀ i : Fin m, p (s i) = true) :
    ∀ (xs : List α) (n : Nat) (s : Bytes n),
      relRepeat R xs n s → ∀ i : Fin n, p (s i) = true := by
  intro xs
  induction xs with
  | nil =>
      intro n s h i
      rw [relRepeat_nil] at h
      subst n
      exact Fin.elim0 i
  | cons x rest ih =>
      intro n s h i
      rw [relRepeat_cons] at h
      rcases h with ⟨m, hm, s₁, s₂, hs, hx, hr⟩
      by_cases hi : i.val < m
      · have hbv : s i = s₁ ⟨i.val, hi⟩ := by
          rw [hs]
          exact splice_prefix_read hm s₁ s₂ i hi
        rw [hbv]
        exact hstep x s₁ hx ⟨i.val, hi⟩
      · have hbv : s i = s₂ ⟨i.val - m, by omega⟩ := by
          rw [hs]
          rw [splice_apply]
          unfold concat
          rw [cast_fin_symm]
          · dsimp
            simp [hi]
          · omega
        rw [hbv]
        exact ih (n - m) s₂ hr ⟨i.val - m, by omega⟩

/-- `relRepeat` is functional when its step relation is (`relFunctional R`): a list
value relates to at most one length+bytes pair. This is the repeat-level mirror of
`relFunctional`, and it is the single lemma the converse theorems (decode→encode)
close with (together with `encodeRepeat_ne_none`/`encodeRepeat_rel`). -/
theorem relRepeat_functional {α : Type} {R : α → {m : Nat} → Bytes m → Prop} (hR : relFunctional R) :
    ∀ (xs : List α) {n₁ n₂ : Nat} (s₁ : Bytes n₁) (s₂ : Bytes n₂),
      relRepeat R xs n₁ s₁ → relRepeat R xs n₂ s₂ → (⟨n₁, s₁⟩ : Sigma fun k => Bytes k) = ⟨n₂, s₂⟩ := by
  intro xs
  induction xs with
  | nil =>
      intro n₁ n₂ s₁ s₂ h₁ h₂
      rw [relRepeat_nil] at h₁ h₂
      subst n₁; subst n₂
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Bytes.ext; intro i; exact Fin.elim0 i
  | cons x rest ih =>
      intro n₁ n₂ s₁ s₂ h₁ h₂
      rw [relRepeat_cons] at h₁ h₂
      rcases h₁ with ⟨m₁, hm₁, s₁₁, s₁₂, hs₁, hx₁, hr₁⟩
      rcases h₂ with ⟨m₂, hm₂, s₂₁, s₂₂, hs₂, hx₂, hr₂⟩
      have hp : (⟨m₁, s₁₁⟩ : Sigma fun k => Bytes k) = ⟨m₂, s₂₁⟩ := hR x s₁₁ s₂₁ hx₁ hx₂
      cases hp
      have hfull := ih s₁₂ s₂₂ hr₁ hr₂
      have hl : n₁ - m₁ = n₂ - m₁ := congrArg (Sigma.fst (β := fun k => Bytes k)) hfull
      have hn : n₁ = n₂ := by omega
      subst n₂
      have hb : s₁₂ = s₂₂ := by
        cases hfull
        rfl
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        rw [hs₁, hs₂]
        rw [hb]

/-- Encoder completeness for repetition: if `relRepeat (Rel p) xs n s` and `Rel p` is
functional, then `encodeRepeat p xs = some ⟨n, s⟩`. This is the repetition mirror of
`encode_of_decode` (the decode→encode converse), and it is what the per-base
converse theorems (`decodeFull … = some v → encode{X} v = some ⟨n, s⟩`) reduce to. -/
theorem encodeRepeat_of_rel {α : Type} (p : Codec α) (hR : relFunctional (Rel p)) :
    ∀ (xs : List α) {n : Nat} (s : Bytes n), relRepeat (Rel p) xs n s → encodeRepeat p xs = some ⟨n, s⟩ := by
  intro xs n s hrel
  have hne : encodeRepeat p xs ≠ none := encodeRepeat_ne_none p xs s hrel
  cases he : encodeRepeat p xs with
  | none => exact False.elim (hne he)
  | some e =>
      rcases e with ⟨n', s'⟩
      have hrel' : relRepeat (Rel p) xs n' s' := encodeRepeat_rel p xs he
      have hpin : (⟨n, s⟩ : Sigma fun k => Bytes k) = ⟨n', s'⟩ := relRepeat_functional hR xs s s' hrel hrel'
      cases hpin
      rfl

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
      have hs₁x' : s₁x = single ax.1 := by simpa using hs₁x
      have hs₁y' : s₁y = single ay.1 := by simpa using hs₁y
      rw [Iso.cons] at hax hay
      dsimp at hax hay
      have hax' : ax.1 :: ax.2 = xs := Option.some.inj hax
      have hay' : ay.1 :: ay.2 = ys := Option.some.inj hay
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
      have htailEq : s₂x = s₂y := by
        rw [← bdrop_splice hmx s₁x s₂x, ← bdrop_splice hmy s₁y s₂y]
        congr 1
        rw [← hsx]
        rw [hsy]
      have htail : ax.2 = ay.2 := by
        exact ih s₂x hr₂x (by simpa [htailEq] using hr₂y)
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

/-- The generic `ConsumesByte` witness for a fixed-width `count (k+1) (satisfy p)`
leaf: productivity follows from the generic productivity lemmas (each step consumes
`k+1 ≥ 1` bytes, so a `count 0` leaf — which would match the empty string — is
correctly excluded). -/
theorem consumesByte_count_satisfy_succ (p : UInt8 → Bool) (k : Nat) :
    ConsumesByte (count (k + 1) (Codec.satisfy p)) := by
  rw [← productive_iff_consumesByte (count (k + 1) (Codec.satisfy p))]
  exact Productive_count_satisfy_succ p k

/-! ## The first-class run value (`Run`)

`many` is a *derived* combinator (the paper §3.4 derives `many p = nil $ pure ()
| cons $ p ∗ many p`; F\* has no `many`, just `satisfy_many0`), realized by the
already-proved `relRepeat`/`decodeRepeat`/`encodeRepeat` triple.  A concrete
format surfaces unbounded repetition as a **first-class `Run` value** — a
`structure` bundling the element description and its productivity witness, with
the three interpretations *inherited* (never re-defined) — so a consumer holds
one value and calls one `decode`/`encode`, never names a bespoke per-format
function.

`Run` is polymorphic in the element value type `α`: the fixed-width bases
(2/4/8/10/16) have `α = UInt8` (one byte per element, a `Codec UInt8`); the
cross-byte bit-packing bases (32/64) have `α = List UInt8` (a whole block per
element, a `Codec (List UInt8)`).  The value of a `Run α` is `List α`, and the
facade normalizes it to the uniform `List UInt8` value type (for the padded
bases via a terminal-tail `B32`/`B64` transport). -/
structure Run (α : Type) where
  /-- The element (or block) description. -/
  elem : Codec α
  /-- The productivity witness: every element step consumes ≥ 1 byte, which is
  the guard under which `decodeRepeat` is total. -/
  step : ConsumesByte elem

namespace Run

/-- The inherited whole-input decoder: `decodeRepeat elem step` with
full-consumption. Yields `Option (List α)` over a `Bytes n`. -/
def decodeFull (r : Run α) {n : Nat} (s : Bytes n) : Option (List α) :=
  Codec.decodeFull r.elem r.step n s

/-- The inherited repetition decoder (all prefixes, for a `Bytes n`). -/
def decode (r : Run α) {n : Nat} (s : Bytes n) : List (List α × Suffix n) :=
  decodeRepeat r.elem r.step n s

/-- The inherited encoder: `encodeRepeat elem`. Yields the concatenated
length-indexed bytes. -/
def encode (r : Run α) (xs : List α) : Option (Sigma fun n => Bytes n) :=
  encodeRepeat r.elem xs

/-- The inherited least-fixpoint relation: `relRepeat (Rel elem)`. -/
def rel (r : Run α) : List α → (n : Nat) → Bytes n → Prop :=
  relRepeat (Rel r.elem)

end Run

/-! ## The prefix-transport lemma (full-block run + terminal tail)

The whole-input roundtrip of the padded bases (32/64) composes the *full-block
run* (an unbounded `decodeRepeat` over the non-padded block element) with the
*terminal tail* (a bounded `decodeFull` over the padded tail element).  The one
new transport fact that composition needs: a full-consumption decode of a prefix
`sb : Bytes m₁` (`(xs, Suffix.empty m₁) ∈ decodeRepeat p h m₁ sb`) lifts to a
prefix-match over the larger `concat sb st` — the same `xs` decode now leaves the
suffix `st` (`Suffix.drop m₁ (concat sb st)`).  `[propext, Quot.sound]`-only. -/

/-- Dropping the first `m₁` bytes of a `concat` recovers the second component. -/
theorem bdrop_concat {m₁ m₂ : Nat} (sb : Bytes m₁) (st : Bytes m₂) :
    bdrop m₁ (concat sb st) = cast (congrArg Bytes (Nat.add_sub_cancel_left m₁ m₂).symm) st := by
  apply Bytes.ext
  intro i
  rw [cast_bytes_val' (e := (Nat.add_sub_cancel_left m₁ m₂).symm)]
  dsimp [bdrop, concat]
  have hnot : ¬ i.val + m₁ < m₁ := by omega
  simp [hnot]

/-- `concat sb st` re-assembles from its own `Suffix.drop m₁` and the original prefix. -/
theorem concat_eq_drop_prepend {m₁ m₂ : Nat} (sb : Bytes m₁) (st : Bytes m₂) :
    concat sb st =
      (Suffix.drop m₁ (concat sb st)).prepend
        (cast (congrArg Bytes (show m₁ = (m₁ + m₂) - (Suffix.drop m₁ (concat sb st)).remaining by
          dsimp [Suffix.drop]
          exact (Nat.sub_sub_self (Nat.le.intro rfl : m₁ ≤ m₁ + m₂)).symm)) sb) := by
  apply Bytes.ext
  intro i
  rw [prepend_apply]
  dsimp [Suffix.drop]
  rw [bdrop_concat sb st]
  dsimp [concat]
  rw [cast_fin_symm]
  · by_cases hi : i.val < m₁ <;> simp [hi]
  · omega

/-- The prefix-transport lemma: a full-consumption `decodeRepeat` of a prefix lifts
to a prefix-match over the concatenation (the freshly consumed suffix is `st`). -/
theorem decodeRepeat_prefix_concat {α : Type} (p : Codec α) (h : ConsumesByte p) :
    ∀ (xs : List α) {m₁ m₂ : Nat} (sb : Bytes m₁) (st : Bytes m₂),
      (xs, Suffix.empty m₁) ∈ decodeRepeat p h m₁ sb →
      (xs, Suffix.drop m₁ (concat sb st)) ∈ decodeRepeat p h (m₁ + m₂) (concat sb st) := by
  intro xs m₁ m₂ sb st hmem
  rcases (decodeRepeat_spec p h xs m₁ sb (Suffix.empty m₁)).1 hmem with ⟨s₀, hsb, hrel⟩
  let srel : Bytes ((m₁ + m₂) - (Suffix.drop m₁ (concat sb st)).remaining) :=
    cast (congrArg Bytes (show m₁ = (m₁ + m₂) - (Suffix.drop m₁ (concat sb st)).remaining by
      dsimp [Suffix.drop]
      exact (Nat.sub_sub_self (Nat.le.intro rfl : m₁ ≤ m₁ + m₂)).symm)) sb
  refine (decodeRepeat_spec p h xs (m₁ + m₂) (concat sb st) (Suffix.drop m₁ (concat sb st))).2 ?_
  refine ⟨srel, ?_, ?_⟩
  · simpa [srel] using (concat_eq_drop_prepend sb st)
  · have hidx : (m₁ + m₂) - (Suffix.drop m₁ (concat sb st)).remaining = m₁ := by
      dsimp [Suffix.drop]
      exact Nat.sub_sub_self (Nat.le.intro rfl : m₁ ≤ m₁ + m₂)
    have hsb' : sb = s₀ := by
      rw [hsb]
      apply Bytes.ext
      intro i
      simp [Suffix.prepend, Suffix.empty, splice, concat]
    have hsrel : srel = cast (congrArg Bytes hidx.symm) s₀ := by
      dsimp [srel]
      rw [hsb']
    rw [hsrel]
    exact (relRepeat_cast (Rel p) xs hidx.symm s₀).2 hrel

end BaseN.Common
