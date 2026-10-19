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

end BaseN.Common
