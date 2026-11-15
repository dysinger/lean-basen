/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import BaseN.Radix
import BaseN.RadixAlphabets

/-!
# BaseN.RadixCodec — the numeral `Iso` over the quotient

`BaseN.Radix` gives the radix-generic arithmetic: `digitVal`, `toNat`, `ofNat`, and
the round-trip pair. This module turns that pair into the object the `basen` spec
names — **a bijection between `Nat` and the radix's numerals modulo information-free
variation** — and supplies the normaliser that carries a lax spelling into it.

## Why the codomain is a quotient, not raw syntax

`Codec.Iso.law` is `apply a = some b ↔ unapply b = some a`. Stated over raw
`List UInt8`, `"007"` and `"7"` are two distinct left-hand values that must both map
to the number `7`; `unapply 7` cannot be `some` of both, so the `→` direction is
**false** — not unproved, and not fixable by reordering a proof. The equivalence has
to live in the codomain, which is `Codec.Normal (List UInt8) (trimFor b)`: `codec`'s
`Normal` layer reifies the quotient as the fixed points of the normaliser, and
`Codec.fill_surj` is what makes that reification faithful rather than merely a subset.

So `numeralIso b _ : Iso Nat (Normal (List UInt8) (trimFor b))` and its law holds
**unconditionally on the quotient**, with no hypothesis about spelling. A *spelling*
reaches a number through `trimFor` first; `trimFor`'s totality and idempotence are a
separate obligation (`trimFor_canonical`), not a hypothesis on the `Iso`.

## What `trimFor` absorbs, and what it rejects

| variation                            | absorbed?         | reason                                    |
| ------------------------------------ | ----------------- | ----------------------------------------- |
| leading blanks (`"  7"`)             | **yes**           | the stated reading policy, generalised    |
| leading zero digits (`"007"`)        | **yes**           | changes no value                          |
| trailing blank (`"7 "`)              | **no** — rejected | a trailing blank is not part of a numeral |
| wrong-alphabet digit (`"9"` radix 8) | **no** — rejected | would change or destroy the value         |
| trailing data (`"7x"`)               | **no** — rejected |                                           |
| radix prefix (`"0x10"`)              | **no** — rejected | a prefix names a *radix*, not padding     |

The prefix row is deliberate: the radix here is a **parameter**, so a C-family reading
in which a leading zero changes the radix (`017` is octal) does not apply. A caller
that wants prefix-driven radix selection does that *before* calling in.

Zero is the radix's **single zero digit**, never the empty sequence. `toNat b []` is
`some 0` only as a by-product of the fold's base case; no theorem here claims the
empty sequence is a numeral, and `trimFor` rejects it.

## Shape

`trimFor` follows `Codec.Normalizer`'s pattern — one total map, proved idempotent on
its image, feeding `Codec.fill` — which is the shape `basen-uppercase-prepass`'s
`upperNormalizer` uses for case folding. The two differ only in *what they absorb*,
which is precisely the variation `Codec.Normal` exists to abstract over; that is why
this is one mechanism and not a second one.

`trimFor` is `Option`-valued rather than a total endofunction, and the reason is
stated rather than glossed: `"7x"` names no number, so collapsing it to some list
would make `fill` a bijection onto a quotient of strings most of which denote
nothing. On the accepting subtype (`isNumeral`) `trimFor` is a total endofunction
into the canonical forms, and *that* is what the `Iso` needs.

## Why `numeralIso` does **not** go through the padded bases' tail spine

A future implementer reaching for `BaseN.Base64.b64BlockIso` here should stop and read
this. The padded bases (32 and 64) split their encoding into a **full-block layer** plus a
**terminal-tail layer** whose `=` padding encodes a *length class* — 0, 1 or 2 bytes in the
last group. A minimal-width numeral has no such thing: `ofNat 64 7` is one digit, not a
digit plus a length announcement, and `numeralIso`'s codomain is the numeral quotient, so
composing through the tail spine would attribute a length class to a value that does not
carry one.

So `numeralIso` is built on `digitVal`/`toNat`/`ofNat` and `trimFor` alone, and this
module never imports or mentions `b32TailIso` / `b64TailIso`. The block isos **are** tied
to the fold, but in `BaseN.RadixTie` and over the **block layer only**
(`b32BlockApply`/`b64BlockApply`), which is where the tie is true. Reading a padded
encoding as a number is out of scope and no theorem here claims it — the spec states the
same thing as a requirement, so the boundary is enforced rather than remembered.

## Relationship to `BaseN.RadixAlphabets`

`isZeroDigit` compares against `byteOfDigit b 0`, the same alphabet `digitVal` reads,
so the normaliser and the fold share one alphabet source rather than two that must be
kept in agreement. `isDigits` is defined through `digitVal` itself, so "is this byte a
digit" and "what is its value" cannot drift apart.

Every law in this module is `[propext, Quot.sound]`-only.
-/

namespace BaseN.RadixCodec

open BaseN.Radix
open Codec

/-! ## The blank and zero-digit predicates

Only the ASCII space is a blank. `\t`/`\n` are **not** absorbed: a numeral in a framed
format does not carry them, and admitting them would widen the accepted set past what
the block layer accepts — the "accepts anything" failure the spec forbids. -/

/-- `isBlank c` — `c` is the ASCII space. -/
def isBlank (c : UInt8) : Bool := decide (c.toNat = 32)

theorem isBlank_eq_true_iff {c : UInt8} : isBlank c = true ↔ c.toNat = 32 :=
  decide_eq_true_iff

/-- `isZeroDigit b c` — `c` is the radix's zero digit.

Defined through `byteOfDigit` — the same alphabet `digitVal` reads — so the
normaliser and the fold share one alphabet source. Measured at all seven radices,
`byteOfDigit b 0` is `'0'` (ASCII 48) and `digitVal b` accepts it, base 2's included
(`bitVal 48 = 0` at `Base2.lean:36`). `acceptsDigitZero` records the second half as a
`decide`, because the encoder/decoder sentinel asymmetry `Base2.valToBit`'s docstring
says is deliberate is exactly what could make the two disagree. -/
def isZeroDigit (b : Nat) (c : UInt8) : Bool := c.toNat == (byteOfDigit b 0).toNat

/-- The alphabet's zero byte is never a blank. -/
theorem byteOfDigit_zero_ne_blank_nat (b : Nat) : (byteOfDigit b 0).toNat ≠ 32 := by
  rw [byteOfDigit_toNat]
  unfold byteOfDigitNat
  by_cases h32 : b = 32
  · subst h32; rw [ite_eq_left rfl, ite_eq_left (by omega : (0:Nat) ≤ 25)]; omega
  · rw [ite_eq_right h32]
    by_cases h64 : b = 64
    · subst h64; rw [ite_eq_left rfl, ite_eq_left (by omega : (0:Nat) ≤ 25)]; omega
    · rw [ite_eq_right h64]
      by_cases h16 : b = 16
      · subst h16; rw [ite_eq_left rfl, ite_eq_left (by omega : (0:Nat) ≤ 9)]; omega
      · rw [ite_eq_right h16]; omega


theorem isZeroDigit_eq_true_iff {b : Nat} {c : UInt8} :
    isZeroDigit b c = true ↔ c.toNat = (byteOfDigit b 0).toNat :=
  beq_iff_eq

/-- The radix's digit zero is itself a digit of the radix's decoder alphabet. -/
def acceptsDigitZero (b : Nat) : Bool := (digitVal b (byteOfDigit b 0)).isSome

theorem acceptsDigitZero_iff {b : Nat} :
    acceptsDigitZero b = true ↔ (digitVal b (byteOfDigit b 0)).isSome = true :=
  beq_iff_eq (a := (digitVal b (byteOfDigit b 0)).isSome) (b := true)

/-! ## The digit tail and the alphabet check -/

/-- `digitTail b zs` — `zs` with its leading zero digits removed. -/
def digitTail (b : Nat) : List UInt8 → List UInt8
  | [] => []
  | c :: cs => if isZeroDigit b c then digitTail b cs else c :: cs

/-- `isDigits b zs` — every byte of `zs` is a digit in radix `b`.

Defined through `digitVal`, so this predicate and `toNat` read one alphabet. -/
def isDigits (b : Nat) : List UInt8 → Bool
  | [] => true
  | c :: cs => (digitVal b c).isSome && isDigits b cs

theorem isDigits_cons {b : Nat} {c : UInt8} {cs : List UInt8} :
    isDigits b (c :: cs) = true ↔ (digitVal b c).isSome = true ∧ isDigits b cs = true := by
  -- the `match` does not reduce at a variable `cs`, so `show` the unfolded body first
  show ((digitVal b c).isSome && isDigits b cs) = true ↔ _
  exact Bool.and_eq_true_iff

theorem isDigits_iff {b : Nat} (zs : List UInt8) :
    isDigits b zs = true ↔ ∀ c ∈ zs, (digitVal b c).isSome = true := by
  induction zs with
  | nil => simp [isDigits]
  | cons c cs ih =>
      rw [isDigits_cons, ih]
      constructor
      · rintro ⟨h1, h2⟩ d hd
        rcases List.mem_cons.1 hd with rfl | hd
        · exact h1
        · exact h2 d hd
      · intro h
        exact ⟨h c (List.mem_cons_self ..), fun d hd => h d (List.mem_cons_of_mem _ hd)⟩

/-- A digit-list whose bytes are all in the alphabet converts. -/
theorem toNat_isSome_of_isDigits {b : Nat} :
    ∀ {zs : List UInt8}, isDigits b zs = true → (toNat b zs).isSome = true
  | [], _ => rfl
  | c :: cs, h => by
      rw [isDigits_cons] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h1
      have htl := toNat_isSome_of_isDigits h2
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 htl
      rw [toNat_cons_some b c cs v hv, ha]
      rfl

/-! ## The value↔byte bridge

`digitVal_byteOfDigit` (`BaseN.Radix`) says the **encoder's** byte is readable.
The `Iso`'s backward direction needs the converse: a byte the **fold** can read is
the encoder's byte for the value it reads. Together they say that `digitVal` and
`byteOfDigit` are inverse on the alphabet, which is what lets a digit *list* be
rewritten as `ds.map (byteOfDigit b)` and so let `natVal_inj_head` apply.

`digitVal_lt_of_some` is the range fact — a read value is below the radix — and it
is where the `isRadix` split earns its keep: each alphabet's windows are different,
so the bound is discharged radix by radix.

**Why this is a per-radix case split rather than one `simp`.** `digitVal`'s
`if`-chain does not reduce at a variable radix (`split`/`simp` stall on the
`radix = 2` test), and `UInt8.ofNat` appears throughout in `byteOfDigit`, so every
window fact would need a `% 256`. The route that closes is: restate the arm's
`if`-chain as one `hbody` equation, case each window with `ite_eq_left`/`ite_eq_right`,
and finish with `UInt8.toNat.inj` plus `byteOfDigit_toNat_eq` (in-range, so no
modulus). `(0x30 : UInt8).toNat = 48` is a `decide`, which is what
`digitVal_blank` used, and it is not needed here.
-/

theorem digitVal_lt_of_some {b : Nat} (hr : IsRadix b) {c : UInt8} {v : Nat}
    (h : digitVal b c = some v) : v < b := by
  cases hr with
  | b2 =>
      unfold digitVal at h
      simp only [ite_true] at h
      by_cases hw : inWin 48 49 c.toNat = true
      · rw [ite_eq_left hw] at h
        have hv : v = c.toNat - 48 := (Option.some.inj h).symm
        have := inWin_eq_true hw
        omega
      · rw [ite_eq_right hw] at h; exact absurd h (by simp)
  | b4 =>
      unfold digitVal at h
      simp only [ite_true] at h
      by_cases hw : inWin 48 51 c.toNat = true
      · rw [ite_eq_left hw] at h
        have hv : v = c.toNat - 48 := (Option.some.inj h).symm
        have := inWin_eq_true hw
        omega
      · rw [ite_eq_right hw] at h; exact absurd h (by simp)
  | b8 =>
      unfold digitVal at h
      simp only [ite_true] at h
      by_cases hw : inWin 48 55 c.toNat = true
      · rw [ite_eq_left hw] at h
        have hv : v = c.toNat - 48 := (Option.some.inj h).symm
        have := inWin_eq_true hw
        omega
      · rw [ite_eq_right hw] at h; exact absurd h (by simp)
  | b10 =>
      unfold digitVal at h
      simp only [ite_true] at h
      by_cases hw : inWin 48 57 c.toNat = true
      · rw [ite_eq_left hw] at h
        have hv : v = c.toNat - 48 := (Option.some.inj h).symm
        have := inWin_eq_true hw
        omega
      · rw [ite_eq_right hw] at h; exact absurd h (by simp)
  | b16 =>
      have hbody : digitVal 16 c =
          (if inWin 48 57 c.toNat then some (c.toNat - 48)
           else if inWin 65 70 c.toNat then some (c.toNat - 55) else none) := by
        unfold digitVal; simp
      rw [hbody] at h
      by_cases h1 : inWin 48 57 c.toNat = true
      · rw [ite_eq_left h1] at h
        have hv : v = c.toNat - 48 := (Option.some.inj h).symm
        have := inWin_eq_true h1
        omega
      · rw [ite_eq_right h1] at h
        by_cases h2 : inWin 65 70 c.toNat = true
        · rw [ite_eq_left h2] at h
          have hv : v = c.toNat - 55 := (Option.some.inj h).symm
          have := inWin_eq_true h2
          omega
        · rw [ite_eq_right h2] at h; exact absurd h (by simp)
  | b32 =>
      have hbody : digitVal 32 c =
          (if inWin 65 90 c.toNat then some (c.toNat - 65)
           else if inWin 50 55 c.toNat then some (c.toNat - 50 + 26) else none) := by
        unfold digitVal; simp
      rw [hbody] at h
      by_cases h1 : inWin 65 90 c.toNat = true
      · rw [ite_eq_left h1] at h
        have hv : v = c.toNat - 65 := (Option.some.inj h).symm
        have := inWin_eq_true h1
        omega
      · rw [ite_eq_right h1] at h
        by_cases h2 : inWin 50 55 c.toNat = true
        · rw [ite_eq_left h2] at h
          have hv : v = c.toNat - 50 + 26 := (Option.some.inj h).symm
          have := inWin_eq_true h2
          omega
        · rw [ite_eq_right h2] at h; exact absurd h (by simp)
  | b64 =>
      have hbody : digitVal 64 c =
          (if inWin 65 90 c.toNat then some (c.toNat - 65)
           else if inWin 97 122 c.toNat then some (c.toNat - 97 + 26)
           else if inWin 48 57 c.toNat then some (c.toNat - 48 + 52)
           else if c.toNat = 43 then some 62
           else if c.toNat = 47 then some 63 else none) := by
        unfold digitVal; simp
      rw [hbody] at h
      by_cases h1 : inWin 65 90 c.toNat = true
      · rw [ite_eq_left h1] at h
        have hv : v = c.toNat - 65 := (Option.some.inj h).symm
        have := inWin_eq_true h1
        omega
      · rw [ite_eq_right h1] at h
        by_cases h2 : inWin 97 122 c.toNat = true
        · rw [ite_eq_left h2] at h
          have hv : v = c.toNat - 97 + 26 := (Option.some.inj h).symm
          have := inWin_eq_true h2
          omega
        · rw [ite_eq_right h2] at h
          by_cases h3 : inWin 48 57 c.toNat = true
          · rw [ite_eq_left h3] at h
            have hv : v = c.toNat - 48 + 52 := (Option.some.inj h).symm
            have := inWin_eq_true h3
            omega
          · rw [ite_eq_right h3] at h
            by_cases h4 : c.toNat = 43
            · rw [ite_eq_left h4] at h
              have hv : v = 62 := (Option.some.inj h).symm
              omega
            · rw [ite_eq_right h4] at h
              by_cases h5 : c.toNat = 47
              · rw [ite_eq_left h5] at h
                have hv : v = 63 := (Option.some.inj h).symm
                omega
              · rw [ite_eq_right h5] at h; exact absurd h (by simp)



theorem byteOfDigitNat_nonPow (r d : Nat) (h32 : r ≠ 32) (h64 : r ≠ 64) (h16 : r ≠ 16) :
    byteOfDigitNat r d = 48 + d := by
  rw [byteOfDigitNat_eq, ite_eq_right h32, ite_eq_right h64, ite_eq_right h16]

theorem byteOfDigitNat_32 (d : Nat) :
    byteOfDigitNat 32 d = (if d ≤ 25 then 65 + d else 50 + d - 26) := by
  rw [byteOfDigitNat_eq]; simp

theorem byteOfDigitNat_64 (d : Nat) :
    byteOfDigitNat 64 d =
      (if d ≤ 25 then 65 + d
       else if d ≤ 51 then 97 + d - 26
       else if d ≤ 61 then 48 + d - 52
       else if d = 62 then 43 else 47) := by
  rw [byteOfDigitNat_eq]; simp

theorem byteOfDigitNat_16 (d : Nat) :
    byteOfDigitNat 16 d = (if d ≤ 9 then 48 + d else 55 + d) := by
  rw [byteOfDigitNat_eq]; simp

/-- A `48 + d` window arm: `digitVal r c = some v` forces `c.toNat = 48 + v`. -/
theorem bridge_48 (r lo hi : Nat) (c : UInt8) (v : Nat)
    (hbody : digitVal r c = (if inWin lo hi c.toNat then some (c.toNat - lo) else none))
    (h : digitVal r c = some v) (hlo : lo = 48) :
    c.toNat = 48 + v := by
  subst hlo
  rw [hbody] at h
  by_cases hw : inWin 48 hi c.toNat = true
  · rw [ite_eq_left hw] at h
    have hv : v = c.toNat - 48 := (Option.some.inj h).symm
    subst hv
    have := (inWin_eq_true hw).1
    omega
  · rw [ite_eq_right hw] at h
    exact absurd h (by simp)

theorem bridge_2 (c : UInt8) (v : Nat) (h : digitVal 2 c = some v) :
    c.toNat = byteOfDigitNat 2 v := by
  have := bridge_48 2 48 49 c v (by unfold digitVal; simp) h rfl
  rw [this, byteOfDigitNat_nonPow 2 v (by decide) (by decide) (by decide)]

theorem bridge_4 (c : UInt8) (v : Nat) (h : digitVal 4 c = some v) :
    c.toNat = byteOfDigitNat 4 v := by
  have := bridge_48 4 48 51 c v (by unfold digitVal; simp) h rfl
  rw [this, byteOfDigitNat_nonPow 4 v (by decide) (by decide) (by decide)]

theorem bridge_8 (c : UInt8) (v : Nat) (h : digitVal 8 c = some v) :
    c.toNat = byteOfDigitNat 8 v := by
  have := bridge_48 8 48 55 c v (by unfold digitVal; simp) h rfl
  rw [this, byteOfDigitNat_nonPow 8 v (by decide) (by decide) (by decide)]

theorem bridge_10 (c : UInt8) (v : Nat) (h : digitVal 10 c = some v) :
    c.toNat = byteOfDigitNat 10 v := by
  have := bridge_48 10 48 57 c v (by unfold digitVal; simp) h rfl
  rw [this, byteOfDigitNat_nonPow 10 v (by decide) (by decide) (by decide)]

/-- radix 16: two windows, `48 + d` then `55 + d`. -/
theorem bridge_16 (c : UInt8) (v : Nat) (h : digitVal 16 c = some v) :
    c.toNat = byteOfDigitNat 16 v := by
  have hbody : digitVal 16 c =
      (if inWin 48 57 c.toNat then some (c.toNat - 48)
       else if inWin 65 70 c.toNat then some (c.toNat - 55) else none) := by
    unfold digitVal; simp
  rw [hbody] at h
  by_cases h1 : inWin 48 57 c.toNat = true
  · rw [ite_eq_left h1] at h
    have hv : v = c.toNat - 48 := (Option.some.inj h).symm
    subst hv
    have hw := inWin_eq_true h1
    rw [byteOfDigitNat_16]
    by_cases hd : c.toNat - 48 ≤ 9
    · rw [ite_eq_left hd]; omega
    · rw [ite_eq_right hd]; omega
  · rw [ite_eq_right h1] at h
    by_cases h2 : inWin 65 70 c.toNat = true
    · rw [ite_eq_left h2] at h
      have hv : v = c.toNat - 55 := (Option.some.inj h).symm
      subst hv
      have hw := inWin_eq_true h2
      rw [byteOfDigitNat_16]
      by_cases hd : c.toNat - 55 ≤ 9
      · rw [ite_eq_left hd]; omega
      · rw [ite_eq_right hd]; omega
    · rw [ite_eq_right h2] at h
      exact absurd h (by simp)

/-- radix 32: `A-Z` then `2-7`. -/
theorem bridge_32 (c : UInt8) (v : Nat) (h : digitVal 32 c = some v) :
    c.toNat = byteOfDigitNat 32 v := by
  have hbody : digitVal 32 c =
      (if inWin 65 90 c.toNat then some (c.toNat - 65)
       else if inWin 50 55 c.toNat then some (c.toNat - 50 + 26) else none) := by
    unfold digitVal; simp
  rw [hbody] at h
  by_cases h1 : inWin 65 90 c.toNat = true
  · rw [ite_eq_left h1] at h
    have hv : v = c.toNat - 65 := (Option.some.inj h).symm
    subst hv
    have hw := inWin_eq_true h1
    rw [byteOfDigitNat_32]
    by_cases hd : c.toNat - 65 ≤ 25
    · rw [ite_eq_left hd]; omega
    · rw [ite_eq_right hd]; omega
  · rw [ite_eq_right h1] at h
    by_cases h2 : inWin 50 55 c.toNat = true
    · rw [ite_eq_left h2] at h
      have hv : v = c.toNat - 50 + 26 := (Option.some.inj h).symm
      subst hv
      have hw := inWin_eq_true h2
      rw [byteOfDigitNat_32]
      by_cases hd : c.toNat - 50 + 26 ≤ 25
      · rw [ite_eq_left hd]; omega
      · rw [ite_eq_right hd]; omega
    · rw [ite_eq_right h2] at h
      exact absurd h (by simp)

/-- radix 64: `A-Z`, `a-z`, `0-9`, `+`, `/`. -/
theorem bridge_64 (c : UInt8) (v : Nat) (h : digitVal 64 c = some v) :
    c.toNat = byteOfDigitNat 64 v := by
  have hbody : digitVal 64 c =
      (if inWin 65 90 c.toNat then some (c.toNat - 65)
       else if inWin 97 122 c.toNat then some (c.toNat - 97 + 26)
       else if inWin 48 57 c.toNat then some (c.toNat - 48 + 52)
       else if c.toNat = 43 then some 62
       else if c.toNat = 47 then some 63 else none) := by
    unfold digitVal; simp
  rw [hbody] at h
  by_cases h1 : inWin 65 90 c.toNat = true
  · rw [ite_eq_left h1] at h
    have hv : v = c.toNat - 65 := (Option.some.inj h).symm
    subst hv
    have hw := inWin_eq_true h1
    rw [byteOfDigitNat_64]
    by_cases hd : c.toNat - 65 ≤ 25
    · rw [ite_eq_left hd]; omega
    · rw [ite_eq_right hd]
      by_cases hd2 : c.toNat - 65 ≤ 51
      · rw [ite_eq_left hd2]; omega
      · rw [ite_eq_right hd2]
        by_cases hd3 : c.toNat - 65 ≤ 61
        · rw [ite_eq_left hd3]; omega
        · rw [ite_eq_right hd3]
          by_cases hd4 : c.toNat - 65 = 62
          · rw [ite_eq_left hd4]; omega
          · rw [ite_eq_right hd4]; omega
  · rw [ite_eq_right h1] at h
    by_cases h2 : inWin 97 122 c.toNat = true
    · rw [ite_eq_left h2] at h
      have hv : v = c.toNat - 97 + 26 := (Option.some.inj h).symm
      subst hv
      have hw := inWin_eq_true h2
      rw [byteOfDigitNat_64]
      by_cases hd : c.toNat - 97 + 26 ≤ 25
      · rw [ite_eq_left hd]; omega
      · rw [ite_eq_right hd]
        by_cases hd2 : c.toNat - 97 + 26 ≤ 51
        · rw [ite_eq_left hd2]; omega
        · rw [ite_eq_right hd2]
          by_cases hd3 : c.toNat - 97 + 26 ≤ 61
          · rw [ite_eq_left hd3]; omega
          · rw [ite_eq_right hd3]
            by_cases hd4 : c.toNat - 97 + 26 = 62
            · rw [ite_eq_left hd4]; omega
            · rw [ite_eq_right hd4]; omega
    · rw [ite_eq_right h2] at h
      by_cases h3 : inWin 48 57 c.toNat = true
      · rw [ite_eq_left h3] at h
        have hv : v = c.toNat - 48 + 52 := (Option.some.inj h).symm
        subst hv
        have hw := inWin_eq_true h3
        rw [byteOfDigitNat_64]
        by_cases hd : c.toNat - 48 + 52 ≤ 25
        · rw [ite_eq_left hd]; omega
        · rw [ite_eq_right hd]
          by_cases hd2 : c.toNat - 48 + 52 ≤ 51
          · rw [ite_eq_left hd2]; omega
          · rw [ite_eq_right hd2]
            by_cases hd3 : c.toNat - 48 + 52 ≤ 61
            · rw [ite_eq_left hd3]; omega
            · rw [ite_eq_right hd3]
              by_cases hd4 : c.toNat - 48 + 52 = 62
              · rw [ite_eq_left hd4]; omega
              · rw [ite_eq_right hd4]; omega
      · rw [ite_eq_right h3] at h
        by_cases h4 : c.toNat = 43
        · rw [ite_eq_left h4] at h
          have hv : v = 62 := (Option.some.inj h).symm
          subst hv
          rw [byteOfDigitNat_64]
          simp
          omega
        · rw [ite_eq_right h4] at h
          by_cases h5 : c.toNat = 47
          · rw [ite_eq_left h5] at h
            have hv : v = 63 := (Option.some.inj h).symm
            subst hv
            rw [byteOfDigitNat_64]
            simp
            omega
          · rw [ite_eq_right h5] at h
            exact absurd h (by simp)


/-- **The value↔byte bridge**: a byte the fold can read names itself. -/
theorem digitVal_some_byteOfDigit {b : Nat} (hr : IsRadix b) {c : UInt8} {v : Nat}
    (h : digitVal b c = some v) : c = byteOfDigit b v := by
  have hv : v < b := digitVal_lt_of_some hr h
  apply UInt8.toNat.inj
  rw [byteOfDigit_toNat_eq b (isRadix_ge2 hr) (isRadix_le64 hr) v hv]
  cases hr with
  | b2  => exact bridge_2 c v h
  | b4  => exact bridge_4 c v h
  | b8  => exact bridge_8 c v h
  | b10 => exact bridge_10 c v h
  | b16 => exact bridge_16 c v h
  | b32 => exact bridge_32 c v h
  | b64 => exact bridge_64 c v h



/-! ## `trimFor` — the normaliser -/

/-- `strip b ds` — `ds` with its leading blanks and leading zero digits removed, in any
interleaving.

One pre-pass rather than two guards is what makes `trimFor` idempotent
**structurally**: `strip`'s output either is empty or begins with a byte that is
neither a blank nor a zero digit, so applying it again cannot change anything. -/
def strip (b : Nat) : List UInt8 → List UInt8
  | [] => []
  | c :: cs => if isBlank c = true ∨ isZeroDigit b c = true then strip b cs else c :: cs

theorem strip_cons {b : Nat} {c : UInt8} {cs : List UInt8}
    (h : ¬ (isBlank c = true ∨ isZeroDigit b c = true)) : strip b (c :: cs) = c :: cs := by
  show (if isBlank c = true ∨ isZeroDigit b c = true then strip b cs else c :: cs) = c :: cs
  rw [ite_eq_right h]

theorem strip_skip {b : Nat} {c : UInt8} {cs : List UInt8}
    (h : isBlank c = true ∨ isZeroDigit b c = true) : strip b (c :: cs) = strip b cs := by
  show (if isBlank c = true ∨ isZeroDigit b c = true then strip b cs else c :: cs) = strip b cs
  rw [ite_eq_left h]

/-- **`strip` is idempotent** — the structural fact the whole normaliser rests on. -/
theorem strip_idem (b : Nat) (l : List UInt8) : strip b (strip b l) = strip b l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
      by_cases h : isBlank c = true ∨ isZeroDigit b c = true
      · rw [strip_skip h]; exact ih
      · rw [strip_cons h]
        exact strip_cons (fun hh => h hh)

/-! ## The zero spelling

`trimFor`'s all-absorbed branch needs to know whether the input it just absorbed was a
*spelling of zero* or a spelling of nothing. `isDigits` is the wrong question: it asks
whether the raw bytes are a run of digits, and the blanks that `strip` absorbs are not
digits — which rejected `"  0"` while `"  7"` was accepted, because `7` is not the zero
digit. Measured 2026-11-15 at `9a02f89`, at every radix.

The right question has three conjuncts, and the shape of the predicate is what keeps them
apart: **leading blanks, then one or more zero digits, and nothing else.** The two ways a
predicate defined against `strip`'s output alone goes wrong are both measured:

- `strip` absorbs `"  0"` and `"0 "` **identically**, so a predicate over `strip`'s output
  cannot see that the second one's blank is *trailing* — which `design.md` D3 rejects.
  Hence the blanks and the zero digits are separated in the recursion, not conflated.
- Placing blanks and zero digits in one interleaving also accepts `"  "`, which names
  nothing (`design.md` D4). Hence `isZeroZeros` requires a **non-empty** run.

Because `isZeroSpelling b [] = false` by definition, D4's empty-input rule and this
predicate agree, and `trimFor` needs no separate `ds = []` test. -/

/-- `isZeroZeros b zs` — `zs` is a **non-empty** run of the radix's zero digit. -/
def isZeroZeros (b : Nat) : List UInt8 → Bool
  | [] => false
  | c :: cs => isZeroDigit b c && cs.all (fun x => isZeroDigit b x)

/-- `isZeroSpelling b ds` — leading blanks, then one or more zero digits, and nothing else.

`false` on `[]`, so a spelling of nothing is never a spelling of zero. -/
def isZeroSpelling (b : Nat) : List UInt8 → Bool
  | [] => false
  | c :: cs => if isBlank c = true then isZeroSpelling b cs else isZeroZeros b (c :: cs)

theorem isZeroSpelling_nil (b : Nat) : isZeroSpelling b [] = false := rfl

theorem isZeroSpelling_cons_blank {b : Nat} {c : UInt8} {cs : List UInt8}
    (hb : isBlank c = true) : isZeroSpelling b (c :: cs) = isZeroSpelling b cs := by
  show (if isBlank c = true then isZeroSpelling b cs else isZeroZeros b (c :: cs)) = _
  rw [ite_eq_left hb]

theorem isZeroSpelling_cons_zeros {b : Nat} {c : UInt8} {cs : List UInt8}
    (hb : isBlank c = false) : isZeroSpelling b (c :: cs) = isZeroZeros b (c :: cs) := by
  show (if isBlank c = true then isZeroSpelling b cs else isZeroZeros b (c :: cs)) = _
  rw [ite_eq_right (by simp [hb])]

theorem isZeroZeros_cons {b : Nat} {c : UInt8} {cs : List UInt8} :
    isZeroZeros b (c :: cs) = true ↔
      isZeroDigit b c = true ∧ ∀ x ∈ cs, isZeroDigit b x = true := by
  show (isZeroDigit b c && cs.all (fun x => isZeroDigit b x)) = true ↔ _
  rw [Bool.and_eq_true_iff, List.all_eq_true]

/-- A zero-digit run is a zero spelling: its head is a zero digit (never a blank) and the
rest is a run. The disjointness of blanks and zero digits is `byteOfDigit_zero_ne_blank_nat`
at the `UInt8` level, decided by the alphabet rather than assumed. -/
theorem isZeroZeros_spelling {b : Nat} {zs : List UInt8} (h : isZeroZeros b zs = true) :
    isZeroSpelling b zs = true := by
  rcases zs with _ | ⟨c, cs⟩
  · exact absurd h (by simp [isZeroZeros])
  · have hdz := (isZeroZeros_cons.1 h).1
    rw [isZeroSpelling_cons_zeros ?_]
    · exact h
    · rw [isBlank, decide_eq_false_iff_not, isZeroDigit_eq_true_iff.1 hdz]
      exact byteOfDigit_zero_ne_blank_nat b

/-- `strip` empties exactly on lists whose every byte is a blank or a zero digit — the
decomposition `strip`'s own recursion performs, so this is the effect of the definition
rather than a claim about it. -/
theorem strip_nil_all (b : Nat) :
    ∀ {ds : List UInt8}, strip b ds = [] →
      ∀ c ∈ ds, isBlank c = true ∨ isZeroDigit b c = true := by
  intro ds
  induction ds with
  | nil => intro _ c hc; simp at hc
  | cons e t ih =>
      intro hs c hc
      have he : isBlank e = true ∨ isZeroDigit b e = true := by
        by_cases h' : isBlank e = true ∨ isZeroDigit b e = true
        · exact h'
        · rw [strip_cons h'] at hs; exact absurd hs (by simp)
      have ht : strip b t = [] := by rw [strip_skip he] at hs; exact hs
      rcases List.mem_cons.1 hc with rfl | hc
      · exact he
      · exact ih ht c hc


/-- A zero spelling starts either with a blank (and is its tail's) or is a zero-digit run.
Stated as a disjunction because those are the only two shapes the definition admits. -/
theorem isZeroSpelling_cons {b : Nat} {c : UInt8} {cs : List UInt8}
    (h : isZeroSpelling b (c :: cs) = true) :
    (isBlank c = true ∧ isZeroSpelling b cs = true) ∨ isZeroZeros b (c :: cs) = true := by
  by_cases hb : isBlank c = true
  · exact Or.inl ⟨hb, by rwa [isZeroSpelling_cons_blank hb] at h⟩
  · have hbf : isBlank c = false := by
      cases hh : isBlank c with
      | false => rfl
      | true => exact absurd hh hb
    exact Or.inr (by rwa [isZeroSpelling_cons_zeros hbf] at h)

/-- Dropping a head from a longer zero-digit run leaves a zero-digit run. -/
theorem isZeroZeros_tail {b : Nat} {c : UInt8} {cs : List UInt8}
    (h : isZeroZeros b (c :: cs) = true) (hne : cs ≠ []) : isZeroZeros b cs = true := by
  obtain ⟨_, hall⟩ := isZeroZeros_cons.1 h
  rcases cs with _ | ⟨x, xs⟩
  · exact absurd rfl hne
  · exact isZeroZeros_cons.2 ⟨hall x (List.mem_cons_self ..),
      fun y hy => hall y (List.mem_cons_of_mem x hy)⟩

/-- **A zero spelling is absorbed**: `strip` empties it. -/
theorem strip_nil_all' (b : Nat) :
    ∀ {ds : List UInt8}, isZeroSpelling b ds = true →
      ∀ c ∈ ds, isBlank c = true ∨ isZeroDigit b c = true := by
  intro ds
  induction ds with
  | nil => intro _ c hc; simp at hc
  | cons e t ih =>
      intro h c hc
      rcases isZeroSpelling_cons h with ⟨hb, h'⟩ | hz
      · have ht := ih h'
        rcases List.mem_cons.1 hc with rfl | hc
        · exact Or.inl hb
        · exact ht c hc
      · have hall := (isZeroZeros_cons.1 hz).2
        rcases List.mem_cons.1 hc with rfl | hc
        · exact Or.inr (isZeroZeros_cons.1 hz).1
        · exact Or.inr (hall c hc)

/-- Every byte of a zero-digit run is the zero digit. -/
theorem isZeroZeros_all {b : Nat} {zs : List UInt8} (h : isZeroZeros b zs = true) :
    ∀ c ∈ zs, isZeroDigit b c = true := by
  rcases zs with _ | ⟨c, cs⟩
  · intro x hx; simp at hx
  · obtain ⟨h1, h2⟩ := isZeroZeros_cons.1 h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact h2 x hx

/-- A zero-digit run contains no blank. Immediate from the disjointness of alphabet bytes
and ASCII 32, which is `byteOfDigit_zero_ne_blank_nat`. -/
theorem isZeroZeros_blank_free {b : Nat} {zs : List UInt8} (h : isZeroZeros b zs = true) :
    ∀ c ∈ zs, isBlank c = false := by
  intro c hc
  have hdz := isZeroZeros_all h c hc
  rw [isBlank, decide_eq_false_iff_not, isZeroDigit_eq_true_iff.1 hdz]
  exact byteOfDigit_zero_ne_blank_nat b

theorem strip_nil_of_spelling (b : Nat) :
    ∀ {ds : List UInt8}, isZeroSpelling b ds = true → strip b ds = [] := by
  intro ds
  induction ds with
  | nil => intro _; rfl
  | cons c cs ih =>
      intro h
      rw [strip_skip (strip_nil_all' b h c (List.mem_cons_self ..))]
      by_cases hb : isBlank c = true
      · exact ih (by rwa [isZeroSpelling_cons_blank hb] at h)
      · have hbf : isBlank c = false := by
          cases hh : isBlank c with
          | false => rfl
          | true => exact absurd hh hb
        have hz : isZeroZeros b (c :: cs) = true := (isZeroSpelling_cons_zeros hbf).symm ▸ h
        cases cs with
        | nil => rfl
        | cons x xs =>
            -- the tail after removing the head is `x :: xs`, whose run shape is `hz`'s
            -- with the head dropped; the disjointness of blanks and zero digits is the
            -- reason a zero-digit run is a zero spelling, proved here rather than through
            -- `isZeroZeros_spelling`, which lives below the lemma that supplies it
            have hx : isZeroZeros b (x :: xs) = true :=
              isZeroZeros_cons.2 ⟨(isZeroZeros_cons.1 hz).2 x (List.mem_cons_self ..),
                fun y hy => (isZeroZeros_cons.1 hz).2 y (List.mem_cons_of_mem x hy)⟩
            have hxf : isBlank x = false := by
              rw [isBlank, decide_eq_false_iff_not,
                isZeroDigit_eq_true_iff.1 (isZeroZeros_cons.1 hx).1]
              exact byteOfDigit_zero_ne_blank_nat b
            exact ih (hx ▸ isZeroSpelling_cons_zeros hxf ▸ rfl : isZeroSpelling b (x :: xs) = true)

/-- `trimFor b ds` — the canonical numeral for the lax spelling `ds`, or `none` if `ds`
names no number.

`some` on: leading blanks and leading zero digits (in any interleaving), then a
non-empty run of digits, and nothing else. `none` on everything else — a trailing
blank, an out-of-alphabet byte, trailing data after a numeral, the empty input, and an
input of blanks only.

The all-zero case is the delicate one: `"000"` and `"  0"` are spellings of zero and
must reach `ofNat b 0`, while `""` and `"   "` are not spellings of anything. The test
is `strip` being empty (so every remaining byte was a blank or a zero digit) **and** at
least one byte having survived (so a digit was actually written). -/
def trimFor (b : Nat) (ds : List UInt8) : Option (List UInt8) :=
  let t := strip b ds
  if t = [] then
    (if isZeroSpelling b ds then some (ofNat b 0) else none)
  else if isDigits b t then some t else none

/-- `isNumeral b ds` — `ds` is a spelling `trimFor` accepts. On this subtype `trimFor`
is a total endofunction into the canonical forms, which is what makes `numeralIso` an
ordinary `Iso` over a genuine quotient. -/
def isNumeral (b : Nat) (ds : List UInt8) : Bool := (trimFor b ds).isSome

/-! ## Blank bytes and alphabet bytes are disjoint

An alphabet byte is never a blank. ASCII 32 is below every alphabet's window, and the
`if`-chains `byteOfDigitNat` uses never land on it, which the case split below
discharges radix by radix. This is what lets `dropWhile isBlank` leave an `ofNat`
alone. -/

theorem byteOfDigitNat_ne_32 (r d : Nat) (hr : 2 ≤ r) (hd : d < r) :
    byteOfDigitNat r d ≠ 32 := by
  unfold byteOfDigitNat
  by_cases h32 : r = 32
  · subst h32
    by_cases h25 : d ≤ 25
    · simp [h25]; omega
    · simp [h25]; omega
  · by_cases h64 : r = 64
    · subst h64
      simp only [h32, ite_false]
      by_cases h1 : d ≤ 25
      · simp [h1]; omega
      · by_cases h2 : d ≤ 51
        · simp [h1, h2]; omega
        · by_cases h3 : d ≤ 61
          · simp [h1, h2, h3]; omega
          · by_cases h62 : d = 62
            · simp [h62]
            · rw [ite_eq_right (by omega : ¬ d ≤ 25), ite_eq_right (by omega : ¬ d ≤ 51),
                  ite_eq_right h3, ite_eq_right h62]
              show ¬ (47 : Nat) = 32
              omega
    · by_cases h16 : r = 16
      · subst h16
        by_cases h9 : d ≤ 9
        · simp [h32, h64, h9]; omega
        · simp [h32, h64, h9]; omega
      · simp [h32, h64, h16]; omega

/-- The `UInt8` spelling, which is the one `trimFor` inspects. -/
theorem byteOfDigit_toNat_ne_32 {b x : Nat} (hr : IsRadix b) (hx : x < b) :
    (byteOfDigit b x).toNat ≠ 32 := by
  have hb2 : 2 ≤ b := isRadix_ge2 hr
  have hlt := byteOfDigitNat_ne_32 b x hb2 hx
  intro h
  rw [byteOfDigit_toNat] at h
  have hlt256 : byteOfDigitNat b x < 256 := by
    clear h hlt
    have hb64 : b ≤ 64 := isRadix_le64 hr
    have hx' : x < 256 := by omega
    unfold byteOfDigitNat
    split
    · split <;> omega
    · split
      · rename_i hb
        subst hb
        split
        · omega
        · split
          · omega
          · split
            · omega
            · split
              · omega
              · omega
      · split
        · split <;> omega
        · omega
  omega

/-- `ofNat`'s zero digit is the zero-digit byte. -/
theorem ofNat_zero_head (b : Nat) : (ofNat b 0).head? = some (byteOfDigit b 0) := by
  unfold ofNat
  rw [ite_eq_left rfl]
  rfl

/-- `ofNat`'s zero digit is the byte `isZeroDigit` names. -/
theorem isZeroDigit_ofNat_zero (b : Nat) :
    isZeroDigit b ((ofNat b 0).headD 0) = true := by
  have hd : (ofNat b 0).headD 0 = byteOfDigit b 0 := by
    cases h : ofNat b 0 with
    | nil =>
        have hh := ofNat_zero_head b
        rw [h] at hh
        cases hh
    | cons x xs =>
        show x = byteOfDigit b 0
        have hh := ofNat_zero_head b
        rw [h] at hh
        simpa using hh
  exact beq_iff_eq.2 (by rw [hd])

/-- A blank byte is not a digit, so `dropWhile isBlank` leaves an `ofNat` alone. -/
theorem ofNat_dropWhile_blank {b : Nat} (hr : IsRadix b) {n : Nat} (hn : n ≠ 0) :
    (ofNat b n).dropWhile isBlank = ofNat b n := by
  unfold ofNat
  rw [ite_eq_right hn]
  rcases hd : natDigits b n with _ | ⟨x, xs⟩
  · exact absurd hd (natDigits_ne_nil hr n hn)
  · have hxr : x < b := natDigits_lt hr n x (by rw [hd]; exact List.mem_cons_self ..)
    simp only [List.map_cons]
    rw [List.dropWhile_cons, ite_eq_right]
    intro hb
    exact byteOfDigit_toNat_ne_32 hr hxr (isBlank_eq_true_iff.1 hb)

/-- `ofNat` of a positive value starts with a non-zero digit, so `digitTail` leaves it
alone. -/
theorem ofNat_digitTail {b : Nat} (hr : IsRadix b) {n : Nat} (hn : n ≠ 0) :
    digitTail b (ofNat b n) = ofNat b n := by
  unfold ofNat
  rw [ite_eq_right hn]
  rcases hd : natDigits b n with _ | ⟨x, xs⟩
  · exact absurd hd (natDigits_ne_nil hr n hn)
  · have hxr : x < b := natDigits_lt hr n x (by rw [hd]; exact List.mem_cons_self ..)
    have hxne : x ≠ 0 := by
      have := natDigits_head_ne_zero hr n hn
      rw [hd] at this
      simpa using this
    simp only [List.map_cons]
    rw [digitTail, ite_eq_right]
    intro hz
    apply hxne
    have h1 : (byteOfDigit b x).toNat = (byteOfDigit b 0).toNat := isZeroDigit_eq_true_iff.1 hz
    exact byteOfDigit_inj hr hxr (by have := isRadix_ge2 hr; omega) (UInt8.toNat.inj h1)


/-! ## `digitTail`'s cons equations and idempotence

The cons equations are stated for `true`/`false` explicitly rather than through
`digitTail`'s `match`, because the `match` does not reduce at a variable tail. -/

theorem digitTail_cons_zero {b : Nat} {c : UInt8} {cs : List UInt8}
    (h : isZeroDigit b c = true) : digitTail b (c :: cs) = digitTail b cs := by
  show (if isZeroDigit b c then digitTail b cs else c :: cs) = digitTail b cs
  rw [ite_eq_left h]

theorem digitTail_cons_ne {b : Nat} {c : UInt8} {cs : List UInt8}
    (h : isZeroDigit b c = false) : digitTail b (c :: cs) = c :: cs := by
  show (if isZeroDigit b c then digitTail b cs else c :: cs) = c :: cs
  rw [ite_eq_right]
  intro hc
  rw [h] at hc
  exact Bool.noConfusion hc

/-- **`digitTail` is idempotent** — dropping leading zeros twice drops them once. -/
theorem digitTail_idem (b : Nat) (zs : List UInt8) :
    digitTail b (digitTail b zs) = digitTail b zs := by
  induction zs with
  | nil => rfl
  | cons c cs ih =>
      by_cases hb : isZeroDigit b c = true
      · rw [digitTail_cons_zero hb]
        exact ih
      · have hf : isZeroDigit b c = false := by
          cases h : isZeroDigit b c
          · rfl
          · exact absurd h hb
        rw [digitTail_cons_ne hf, digitTail_cons_ne hf]

/-- The digit zero of every radix this layer serves is a digit of its alphabet. -/
theorem digitVal_byteOfDigit_zero {b : Nat} (hr : IsRadix b) :
    (digitVal b (byteOfDigit b 0)).isSome = true := by
  unfold digitVal
  rw [byteOfDigit_toNat]
  unfold byteOfDigitNat
  simp only []
  cases hr with
  | b2 => decide
  | b4 => decide
  | b8 => decide
  | b10 => decide
  | b16 => decide
  | b32 => decide
  | b64 => decide

/-- **`dropWhile` is idempotent** — dropping leading blanks twice drops them once. Not
in the stdlib under this name, so it is proved here rather than assumed. -/
theorem dropWhile_idem (p : UInt8 → Bool) (l : List UInt8) :
    (l.dropWhile p).dropWhile p = l.dropWhile p := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.dropWhile_cons]
      by_cases h : p x = true
      · rw [ite_eq_left h, ih]
      · rw [ite_eq_right h]
        rw [List.dropWhile_cons, ite_eq_right h]

/-- The head of a `digitTail` is never a zero digit: `digitTail` only stops at a
non-zero byte or at the end. -/
theorem digitTail_head_ne_zero {b : Nat} :
    ∀ (l : List UInt8) {x : UInt8} {xs : List UInt8}, digitTail b l = x :: xs →
      isZeroDigit b x = false := by
  intro l
  induction l with
  | nil => intro x xs h; simp [digitTail] at h
  | cons c cs ih =>
      intro x xs h
      by_cases hz : isZeroDigit b c = true
      · rw [digitTail_cons_zero hz] at h
        exact ih h
      · have hf : isZeroDigit b c = false := by
          cases hh : isZeroDigit b c
          · rfl
          · exact absurd hh hz
        rw [digitTail_cons_ne hf] at h
        have h1 : c = x := (List.cons.inj h).1
        rw [← h1]
        exact hf

theorem isZeroDigit_not_blank {b : Nat} {c : UInt8} (h : isZeroDigit b c = true) :
    isBlank c = false := by
  have hz : c.toNat = (byteOfDigit b 0).toNat := isZeroDigit_eq_true_iff.1 h
  rw [isBlank, decide_eq_false_iff_not, hz]
  exact byteOfDigit_zero_ne_blank_nat b


/-- Every byte `ofNat` emits is not a blank. The load-bearing fact is that ASCII 32 is
below every alphabet's window: no digit of any radix this layer serves is a space. -/
theorem byteOfDigitNat_bounded (r d : Nat) (hr : 2 ≤ r) (hr64 : r ≤ 64) (hd : d < r) :
    byteOfDigitNat r d < 256 := by
  have hd256 : d < 256 := by omega
  unfold byteOfDigitNat
  split
  · split <;> omega
  · split
    · rename_i hb
      subst hb
      split
      · omega
      · split
        · omega
        · split
          · omega
          · split
            · omega
            · omega
    · split
      · split <;> omega
      · omega

theorem byteOfDigit_toNat_val {b d : Nat} (hr : IsRadix b) (hd : d < b) :
    (byteOfDigit b d).toNat = byteOfDigitNat b d := by
  rw [byteOfDigit_toNat]
  exact Nat.mod_eq_of_lt (byteOfDigitNat_bounded b d (isRadix_ge2 hr) (isRadix_le64 hr) hd)

/-- Every byte `ofNat` emits is not a blank, because ASCII 32 is below every alphabet's
window. -/
theorem byteOfDigitNat_ne_32' {r d : Nat} (hr : 2 ≤ r) (hr64 : r ≤ 64) (hd : d < r) :
    byteOfDigitNat r d ≠ 32 := by
  unfold byteOfDigitNat
  by_cases h32 : r = 32
  · subst h32
    by_cases h25 : d ≤ 25
    · simp [h25]; omega
    · simp [h25]; omega
  · rw [ite_eq_right h32]
    by_cases h64 : r = 64
    · subst h64
      rw [ite_eq_left rfl]
      by_cases h1 : d ≤ 25
      · rw [ite_eq_left h1]; omega
      · rw [ite_eq_right h1]
        by_cases h2 : d ≤ 51
        · rw [ite_eq_left h2]; omega
        · rw [ite_eq_right h2]
          by_cases h3 : d ≤ 61
          · rw [ite_eq_left h3]; omega
          · rw [ite_eq_right h3]
            by_cases h62 : d = 62
            · rw [ite_eq_left h62]; omega
            · rw [ite_eq_right h62]; omega
    · rw [ite_eq_right h64]
      by_cases h16 : r = 16
      · subst h16
        rw [ite_eq_left rfl]
        by_cases h9 : d ≤ 9
        · rw [ite_eq_left h9]; omega
        · rw [ite_eq_right h9]; omega
      · rw [ite_eq_right h16]; omega

theorem byteOfDigit_ne_32 {b d : Nat} (hr : IsRadix b) (hd : d < b) :
    (byteOfDigit b d).toNat ≠ 32 := by
  rw [byteOfDigit_toNat_val hr hd]
  exact byteOfDigitNat_ne_32' (isRadix_ge2 hr) (isRadix_le64 hr) hd

/-- Every byte `ofNat` emits is not a blank. -/
theorem ofNat_isBlank_false {b n : Nat} (hr : IsRadix b) :
    ∀ c ∈ ofNat b n, isBlank c = false := by
  intro c hc
  unfold ofNat at hc
  by_cases hn : n = 0
  · rw [ite_eq_left hn] at hc
    simp only [List.mem_singleton] at hc
    subst hc
    unfold isBlank
    rw [decide_eq_false_iff_not]
    rw [byteOfDigit_toNat_val hr (by have := isRadix_ge2 hr; omega)]
    exact byteOfDigitNat_ne_32' (isRadix_ge2 hr) (isRadix_le64 hr)
      (by have := isRadix_ge2 hr; omega)
  · rw [ite_eq_right hn] at hc
    obtain ⟨d, hdmem, rfl⟩ := List.mem_map.1 hc
    unfold isBlank
    rw [decide_eq_false_iff_not]
    exact byteOfDigit_ne_32 hr (natDigits_lt hr n d hdmem)


/-! ## `ofNat`'s output is a canonical spelling -/

/-- `ofNat b 0` is the single zero-digit byte. -/
theorem ofNat_zero_eq (b : Nat) : ofNat b 0 = [byteOfDigit b 0] := by
  unfold ofNat
  rw [ite_eq_left rfl]

/-- The zero byte is not a blank. -/
theorem byteOfDigit_zero_ne_blank (b : Nat) : isBlank (byteOfDigit b 0) = false := by
  rw [isBlank, decide_eq_false_iff_not]
  intro h
  rw [byteOfDigit_toNat] at h
  unfold byteOfDigitNat at h
  by_cases h32 : b = 32
  · subst h32; rw [ite_eq_left rfl, ite_eq_left (by omega : (0:Nat) ≤ 25)] at h; omega
  · rw [ite_eq_right h32] at h
    by_cases h64 : b = 64
    · subst h64; rw [ite_eq_left rfl, ite_eq_left (by omega : (0:Nat) ≤ 25)] at h; omega
    · rw [ite_eq_right h64] at h
      by_cases h16 : b = 16
      · subst h16; rw [ite_eq_left rfl, ite_eq_left (by omega : (0:Nat) ≤ 9)] at h; omega
      · rw [ite_eq_right h16] at h; omega

theorem ofNat_zero_dropWhile (b : Nat) : (ofNat b 0).dropWhile isBlank = ofNat b 0 := by
  rw [ofNat_zero_eq, List.dropWhile_cons, ite_eq_right]
  intro hb
  rw [byteOfDigit_zero_ne_blank] at hb
  exact absurd hb (by simp)

theorem ofNat_zero_digitTail (b : Nat) : digitTail b (ofNat b 0) = [] := by
  rw [ofNat_zero_eq]
  show (if isZeroDigit b (byteOfDigit b 0) then digitTail b [] else [byteOfDigit b 0]) = []
  have h : isZeroDigit b (byteOfDigit b 0) = true := by
    have := isZeroDigit_ofNat_zero b
    rw [ofNat_zero_eq] at this
    simpa using this
  rw [h]; rfl

theorem ofNat_zero_ne_nil (b : Nat) : ofNat b 0 ≠ [] := by
  rw [ofNat_zero_eq]; simp

theorem ofNat_ne_nil {b n : Nat} (hr : IsRadix b) (hn : n ≠ 0) : ofNat b n ≠ [] := by
  unfold ofNat
  rw [ite_eq_right hn]
  intro h
  have hh := natDigits_ne_nil hr n hn
  rw [List.map_eq_nil_iff] at h
  exact hh h

/-- Every byte `ofNat` emits is a digit of the radix's alphabet. -/
theorem ofNat_isDigits {b n : Nat} (hr : IsRadix b) : isDigits b (ofNat b n) = true := by
  rw [isDigits_iff]
  intro c hc
  unfold ofNat at hc
  by_cases hn : n = 0
  · rw [ite_eq_left hn] at hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact acceptsDigitZero_iff.2 (by
      rw [digitVal_byteOfDigit hr 0 (by have := isRadix_ge2 hr; omega)]; rfl)
  · rw [ite_eq_right hn] at hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [digitVal_byteOfDigit hr d (natDigits_lt hr n d hd)]
    rfl


/-- `strip` leaves a list alone when every byte is non-blank and the head is not a zero
digit. -/
theorem strip_eq_self {b : Nat} :
    ∀ (l : List UInt8), (∀ c ∈ l, isBlank c = false) → l ≠ [] →
      isZeroDigit b (l.headD 0) = false → strip b l = l
  | [], _, hne, _ => absurd rfl hne
  | c :: cs, hnb, _, hz => by
      apply strip_cons
      rintro (hb | hzz)
      · have hcf : isBlank c = false := hnb c (List.mem_cons_self ..)
        rw [hcf] at hb
        exact absurd hb (by simp)
      · have hcf : isZeroDigit b c = false := by simpa using hz
        rw [hcf] at hzz
        exact absurd hzz (by simp)

/-- `ofNat`'s head at a positive value is not the zero digit. -/
theorem ofNat_head_not_zeroD {b n : Nat} (hr : IsRadix b) (hn : n ≠ 0) :
    isZeroDigit b ((ofNat b n).headD 0) = false := by
  unfold ofNat
  rw [ite_eq_right hn]
  rcases hd : natDigits b n with _ | ⟨d, ds⟩
  · exact absurd hd (natDigits_ne_nil hr n hn)
  · have hd_ne : d ≠ 0 := by
      have := natDigits_head_ne_zero hr n hn
      rw [hd] at this
      simpa using this
    have hdr : d < b := natDigits_lt hr n d (by rw [hd]; exact List.mem_cons_self ..)
    have hb2 : 2 ≤ b := isRadix_ge2 hr
    show isZeroDigit b ((List.map (byteOfDigit b) (d :: ds)).headD 0) = false
    simp only [List.map_cons, List.headD_cons]
    unfold isZeroDigit
    rw [beq_eq_false_iff_ne]
    intro hh
    exact hd_ne (byteOfDigit_inj hr hdr (by omega) (UInt8.toNat.inj hh))

/-- `strip` leaves a positive `ofNat` alone. -/
theorem strip_ofNat {b n : Nat} (hr : IsRadix b) (hn : n ≠ 0) :
    strip b (ofNat b n) = ofNat b n :=
  strip_eq_self _ (ofNat_isBlank_false hr) (ofNat_ne_nil hr hn) (ofNat_head_not_zeroD hr hn)

/-- `isZeroDigit` and `digitVal` agree at the zero digit, so the radix's zero byte is a
zero-digit run of one. The bridge `digitVal_byteOfDigit` is the only alphabet fact needed. -/
theorem isZeroZeros_ofNat_zero (b : Nat) :
    isZeroZeros b (ofNat b 0) = true := by
  rw [ofNat_zero_eq, isZeroZeros_cons]
  exact ⟨isZeroDigit_ofNat_zero b, by simp⟩

/-- The radix's zero numeral is a zero spelling, so `trimFor` maps it to `ofNat b 0`. -/
theorem isZeroSpelling_ofNat_zero (b : Nat) : isZeroSpelling b (ofNat b 0) = true := by
  rw [ofNat_zero_eq]
  refine (isZeroSpelling_cons_zeros ?_ ).trans (isZeroZeros_ofNat_zero b)
  show isBlank (byteOfDigit b 0) = false
  rw [isBlank, decide_eq_false_iff_not]
  exact byteOfDigit_zero_ne_blank_nat b

/-- **`ofNat` emits canonical spellings**: `trimFor` maps an `ofNat` to itself. -/
theorem trimFor_ofNat {b n : Nat} (hr : IsRadix b) :
    trimFor b (ofNat b n) = some (ofNat b n) := by
  unfold trimFor
  by_cases hn : n = 0
  · subst hn
    have hz : strip b (ofNat b 0) = [] := by
      rw [ofNat_zero_eq]
      apply strip_skip
      right
      have h : isZeroDigit b (byteOfDigit b 0) = true := by
        have := isZeroDigit_ofNat_zero b
        rw [ofNat_zero_eq] at this
        simpa using this
      exact h
    rw [ite_eq_left hz, ite_eq_left (isZeroSpelling_ofNat_zero b)]
  · have hs : strip b (ofNat b n) = ofNat b n := strip_ofNat hr hn
    rw [ite_eq_right (by rw [hs]; exact ofNat_ne_nil hr hn), hs,
        ite_eq_left (ofNat_isDigits hr)]

/-- **The three-spelling witness.** Canonical, leading-zero and leading-whitespace
spellings of one number all reach the same canonical form under the normaliser.

This is `spec.md`'s "Three spellings reach one quotient element" scenario as a theorem
rather than a comment, and it is the task that found the zero-spelling defect: the shipped
`trimFor` passed it for every non-zero number and failed it for zero, because the defect was
confined to the class where the only digit is the zero digit. Stated over an arbitrary
spelling `ds` rather than three literals, so it covers every absorbed variation at once —
`trimFor_ofNat` on the right is what makes the image single.

**Mutation-tested.** Reverting the zero branch's guard to the superseded `isDigits b ds`
makes the literal witness `trimFor 10 [32,32,48] = some [48]` fail, and removing one
absorbed variation (leading blanks) makes `three_spellings`' premise unsatisfiable for that
spelling — both fire. -/
theorem three_spellings {b n : Nat} (hr : IsRadix b) {ds : List UInt8}
    (h : trimFor b ds = some (ofNat b n)) :
    trimFor b ds = trimFor b (ofNat b n) := by
  rw [h, trimFor_ofNat hr]

/-- The witness at the literals the spec names, in radix 10: `"7"`, `"007"` and `"  7"` all
normalise to `"7"`. `decide` closes each because every input is a closed list. -/
theorem three_spellings_ten :
    trimFor 10 [0x37] = some [0x37] ∧
    trimFor 10 [0x30, 0x30, 0x37] = some [0x37] ∧
    trimFor 10 [0x20, 0x20, 0x37] = some [0x37] :=
  ⟨by decide, by decide, by decide⟩

/-- The same three spellings for **zero** — the class the defect was confined to, and the
reason this witness and the fix are one task. -/
theorem three_spellings_zero :
    trimFor 10 [0x30] = some [0x30] ∧
    trimFor 10 [0x30, 0x30] = some [0x30] ∧
    trimFor 10 [0x20, 0x20, 0x30] = some [0x30] :=
  ⟨by decide, by decide, by decide⟩


/-- `trimFor` maps the radix's zero numeral to itself. This is the zero arm of
`trimFor_idem`'s first branch, stated separately so that idempotence needs no `IsRadix`. -/
theorem trimFor_ofNat_self_zero (b : Nat) : trimFor b (ofNat b 0) = some (ofNat b 0) := by
  unfold trimFor
  rw [ite_eq_left (strip_nil_of_spelling b (isZeroSpelling_ofNat_zero b)),
      ite_eq_left (isZeroSpelling_ofNat_zero b)]

/-- **`trimFor` is idempotent on its image** — the `Codec.Normalizer` law.

**No `IsRadix` hypothesis.** Both branches settle on `strip`'s own equations — `strip_idem`,
and `strip`'s recursion for the zero arm — plus the fact that `trimFor`'s answer is already
canonical, so idempotence is a fact about the normaliser's *shape* rather than about the
alphabet. The hypothesis was carried while the zero branch tested `isDigits`; the zero-spelling
fix removed the dependency, and keeping it would be a claim the theorem does not make. -/
theorem trimFor_idem {b : Nat} {ds t : List UInt8}
    (h : trimFor b ds = some t) : trimFor b t = some t := by
  unfold trimFor at h ⊢
  by_cases hs : strip b ds = []
  · rw [ite_eq_left hs] at h
    -- the branch accepted, so `ds` was a zero spelling and `t = ofNat b 0`
    by_cases hd : isZeroSpelling b ds = true
    · rw [ite_eq_left hd] at h
      rw [← Option.some.inj h]
      exact trimFor_ofNat_self_zero b
    · rw [ite_eq_right hd] at h; exact absurd h (by simp)
  · rw [ite_eq_right hs] at h
    by_cases hd : isDigits b (strip b ds) = true
    · rw [ite_eq_left hd] at h
      have hst : strip b (strip b ds) = strip b ds := strip_idem b ds
      rw [← Option.some.inj h, hst, ite_eq_right hs, hd]
      rfl
    · rw [ite_eq_right hd] at h; exact absurd h (by simp)


theorem natVal_snoc (b : Nat) (vs : List Nat) (v : Nat) :
    natVal b (vs ++ [v]) = natVal b vs * b + v := by
  rw [natVal_append]; simp [natVal]

theorem natVal_mod (b : Nat) (vs : List Nat) (v : Nat) (hv : v < b) :
    natVal b (vs ++ [v]) % b = v := by
  rw [natVal_snoc, Nat.add_mod, Nat.mul_comm (natVal b vs) b, Nat.mul_mod_right, Nat.zero_add,
      Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hv]

theorem natVal_div (b : Nat) (vs : List Nat) (v : Nat) (hb : 0 < b) (hv : v < b) :
    natVal b (vs ++ [v]) / b = natVal b vs := by
  rw [natVal_snoc]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hv, Nat.zero_add]

theorem natVal_pos {b : Nat} (hb : 2 ≤ b) :
    ∀ (vs : List Nat), vs ≠ [] → vs.head? ≠ some 0 → 0 < natVal b vs
  | [], hne, _ => absurd rfl hne
  | v :: vs, _, hhd => by
      have hv : 0 < v := by
        by_cases h0 : v = 0
        · exact absurd (by rw [h0]; rfl) hhd
        · omega
      cases vs with
      | nil => simp [natVal]; omega
      | cons w ws =>
          simp only [natVal]
          have hb1 : 0 < b ^ (w :: ws).length := Nat.pow_pos (by omega)
          have : 0 < v * b ^ (w :: ws).length := Nat.mul_pos hv hb1
          omega

theorem dropLast_ne_nil {l : List Nat} (h : 2 ≤ l.length) : l.dropLast ≠ [] := by
  intro hnil
  have hlen := List.length_dropLast (xs := l)
  rw [hnil] at hlen
  simp at hlen
  omega

theorem head_append_singleton {l : List Nat} {a : Nat} :
    (l ++ [a]).head? = l.head?.or (some a) := List.head?_append

theorem head_or_some_ne {l : List Nat} {a : Nat} (hne : l ≠ []) :
    (l.head?.or (some a)) ≠ some 0 ↔ l.head? ≠ some 0 := by
  cases hh : l.head? with
  | none => exact absurd (List.head?_eq_none_iff.1 hh) hne
  | some x => simp

/-- **Canonical digit lists are unique**, by length induction: a non-empty list whose
every digit is below the radix, with a non-zero head, is exactly `natDigits` of the value
it denotes. This is the injection the `Iso`'s backward direction needs. -/
theorem natVal_inj_head {b : Nat} (hr : IsRadix b) :
    ∀ (n : Nat) (vs : List Nat), vs.length = n → (∀ v ∈ vs, v < b) →
      vs.head? ≠ some 0 → ∀ m, natVal b vs = m → vs = natDigits b m := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro vs hn hlt hhd m hm
    have hb2 : 2 ≤ b := isRadix_ge2 hr
    rcases vs with _ | ⟨v, t⟩
    · simp [natVal] at hm
      subst hm
      rw [natDigits]; rfl
    · rcases t with _ | ⟨w, ws⟩
      · -- single element
        simp only [natVal, List.length_nil, Nat.pow_zero, Nat.mul_one, Nat.add_zero] at hm
        subst hm
        have hv0 : v ≠ 0 := by
          intro h0; exact hhd (by rw [h0]; rfl)
        have hvlt : v < b := hlt v (by simp)
        rw [natDigits, ite_eq_right hv0, ite_eq_right (by omega : ¬ b < 2),
            Nat.div_eq_of_lt hvlt, Nat.mod_eq_of_lt hvlt, natDigits, ite_eq_left rfl]
        rfl
      · -- ≥ 2 elements; split off the last
        have hne : (v :: w :: ws) ≠ [] := by simp
        have hlen2 : 2 ≤ (v :: w :: ws).length := by simp
        have hinit : (v :: w :: ws) = (v :: w :: ws).dropLast ++ [(v :: w :: ws).getLast hne] :=
          (List.dropLast_concat_getLast hne).symm
        have hs_ne : (v :: w :: ws).dropLast ≠ [] := dropLast_ne_nil hlen2
        have hlast_mem : (v :: w :: ws).getLast hne ∈ v :: w :: ws := List.getLast_mem hne
        have hlast : (v :: w :: ws).getLast hne < b := hlt _ hlast_mem
        have hs_all : ∀ x ∈ (v :: w :: ws).dropLast, x < b := by
          intro x hx
          apply hlt x
          rw [hinit]
          exact List.mem_append_left _ hx
        have hshead : (v :: w :: ws).dropLast.head? ≠ some 0 := by
          rw [show (v :: w :: ws).dropLast.head? = some v from rfl]
          simpa using hhd
        have hpos : 0 < natVal b (v :: w :: ws).dropLast :=
          natVal_pos hb2 _ hs_ne hshead
        have hslen : (v :: w :: ws).dropLast.length < n := by
          have hL := List.length_dropLast (xs := (v :: w :: ws))
          have hn' : (v :: w :: ws).length = n := hn
          omega
        have hS : (v :: w :: ws).dropLast = natDigits b (natVal b (v :: w :: ws).dropLast) :=
          ih _ hslen _ rfl hs_all hshead _ rfl
        -- `dropLast`/`getLast` are definitionally head/tail, so restate the last element
        -- as a `Nat` variable first
        obtain ⟨last, hlast_eq⟩ : ∃ last : Nat, (v :: w :: ws).getLast hne = last := ⟨_, rfl⟩
        have hinit' : v :: w :: ws = (v :: w :: ws).dropLast ++ [last] := by
          rw [← hlast_eq]; exact hinit
        have hval_eq : natVal b (v :: w :: ws) = natVal b (v :: w :: ws).dropLast * b + last := by
          have h := natVal_snoc b (v :: w :: ws).dropLast last
          rw [← hinit'] at h
          exact h
        have hm2 : m = natVal b (v :: w :: ws).dropLast * b + last := hm ▸ hval_eq
        rw [hm2]
        have hne0 : natVal b (v :: w :: ws).dropLast * b + last ≠ 0 := by
          have h1 : 0 < natVal b (v :: w :: ws).dropLast * b := Nat.mul_pos hpos (by omega)
          omega
        have hlt' : last < b := by rw [← hlast_eq]; exact hlast
        subst hm2
        rw [natDigits_eq hr _ hne0]
        have hdv : (natVal b (v :: w :: ws).dropLast * b + last) / b =
            natVal b (v :: w :: ws).dropLast := by
          have h := natVal_div b (v :: w :: ws).dropLast last (by omega) hlt'
          rw [natVal_snoc] at h; exact h
        have hmd : (natVal b (v :: w :: ws).dropLast * b + last) % b = last := by
          have h := natVal_mod b (v :: w :: ws).dropLast last hlt'
          rw [natVal_snoc] at h; exact h
        rw [hdv, hmd]
        -- the inner `natDigits (natVal ...)` is `hS`'s left side; rewriting it inside the
        -- outer `natDigits` is blocked, so prove the outer form separately
        have : natDigits b (natVal b (v :: w :: ws).dropLast) = (v :: w :: ws).dropLast := hS.symm
        rw [this]
        exact hinit'


/-! ## `normF`, the numeral quotient, and `numeralIso`

This is the object the `basen` spec names: **a bijection between `Nat` and the radix's
numerals modulo information-free variation**.

## Why the codomain is a quotient, and why `normF`'s fallback is not the input

`Codec.Iso.law` is `apply a = some b ↔ unapply b = some a`. Stated over raw
`List UInt8`, `"007"` and `"7"` are two distinct left-hand values that must both map
to `7`, so `unapply 7` cannot be `some` of both and the `→` direction is **false** —
not unproved. So the equivalence lives in the codomain: the fixed points of a
normaliser, which is `Codec.Normal`.

`trimFor` is `Option`-valued, so `normF` supplies the total endofunction
`Codec.Normal` needs — and the fallback is **`ofNat b 0`, not the input**. The
input-as-fallback version looks natural and is wrong: `[]` is a fixed point of
`ds |>.getD ds`, while `trimFor b [] = none` (the empty input names no number),
and `toNat b [] = some 0` is a by-product of the fold's base case. So the `←`
direction would demand `[] = ofNat b 0 = "0"` — false. Mapping every rejected
spelling to the zero numeral instead means **every fixed point of `normF` is a
numeral** (`fixed_is_numeral`), which is exactly what the law needs.

## The two directions

- `→`: `apply` maps `n` to the class of `ofNat b n`; `trimFor_ofNat` says `trimFor`
  accepts it, so `normF` is the identity there, and `toNat_ofNat` reads it back.
- `←`: `toNat b f.raw = some n` on a fixed point. `fixed_is_numeral` gives that
  `trimFor` accepts `f.raw`; `fixed_eq_ofNat` then says a spelling the fold reads at
  `n` and the normaliser fixes **is** `ofNat b n`. That lemma is where
  `digitVal_some_byteOfDigit` (the value↔byte bridge), `natVal_inj_head` (numeral
  uniqueness) and `map_val_eq_ofNat` meet.

Zero is the radix's single zero digit throughout (D4): `toNat b [] = some 0` is a
fold by-product and no theorem here calls `[]` a numeral — `trimFor` rejects it and
`normF` maps it to `ofNat b 0`.

Every law here is `[propext, Quot.sound]`-only.
-/

theorem isDigits_of_toNat {b : Nat} : ∀ {ds : List UInt8}, (toNat b ds).isSome = true → isDigits b ds = true
  | [], _ => rfl
  | d :: ds, h => by
      rcases hd : digitVal b d with _ | v
      · rw [toNat_cons_none b d ds hd] at h; exact absurd h (by simp)
      · rw [toNat_cons_some b d ds v hd] at h
        rw [isDigits_cons]
        refine ⟨by rw [hd]; rfl, isDigits_of_toNat ?_⟩
        cases ht : toNat b ds with
        | none => rw [ht] at h; simp at h
        | some a => rfl

theorem toNat_map_val {b : Nat} (hr : IsRadix b) :
    ∀ (ds : List UInt8), isDigits b ds = true →
      toNat b ds = some (natVal b (ds.map fun c => (digitVal b c).getD 0))
  | [], _ => rfl
  | d :: ds, h => by
      rw [isDigits_cons] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h1
      rw [toNat_cons_some b d ds v hv, toNat_map_val hr ds h2]
      simp [List.map_cons, hv, natVal]

/-- A blank byte reads as **no digit** in every radix. The argument is the one
`digitVal_some_byteOfDigit` makes available: a byte the fold can read is `byteOfDigit` of the
value it read, and no alphabet byte is ASCII 32. This is why a blank anywhere makes the whole
fold reject rather than contributing zero. -/
theorem digitVal_eq_none_of_blank {b : Nat} (hr : IsRadix b) {c : UInt8}
    (h : isBlank c = true) : digitVal b c = none := by
  cases hd : digitVal b c with
  | none => rfl
  | some v =>
      exfalso
      have hbv : c = byteOfDigit b v := digitVal_some_byteOfDigit hr hd
      have hlt : v < b := digitVal_lt_of_some hr hd
      have hne : (byteOfDigit b v).toNat ≠ 32 := byteOfDigit_toNat_ne_32 hr hlt
      rw [isBlank_eq_true_iff] at h
      rw [hbv] at h
      exact hne h

/-- **A blank anywhere makes the fold reject.** `toNat` is not "blanks read as zero": a space
is outside every alphabet, so it poisons the whole conversion exactly like a wrong-alphabet
digit does. This is the lemma that separates `"  0"` (accepted, the blanks are *leading
padding* the normaliser removes) from `"  "` and `"0 "` (rejected). -/
theorem toNat_none_of_mem_blank {b : Nat} (hr : IsRadix b) :
    ∀ {ds : List UInt8}, (∃ c ∈ ds, isBlank c = true) → toNat b ds = none := by
  intro ds
  induction ds with
  | nil => intro h; rcases h with ⟨_, hc, _⟩; simp at hc
  | cons e t ih =>
      intro h
      obtain ⟨c, hc, hb⟩ := h
      have hcase : isBlank e = true ∨ ∃ c' ∈ t, isBlank c' = true := by
        rcases List.mem_cons.1 hc with he | hc
        · exact Or.inl (he ▸ hb)
        · exact Or.inr ⟨c, hc, hb⟩
      rcases hcase with hb0 | ⟨c', hc', hb'⟩
      · exact toNat_cons_none b e t (digitVal_eq_none_of_blank hr hb0)
      · cases hd : digitVal b e with
        | none => exact toNat_cons_none b e t hd
        | some v =>
            rw [toNat_cons_some b e t v hd, ih ⟨c', hc', hb'⟩]
            rfl

/-- A `strip`-empty list with no blank is a zero spelling: every byte is then a zero digit,
which is `isZeroZeros` by construction. The converse of `strip_nil_of_spelling` on the
non-blank inputs, and the reason the zero branch's two arms exhaust the `strip`-empty case. -/
theorem isZeroSpelling_of_strip_nil_no_blank {b : Nat} {ds : List UInt8}
    (hne : ds ≠ []) (hs : strip b ds = []) (hb : ¬ ∃ c ∈ ds, isBlank c = true) :
    isZeroSpelling b ds = true := by
  have hall : ∀ c ∈ ds, isZeroDigit b c = true := by
    intro c hc
    rcases strip_nil_all b hs c hc with h | h
    · exact absurd ⟨c, hc, h⟩ hb
    · exact h
  rcases ds with _ | ⟨c, cs⟩
  · exact absurd rfl hne
  · exact isZeroZeros_spelling (isZeroZeros_cons.2
      ⟨hall c (List.mem_cons_self ..), fun y hy => hall y (List.mem_cons_of_mem c hy)⟩)

theorem toNat_none_of_not_digits {b : Nat} :
    ∀ {ds : List UInt8}, isDigits b ds = false → toNat b ds = none
  | [], h => by
      have h1 : isDigits b ([] : List UInt8) = true := rfl
      rw [h1] at h; exact absurd h (by simp)
  | d :: ds, h => by
      have hbody : isDigits b (d :: ds) = ((digitVal b d).isSome && isDigits b ds) := rfl
      rw [hbody] at h
      by_cases h1 : (digitVal b d).isSome = true
      · rw [h1] at h
        simp only [Bool.true_and] at h
        obtain ⟨v, hv' ⟩ := Option.isSome_iff_exists.1 h1
        rw [toNat_cons_some b d ds v hv', toNat_none_of_not_digits (b := b) h]
        rfl
      · have hv : digitVal b d = none := by
          cases hh : digitVal b d with
          | none => rfl
          | some v => rw [hh] at h1; simp at h1
        rw [toNat_cons_none b d ds hv]

theorem digitVal_getD_lt {b : Nat} (hr : IsRadix b) {c : UInt8}
    (h : (digitVal b c).isSome = true) : (digitVal b c).getD 0 < b := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  rw [hv]
  simpa using digitVal_lt_of_some hr hv

theorem strip_length_le (b : Nat) : ∀ (l : List UInt8), (strip b l).length ≤ l.length
  | [] => Nat.le_refl _
  | c :: cs => by
      by_cases hb : isBlank c = true ∨ isZeroDigit b c = true
      · rw [strip_skip hb]
        have := strip_length_le b cs
        simp only [List.length_cons]
        omega
      · rw [strip_cons hb]; exact Nat.le_refl _

theorem strip_head {b : Nat} {x : UInt8} {xs : List UInt8}
    (h : strip b (x :: xs) = x :: xs) : isZeroDigit b x = false := by
  by_cases hb : isBlank x = true ∨ isZeroDigit b x = true
  · rw [strip_skip hb] at h
    have hl := strip_length_le b xs
    rw [h] at hl
    simp only [List.length_cons] at hl
    omega
  · cases hz : isZeroDigit b x
    · rfl
    · exact absurd (Or.inr hz) hb

theorem natVal_eq_zero {b : Nat} (hb : 2 ≤ b) :
    ∀ {vs : List Nat}, (∀ v ∈ vs, v < b) → natVal b vs = 0 → ∀ v ∈ vs, v = 0
  | [], _, _, v, hv => by simp at hv
  | x :: xs, hlt, h, v, hv => by
      simp only [natVal] at h
      have hx : x < b := hlt x (List.mem_cons_self ..)
      have hpos : 0 < b ^ xs.length := Nat.pow_pos (by omega)
      have hx0 : x = 0 := by
        rcases Nat.eq_zero_or_pos x with rfl | hp
        · rfl
        · exfalso
          have : 0 < x * b ^ xs.length := Nat.mul_pos hp hpos
          omega
      rw [List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact hx0
      · exact natVal_eq_zero hb (fun w hw => hlt w (List.mem_cons_of_mem _ hw)) (by omega) v hv

theorem eq_map_byteOfDigit {b : Nat} (hr : IsRadix b) {ds : List UInt8}
    (h : isDigits b ds = true) : ds = (ds.map fun c => (digitVal b c).getD 0).map (byteOfDigit b) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      rw [isDigits_cons] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h1
      have hdd : d = byteOfDigit b v := digitVal_some_byteOfDigit hr hv
      have hval : (digitVal b (byteOfDigit b v)).getD 0 = v := by
        rw [digitVal_byteOfDigit hr v (digitVal_lt_of_some hr hv)]
        rfl
      have hih := ih h2
      rw [List.map_cons, List.map_cons, hdd, hval]
      exact congrArg (List.cons (byteOfDigit b v)) hih

theorem head_val_ne_zero {b : Nat} (hr : IsRadix b) {x : UInt8} {xs : List UInt8}
    (hdig : isDigits b (x :: xs) = true) (hsx : strip b (x :: xs) = x :: xs) :
    ((x :: xs).map fun c => (digitVal b c).getD 0).head? ≠ some 0 := by
  have hz : isZeroDigit b x = false := strip_head hsx
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1
    ((isDigits_iff _).1 hdig x (List.mem_cons_self ..))
  intro hh
  have hv0 : v = 0 := by
    have h1 : (digitVal b x).getD 0 = 0 := by
      have h := congrArg (fun o => o.getD 0) hh
      simpa using h
    rw [hv] at h1
    simpa using h1
  have hxz : isZeroDigit b x = true := by
    rw [isZeroDigit_eq_true_iff, ← hv0, digitVal_some_byteOfDigit hr hv]
  rw [hz] at hxz
  exact absurd hxz (by simp)

theorem map_val_eq_ofNat {b n : Nat} (hr : IsRadix b) {vs : List Nat}
    (hvs : ∀ v ∈ vs, v < b) (hne : vs ≠ []) (hhd : vs.head? ≠ some 0)
    (hval : natVal b vs = n) : vs.map (byteOfDigit b) = ofNat b n := by
  have hinj : vs = natDigits b n := natVal_inj_head hr _ _ rfl hvs hhd n hval
  have hn : n ≠ 0 := by
    intro h0
    rw [h0] at hinj
    rw [(natDigits_eq_nil hr 0).2 rfl] at hinj
    exact hne hinj
  rw [hinj, ofNat, ite_eq_right hn]

/-- A `strip`-stable digit list never names zero. -/
theorem strip_digits_value_ne_zero {b : Nat} (hr : IsRadix b) {ds : List UInt8}
    (hs : strip b ds ≠ []) (hdd : isDigits b (strip b ds) = true)
    (hfix : trimFor b ds = some ds) (h : toNat b ds = some 0) : False := by
  unfold trimFor at hfix
  rw [ite_eq_right hs, ite_eq_left hdd] at hfix
  have hsd : ds = strip b ds := (Option.some.inj hfix).symm
  have hdig : isDigits b ds = true := by rw [hsd]; exact hdd
  have hval : natVal b (ds.map fun c => (digitVal b c).getD 0) = 0 := by
    have h2 := toNat_map_val hr ds hdig
    rw [h] at h2
    exact (Option.some.inj h2).symm
  have hlt : ∀ v ∈ ds.map (fun c => (digitVal b c).getD 0), v < b := by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hv
    exact digitVal_getD_lt hr ((isDigits_iff ds).1 hdig c hc)
  have hallzero := natVal_eq_zero (isRadix_ge2 hr) hlt hval
  rcases ds with _ | ⟨x, xs⟩
  · exact hs (by rw [← hsd])
  · have hsx : strip b (x :: xs) = x :: xs := hsd.symm
    have hz : isZeroDigit b x = false := strip_head hsx
    have hmem : (digitVal b x).getD 0 ∈ (x :: xs).map (fun c => (digitVal b c).getD 0) :=
      List.mem_map_of_mem (List.mem_cons_self ..)
    have hv0 : (digitVal b x).getD 0 = 0 := hallzero _ hmem
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1
      ((isDigits_iff (x :: xs)).1 hdig x (List.mem_cons_self ..))
    have hv0 : (digitVal b x).getD 0 = 0 := hallzero _ hmem
    have hv0' : v = 0 := by
      rw [hv] at hv0
      simpa using hv0
    have hxz : isZeroDigit b x = true := by
      rw [isZeroDigit_eq_true_iff, ← hv0', digitVal_some_byteOfDigit hr hv]
    rw [hz] at hxz
    exact absurd hxz (by simp)

/-- **A fixed point that converts is exactly `ofNat` of its value.** -/
theorem fixed_eq_ofNat {b : Nat} (hr : IsRadix b) {ds : List UInt8} {n : Nat}
    (hfix : trimFor b ds = some ds) (h : toNat b ds = some n) : ds = ofNat b n := by
  unfold trimFor at hfix
  by_cases hs : strip b ds = []
  · rw [ite_eq_left hs] at hfix
    by_cases hdd : isZeroSpelling b ds = true
    · rw [ite_eq_left hdd] at hfix
      have hz : ds = ofNat b 0 := (Option.some.inj hfix).symm
      rw [hz] at h
      rw [toNat_ofNat hr 0] at h
      rw [hz, ← Option.some.inj h]
    · rw [ite_eq_right hdd] at hfix; exact absurd hfix (by simp)
  · rw [ite_eq_right hs] at hfix
    by_cases hdd : isDigits b (strip b ds) = true
    · rw [ite_eq_left hdd] at hfix
      have hsd : ds = strip b ds := (Option.some.inj hfix).symm
      have hdig : isDigits b ds = true := by rw [hsd]; exact hdd
      have hfx : trimFor b ds = some ds := by
        unfold trimFor
        rw [ite_eq_right hs, ite_eq_left hdd]
        exact hfix
      have hn0 : n ≠ 0 := by
        intro hn'
        rw [hn'] at h
        exact strip_digits_value_ne_zero hr hs hdd hfx h
      have hval : natVal b (ds.map fun c => (digitVal b c).getD 0) = n := by
        have h2 := toNat_map_val hr ds hdig
        rw [h] at h2
        exact (Option.some.inj h2).symm
      have hlt : ∀ v ∈ ds.map (fun c => (digitVal b c).getD 0), v < b := by
        intro v hv
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hv
        exact digitVal_getD_lt hr ((isDigits_iff ds).1 hdig c hc)
      have hne : ds ≠ [] := by rw [hsd]; exact hs
      have hhd : (ds.map fun c => (digitVal b c).getD 0).head? ≠ some 0 := by
        rcases hh : ds with _ | ⟨x, xs⟩
        · exact absurd hh hne
        · subst hh
          have hsx : strip b (x :: xs) = x :: xs := hsd.symm
          exact head_val_ne_zero hr hdig hsx
      have hinj := natVal_inj_head hr _ _ rfl hlt hhd n hval
      have hne' : (ds.map fun c => (digitVal b c).getD 0) ≠ [] := by
        intro h0
        rw [List.map_eq_nil_iff] at h0
        exact hne h0
      rw [eq_map_byteOfDigit hr hdig]
      exact map_val_eq_ofNat hr hlt hne' hhd hval
    · rw [ite_eq_right hdd] at hfix; exact absurd hfix (by simp)


/-- `strip` can only drop blanks and zero digits, so a non-digit survivor is a non-digit
of the original list. -/
theorem strip_subset (b : Nat) : ∀ (ds : List UInt8), ∀ c ∈ strip b ds, c ∈ ds
  | [], c, hc => by simp [strip] at hc
  | d :: ds, c, hc => by
      by_cases hb : isBlank d = true ∨ isZeroDigit b d = true
      · rw [strip_skip hb] at hc
        exact List.mem_cons_of_mem _ (strip_subset b ds c hc)
      · rw [strip_cons hb] at hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ hc

/-- `strip` only drops bytes, so a non-digit survivor is a non-digit of the original. -/
theorem isDigits_strip_false {b : Nat} {ds : List UInt8}
    (hf : isDigits b (strip b ds) = false) : isDigits b ds = false := by
  cases hh : isDigits b ds with
  | false => rfl
  | true =>
      rw [isDigits_iff] at hh
      have hst : isDigits b (strip b ds) = true :=
        (isDigits_iff _).2 fun c hc => hh c (strip_subset b ds c hc)
      rw [hst] at hf
      exact absurd hf (by simp)

/-- **A blank-free `strip`-empty list is a zero spelling**, given it is the prefix-cut tail
of a zero digit. This is the constructive content `exists_blank_of_strip_nil_not_spelling`
needs: if no blank is present and `strip` emptied the list, every byte is a zero digit, so
the list is a zero-digit run and hence a zero spelling.

Stated recursively on the list with `strip_nil_all` as the only source of facts, so no step
needs a decision procedure or `Classical.choice`. -/
theorem isZeroSpelling_of_blank_free (b : Nat) :
    ∀ {ds : List UInt8}, ds ≠ [] → strip b ds = [] →
      (∀ c ∈ ds, isBlank c = false) → isZeroSpelling b ds = true := by
  intro ds
  induction ds with
  | nil => intro hne _ _; exact absurd rfl hne
  | cons x xs ih =>
      intro hne hs hbf
      have hall : ∀ c ∈ x :: xs, isBlank c = true ∨ isZeroDigit b c = true :=
        fun c hc => strip_nil_all b hs c hc
      have hbz : isZeroDigit b x = true := by
        rcases hall x (List.mem_cons_self ..) with hb | hz
        · exact absurd hb (by rw [hbf x (List.mem_cons_self ..)]; simp)
        · exact hz
      have hxf : isBlank x = false := hbf x (List.mem_cons_self ..)
      rw [isZeroSpelling_cons_zeros hxf, isZeroZeros_cons]
      refine ⟨hbz, fun y hy => ?_⟩
      rcases hall y (List.mem_cons_of_mem x hy) with hb | hz
      · exact absurd hb (by rw [hbf y (List.mem_cons_of_mem x hy)]; simp)
      · exact hz

/-- `isBlank` as a `Bool` search: a blank exists exactly when `any` finds one. The
`Bool`-valued form is what lets the constructive argument below decide blank-ness rather
than assume it, which is the difference between `[propext, Quot.sound]` and a
`Classical.choice` leak. -/
theorem exists_blank_iff (ds : List UInt8) :
    (∃ c ∈ ds, isBlank c = true) ↔ ds.any isBlank = true := by
  induction ds with
  | nil => simp
  | cons x xs ih =>
      rw [List.any_cons, Bool.or_eq_true]
      exact ⟨fun ⟨c, hc, hb⟩ => by
               rcases List.mem_cons.1 hc with rfl | hc
               · exact Or.inl hb
               · exact Or.inr (ih.1 ⟨c, hc, hb⟩),
             fun h => by
               rcases h with h | h
               · exact ⟨x, List.mem_cons_self .., h⟩
               · obtain ⟨c, hc, hb⟩ := ih.2 h
                 exact ⟨c, List.mem_cons_of_mem x hc, hb⟩⟩

/-- No blank exists iff `any isBlank` reports `false`. -/
theorem blank_free_of_not_any (ds : List UInt8) (h : ds.any isBlank = false) :
    ∀ c ∈ ds, isBlank c = false := by
  intro c hc
  cases hb : isBlank c with
  | false => rfl
  | true => exact absurd ((exists_blank_iff ds).1 ⟨c, hc, hb⟩) (by rw [h]; simp)

/-- **A `strip`-empty non-empty list with no blank is a zero spelling.** `strip_nil_all`
gives blank-or-zero-digit per byte; with no blank every byte is a zero digit, and a
non-empty zero-digit run is a zero spelling by construction. -/
theorem isZeroSpelling_of_strip_nil_blank_free (b : Nat) :
    ∀ {ds : List UInt8}, ds ≠ [] → strip b ds = [] →
      (∀ c ∈ ds, isBlank c = false) → isZeroSpelling b ds = true := by
  intro ds
  induction ds with
  | nil => intro hne _ _; exact absurd rfl hne
  | cons x xs ih =>
      intro _ hs hbf
      have hall : ∀ c ∈ x :: xs, isBlank c = true ∨ isZeroDigit b c = true :=
        fun c hc => strip_nil_all b hs c hc
      have hx : isZeroDigit b x = true := by
        rcases hall x (List.mem_cons_self ..) with hb | hz
        · exact absurd hb (by rw [hbf x (List.mem_cons_self ..)]; simp)
        · exact hz
      rw [isZeroSpelling_cons_zeros (hbf x (List.mem_cons_self ..)), isZeroZeros_cons]
      exact ⟨hx, fun y hy => by
        rcases hall y (List.mem_cons_of_mem x hy) with hb | hz
        · exact absurd hb (by rw [hbf y (List.mem_cons_of_mem x hy)]; simp)
        · exact hz⟩

/-- **A `strip`-empty non-empty list that is not a zero spelling contains a blank.**

Constructive and `Bool`-directed: `strip_nil_all` gives blank-or-zero-digit per byte, and
`isZeroSpelling_of_strip_nil_blank_free` turns "no blank" into a zero spelling. So either a
blank is found — the conclusion — or the list is a zero spelling, which `hns` refutes. The
`any isBlank` search is what keeps the case split decidable, and therefore keeps
`Classical.choice` out: `Classical.byContradiction` closes this in one line and leaks it
(measured on this lemma). -/
theorem exists_blank_of_strip_nil_not_spelling (b : Nat) :
    ∀ {ds : List UInt8}, ds ≠ [] → strip b ds = [] → ¬ isZeroSpelling b ds = true →
      ∃ c ∈ ds, isBlank c = true := by
  intro ds
  induction ds with
  | nil => intro hne _ _; exact absurd rfl hne
  | cons x xs ih =>
      intro hne hs hns
      cases hany : (x :: xs).any isBlank with
      | true => exact (exists_blank_iff _).2 hany
      | false =>
          exact absurd (isZeroSpelling_of_strip_nil_blank_free b (by simp) hs
            (blank_free_of_not_any _ hany)) hns

/-- `trimFor` rejecting a non-empty-all-blank input means the fold rejects it too.

The empty input is excluded on purpose: `trimFor b [] = none` (it names no number) while
`toNat b [] = some 0` (a by-product of the fold's base case). That asymmetry is D4's point,
and it is why the statement carries `ds ≠ []`. -/
theorem trimFor_none_toNat_none {b : Nat} (hr : IsRadix b) {ds : List UInt8}
    (hnel : ds ≠ []) (h : trimFor b ds = none) : toNat b ds = none := by
  simp only [trimFor] at h
  by_cases hs : strip b ds = []
  · rw [ite_eq_left hs] at h
    by_cases hd : isZeroSpelling b ds = true
    · rw [ite_eq_left hd] at h; exact absurd h (by simp)
    · -- `strip` emptied `ds`, so every byte is a blank or a zero digit; a list that is
      -- not a zero spelling therefore contains a **blank**, and a blank is in no alphabet
      have hblank : ∃ c ∈ ds, isBlank c = true :=
        exists_blank_of_strip_nil_not_spelling b hnel hs hd
      exact toNat_none_of_mem_blank hr hblank
  · rw [ite_eq_right hs] at h
    by_cases hd : isDigits b (strip b ds) = true
    · rw [ite_eq_left hd] at h; exact absurd h (by simp)
    · have hf : isDigits b (strip b ds) = false := by
        cases hh : isDigits b (strip b ds) with
        | false => rfl
        | true => exact absurd hh hd
      -- `strip` only removes blanks and zero digits, both of which are handled; a
      -- non-digit surviving `strip` is a non-digit of `ds`, so the fold rejects `ds` too
      exact toNat_none_of_not_digits (isDigits_strip_false hf)




/-- `normF b ds` — `trimFor`'s answer, or the radix's zero numeral when the input names
nothing.

The fallback is **not** the input: `[]` is a fixed point of `ds |>.getD ds`, and then
`toNat b [] = some 0` makes `[]` a left value the fold reads while `ofNat b 0 = "0"`,
so the `Iso` law's `←` would demand `[] = "0"`. Mapping every rejected spelling to the
zero numeral instead keeps every fixed point a **numeral**, which is what makes
`fixed_eq_ofNat` total. -/
def normF (b : Nat) (ds : List UInt8) : List UInt8 := (trimFor b ds).getD (ofNat b 0)

@[simp] theorem normF_def (b : Nat) (ds : List UInt8) :
    normF b ds = (trimFor b ds).getD (ofNat b 0) := rfl

theorem normF_of_trim {b : Nat} {ds t : List UInt8} (h : trimFor b ds = some t) : normF b ds = t := by
  rw [normF_def, h]; rfl

theorem normF_idem (b : Nat) (hr : IsRadix b) (ds : List UInt8) :
    normF b (normF b ds) = normF b ds := by
  cases h : trimFor b ds with
  | none =>
      have h1 : normF b ds = ofNat b 0 := by rw [normF_def, h]; rfl
      rw [h1, normF_of_trim (trimFor_ofNat hr)]
  | some t => rw [normF_of_trim h, normF_of_trim (trimFor_idem h)]

/-- Every fixed point of `normF` is a numeral `trimFor` accepts. -/
theorem fixed_is_numeral {b : Nat} (hr : IsRadix b) {ds : List UInt8}
    (hfix : normF b ds = ds) : trimFor b ds = some ds := by
  cases h : trimFor b ds with
  | none =>
      rw [normF_def, h] at hfix
      simp only [Option.getD] at hfix
      rw [← hfix] at h
      rw [trimFor_ofNat hr] at h
      exact absurd h (by simp)
  | some t =>
      rw [normF_def, h] at hfix
      simp only [Option.getD_some] at hfix
      rw [← hfix]


/-- `numeralIso b`: `Nat` ≃ the quotient of numerals, which `normF`'s fixed points are. -/
def numeralIso (b : Nat) (hr : IsRadix b) : Iso Nat (Normal (List UInt8) (normF b)) where
  apply n := some ⟨normF b (ofNat b n), normF_idem b hr (ofNat b n)⟩
  unapply f := toNat b f.raw
  law := by
    intro n f
    constructor
    · intro h
      have hf : normF b (ofNat b n) = f.raw := by
        have h1 : (⟨normF b (ofNat b n), normF_idem b hr (ofNat b n)⟩ : Normal (List UInt8) (normF b)) = f :=
          Option.some.inj h
        exact congrArg Normal.raw h1
      have hn : normF b (ofNat b n) = ofNat b n := normF_of_trim (trimFor_ofNat hr)
      show toNat b f.raw = some n
      rw [← hf, hn]
      exact toNat_ofNat hr n
    · intro h
      show some ⟨normF b (ofNat b n), normF_idem b hr (ofNat b n)⟩ = some f
      have hraw : toNat b f.raw = some n := h
      have hfix : trimFor b f.raw = some f.raw := fixed_is_numeral hr f.fixed
      have hof : f.raw = ofNat b n := fixed_eq_ofNat hr hfix hraw
      have hn : normF b (ofNat b n) = ofNat b n := normF_of_trim (trimFor_ofNat hr)
      have hval : f.raw = normF b (ofNat b n) := by rw [hof, hn]
      have : f = ⟨normF b (ofNat b n), normF_idem b hr (ofNat b n)⟩ := by
        apply Normal.ext
        exact hval
      rw [this]


/-! ## The three rejection laws of `trimFor` (task 2.4)

`spec.md` requires that a spelling naming no number be **rejected** rather than normalised:
a trailing blank, a digit outside the radix's alphabet, and trailing data after a valid
numeral. Each gets its own theorem here.

`trimFor` accepts through exactly two routes — `isZeroSpelling b ds` when `strip` empties the
input, and `isDigits b (strip b ds)` otherwise — so a rejection law is a proof that neither
holds. The `IsRadix` hypothesis appears only where the alphabet is consulted. -/

/-- A `Bool` that is not `true` is `false`. -/
theorem bool_eq_false_of_ne_true {x : Bool} (h : x ≠ true) : x = false := by
  cases x with
  | false => rfl
  | true => exact absurd rfl h

/-- The radix's zero digit reads as value `0`. -/
theorem isZeroDigit_zero_val {b : Nat} (hr : IsRadix b) {c : UInt8}
    (h : isZeroDigit b c = true) : digitVal b c = some 0 := by
  rw [isZeroDigit_eq_true_iff] at h
  have hc : c = byteOfDigit b 0 := UInt8.toNat.inj h
  rw [hc]
  exact digitVal_byteOfDigit hr 0 (by have := isRadix_ge2 hr; omega)

/-- `strip` of a single byte either empties it (it was blank or the zero digit) or leaves it. -/
theorem strip_singleton {b : Nat} {c : UInt8} :
    strip b [c] = [] ∨ strip b [c] = [c] := by
  by_cases h : isBlank c = true ∨ isZeroDigit b c = true
  · left
    rw [strip_skip h]
    rfl
  · right
    rw [strip_cons h]

/-- `strip` of `t ++ [blank]` is empty or still contains that blank. -/
theorem strip_append_blank {b : Nat} :
    ∀ (t : List UInt8) (c : UInt8), isBlank c = true →
      strip b (t ++ [c]) = [] ∨ ∃ x ∈ strip b (t ++ [c]), isBlank x = true
  | [], c, hb => by
      left
      rw [List.nil_append, strip_skip (Or.inl hb)]
      rfl
  | d :: ds, c, hb => by
      rw [List.cons_append]
      by_cases h : isBlank d = true ∨ isZeroDigit b d = true
      · rw [strip_skip h]; exact strip_append_blank ds c hb
      · right
        refine ⟨c, ?_, hb⟩
        rw [strip_cons h]
        exact List.mem_cons_of_mem d (by simp)

/-- `strip` of a list ending in a **non-absorbable** byte leaves the prefix's result intact. -/
theorem strip_append_keep {b : Nat} :
    ∀ (t : List UInt8) {c : UInt8}, isBlank c = false → isZeroDigit b c = false →
      strip b (t ++ [c]) = strip b t ++ [c]
  | [], c, hb, hz => by
      show strip b [c] = strip b [] ++ [c]
      rw [strip_cons (by rw [hb, hz]; simp)]
      rfl
  | d :: ds, c, hb, hz => by
      rw [List.cons_append]
      by_cases h : isBlank d = true ∨ isZeroDigit b d = true
      · rw [strip_skip h, strip_skip h]
        exact strip_append_keep ds hb hz
      · rw [strip_cons h, strip_cons h]
        rfl

/-- A list ending in a blank is never a zero spelling. -/
theorem not_zeroSpelling_append_blank {b : Nat} :
    ∀ (t : List UInt8) (c : UInt8), isBlank c = true → isZeroSpelling b (t ++ [c]) = false
  | [], c, hb => by
      show isZeroSpelling b [c] = false
      rw [isZeroSpelling_cons_blank hb]
      rfl
  | d :: ds, c, hb => by
      rw [List.cons_append]
      show isZeroSpelling b (d :: (ds ++ [c])) = false
      by_cases hd : isBlank d = true
      · rw [isZeroSpelling_cons_blank hd]
        exact not_zeroSpelling_append_blank ds c hb
      · have hdf : isBlank d = false := bool_eq_false_of_ne_true hd
        rw [isZeroSpelling_cons_zeros hdf]
        by_cases hz : isZeroZeros b (d :: (ds ++ [c])) = true
        · exfalso
          have hmem : c ∈ (d :: (ds ++ [c])) := by simp
          have hb' := isZeroZeros_blank_free hz c hmem
          rw [hb] at hb'
          exact absurd hb' (by simp)
        · exact bool_eq_false_of_ne_true hz

/-- A list containing a blank is not all digits. -/
theorem isDigits_false_of_mem_blank {b : Nat} (hr : IsRadix b) :
    ∀ {ds : List UInt8}, (∃ c ∈ ds, isBlank c = true) → isDigits b ds = false
  | [], h => by rcases h with ⟨_, hc, _⟩; simp at hc
  | d :: t, h => by
      obtain ⟨c, hc, hb⟩ := h
      have hnone : (digitVal b c).isSome = false := by
        rw [digitVal_eq_none_of_blank hr hb]; rfl
      cases hh : isDigits b (d :: t) with
      | false => rfl
      | true =>
          have hc' := (isDigits_iff (d :: t)).1 hh c hc
          rw [hnone] at hc'
          exact absurd hc' (by simp)

/-! ### The three laws -/

/-- **A trailing blank is rejected.** `spec.md`: `"7 "` is not a numeral. -/
theorem trailing_blank_rejected {b : Nat} (hr : IsRadix b) (t : List UInt8) {c : UInt8}
    (hb : isBlank c = true) : trimFor b (t ++ [c]) = none := by
  unfold trimFor
  by_cases hs : strip b (t ++ [c]) = []
  · rw [ite_eq_left hs]
    rw [ite_eq_right (by rw [not_zeroSpelling_append_blank t c hb]; simp)]
  · rw [ite_eq_right hs]
    rcases strip_append_blank t c hb with h | h
    · exact absurd h hs
    · rw [ite_eq_right (by rw [isDigits_false_of_mem_blank hr h]; simp)]

/-- **An out-of-alphabet digit is rejected.** `spec.md`: `"9"` in radix 8. -/
theorem out_of_alphabet_rejected {b : Nat} (hr : IsRadix b) {c : UInt8}
    (h : digitVal b c = none) : trimFor b [c] = none := by
  have hns : (digitVal b c).isSome = false := by rw [h]; rfl
  unfold trimFor
  rcases strip_singleton (b := b) (c := c) with hs | hs
  · rw [ite_eq_left hs]
    have hz : isZeroSpelling b [c] = false := by
      cases hz2 : isZeroSpelling b [c] with
      | false => rfl
      | true =>
          have hmax : isBlank c = true ∨ isZeroZeros b [c] = true := by
            by_cases hb : isBlank c = true
            · exact Or.inl hb
            · exact Or.inr (by
                rw [← isZeroSpelling_cons_zeros (bool_eq_false_of_ne_true hb)]
                exact hz2)
          rcases hmax with hb | hzz
          · rw [isZeroSpelling_cons_blank hb] at hz2
            rw [isZeroSpelling_nil b] at hz2
            exact absurd hz2 (by simp)
          · have hzd : isZeroDigit b c = true := (isZeroZeros_cons.1 hzz).1
            rw [show digitVal b c = some 0 from isZeroDigit_zero_val hr hzd] at h
            exact absurd h (by simp)
    rw [ite_eq_right (by rw [hz]; simp)]
  · rw [ite_eq_right (by rw [hs]; simp)]
    have hf : isDigits b (strip b [c]) = false := by
      rw [hs]
      show ((digitVal b c).isSome && isDigits b []) = false
      rw [hns]
      rfl
    rw [ite_eq_right (by rw [hf]; simp)]

/-- **Trailing data after a valid numeral is rejected.** `spec.md`: `"7x"`.

The off-alphabet byte is neither absorbed by `strip` nor accepted by `isDigits`:
`not_blank_not_zero_of_no_digit` says so, and `strip_append_keep` says `strip` cannot delete
it. -/
theorem trailing_data_rejected {b : Nat} (hr : IsRadix b) (t : List UInt8) {c : UInt8}
    (hb0 : isBlank c = false) (hc : (digitVal b c).isSome = false) :
    trimFor b (t ++ [c]) = none := by
  have hz0 : isZeroDigit b c = false := by
    cases hz : isZeroDigit b c with
    | false => rfl
    | true =>
        have hnc : (digitVal b c).isSome = false := hc
        rw [show digitVal b c = some 0 from isZeroDigit_zero_val hr hz,
            Option.isSome_some] at hnc
        exact absurd hnc (by simp)
  have hstrip := strip_append_keep t hb0 hz0
  unfold trimFor
  by_cases hs : strip b (t ++ [c]) = []
  · rw [ite_eq_left hs]
    have hns : isZeroSpelling b (t ++ [c]) = false := by
      cases hz : isZeroSpelling b (t ++ [c]) with
      | false => rfl
      | true =>
          -- a zero spelling's bytes are all blanks or zero digits; `c` is neither
          have hall := strip_nil_all' b hz c (List.mem_append_right _ (by simp))
          rcases hall with hb' | hz'
          · rw [hb0] at hb'; exact absurd hb' (by simp)
          · rw [hz0] at hz'; exact absurd hz' (by simp)
    rw [ite_eq_right (by rw [hns]; simp)]
  · rw [ite_eq_right hs]
    have hf : isDigits b (strip b (t ++ [c])) = false := by
      rw [hstrip]
      cases hh : isDigits b (strip b t ++ [c]) with
      | false => rfl
      | true =>
          have hlast := (isDigits_iff (strip b t ++ [c])).1 hh c
            (List.mem_append_right _ (by simp))
          rw [hc] at hlast
          exact absurd hlast (by simp)
    rw [ite_eq_right (by rw [hf]; simp)]

end BaseN.RadixCodec
