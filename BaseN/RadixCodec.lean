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

/-! ## `trimFor` — the normaliser -/

/-- `trimFor b ds` — the canonical numeral for the lax spelling `ds`, or `none` if `ds`
names no number.

`some` on: leading blanks, an optional run of leading zero digits, then a non-empty
run of digits, and nothing else. `none` on everything else — a trailing blank, an
out-of-alphabet byte, trailing data after a numeral, the empty input, and an input of
blanks only.

The all-zero case is the delicate one: `"000"` and `"  0"` are spellings of zero and
must reach `ofNat b 0`, while `""` and `"   "` are not spellings of anything. The test
is `digitTail` being empty (so every remaining byte was a zero digit) **and** at least
one byte surviving `dropWhile isBlank` (so a digit was actually written). -/
def trimFor (b : Nat) (ds : List UInt8) : Option (List UInt8) :=
  let rest := ds.dropWhile isBlank
  let t := digitTail b rest
  if t.isEmpty then
    (if rest.isEmpty then none
     else if isDigits b rest then some (ofNat b 0) else none)
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

end BaseN.RadixCodec
