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
    (if ds = [] then none
     else if isDigits b ds then some (ofNat b 0) else none)
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

/-- A zero-digit byte is never a blank. -/
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
    rw [ite_eq_left hz, ite_eq_right (ofNat_zero_ne_nil b),
        ite_eq_left (ofNat_isDigits hr)]
  · have hs : strip b (ofNat b n) = ofNat b n := strip_ofNat hr hn
    rw [ite_eq_right (by rw [hs]; exact ofNat_ne_nil hr hn), hs,
        ite_eq_left (ofNat_isDigits hr)]

/-- **`trimFor` is idempotent on its image** — the `Codec.Normalizer` law. -/
theorem trimFor_idem {b : Nat} (hr : IsRadix b) {ds t : List UInt8}
    (h : trimFor b ds = some t) : trimFor b t = some t := by
  unfold trimFor at h ⊢
  by_cases hs : strip b ds = []
  · rw [ite_eq_left hs] at h
    by_cases hd0 : ds = []
    · rw [ite_eq_left hd0] at h; simp at h
    · rw [ite_eq_right hd0] at h
      by_cases hd : isDigits b ds = true
      · rw [ite_eq_left hd] at h
        rw [← Option.some.inj h]
        have hz : strip b (ofNat b 0) = [] := by
          rw [ofNat_zero_eq]
          apply strip_skip
          right
          have h : isZeroDigit b (byteOfDigit b 0) = true := by
            have := isZeroDigit_ofNat_zero b
            rw [ofNat_zero_eq] at this
            simpa using this
          exact h
        rw [ite_eq_left hz, ite_eq_right (ofNat_zero_ne_nil b),
            ite_eq_left (ofNat_isDigits hr)]
      · rw [ite_eq_right hd] at h; simp at h
  · rw [ite_eq_right hs] at h
    by_cases hd : isDigits b (strip b ds) = true
    · rw [ite_eq_left hd] at h
      have hst : strip b (strip b ds) = strip b ds := strip_idem b ds
      rw [← Option.some.inj h, hst, ite_eq_right hs, hd]
      rfl
    · rw [ite_eq_right hd] at h; simp at h


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

end BaseN.RadixCodec
