/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# BaseN.Radix — the radix-generic numeral layer

`basen` decodes text to `List UInt8` and, before this module, never to a number.
Each base hard-codes its own way of packing digits **within one block**, and the
value never exists as a `Nat`. This module supplies the missing rung for all
seven radices at once:

  * `digitVal (radix : Nat) (b : UInt8) : Option Nat` — one digit byte to its
    digit value, or `none` if the byte is not in that radix's alphabet;
  * `toNat (radix : Nat) (ds : List UInt8) : Option Nat` — the
    most-significant-first fold `acc := acc * radix + d`;
  * `ofNat (radix : Nat) (n : Nat) : List UInt8` — canonical, minimal-width
    digits (no leading zeros; the radix's single zero digit for `0`).

`toNat` is **not** total: it is `Option`-valued and yields `none` on any byte
outside the alphabet, *without partially converting* the prefix before it.
`ofNat` **is** total.

## Alphabets

`digitVal` recognises exactly the alphabets `basen` already uses, at radix `b`:

| radix | alphabet                      | existing per-base function |
| ----- | ----------------------------- | -------------------------- |
| 2     | `0`/`1` (ASCII 48–49)         | `Base2.bitVal`             |
| 4     | `0`–`3` (ASCII 48–51)         | `Base4.quartetVal`         |
| 8     | `0`–`7` (ASCII 48–55)         | `Base8.octToVal`           |
| 10    | `0`–`9` (ASCII 48–57)         | `Base10.digVal`            |
| 16    | `0`–`9`, `A`–`F` (uppercase)  | `Base16.hexToNibble`       |
| 32    | `A`–`Z`, `2`–`7` (RFC 4648 §6) | `Base32.b32ToVal`         |
| 64    | `A`–`Z`, `a`–`z`, `0`–`9`, `+`, `/` (RFC 4648 §4) | `Base64.b64ToVal` |

Each of those seven is proved equal to `digitVal` at its radix — see
`BaseN.RadixAlphabets` — so no base carries an independent alphabet definition
that could disagree with this one. The **encode** direction is deliberately not
unified: `Base2.valToBit` carries a non-injective sentinel fallback documented in
that module, and `ofNat` here is this layer's own encoder.

## What this module does NOT do

`numeralIso` is **minimal-width** and does not go through the padded bases'
`B32`/`B64` terminal-tail spine. Padding there encodes a *length class*; a
minimal-width numeral has none. Reading a padded base-32/base-64 encoding as a
number is a different object and a separate composition.

`digitVal`/`toNat`/`ofNat` are **numeral helpers layered above** the per-base
`Codec` values, not a `Codec`-level dispatch: no `Base` enum is introduced and the
radix parameter of these functions does not replace `Codec.decode`'s uniform
surface (see `BaseN.lean`'s design note).

Every law here is `[propext, Quot.sound]`-only, stdlib-only.
-/

namespace BaseN.Radix

/-! ## The window predicate

Every `basen` alphabet is a union of ASCII code windows, which is what makes one
generic `digitVal` a *faithful* substitute for the seven hand-rolled ones rather
than an approximation of them. `lo ≤ c ≤ hi` is the only shape needed. -/

/-- `inWin lo hi c` — `c` lies in the closed ASCII window `[lo, hi]`. -/
def inWin (lo hi c : Nat) : Bool := decide (lo ≤ c ∧ c ≤ hi)

theorem inWin_eq_true {lo hi c : Nat} (h : inWin lo hi c = true) : lo ≤ c ∧ c ≤ hi :=
  of_decide_eq_true h

theorem inWin_eq_false {lo hi c : Nat} (h : ¬ (lo ≤ c ∧ c ≤ hi)) : inWin lo hi c = false := by
  unfold inWin
  exact decide_eq_false h

/-! ## `digitVal` — one digit byte to its digit value -/

/-- `digitVal radix b` — the digit value of the byte `b` in the given radix, or
`none` if `b` is not in that radix's alphabet.

The radix is a *parameter*, not a case split on seven alphabets: each arm is one
window of the radix's alphabet, and radices 2/4/8 all read their digits from the
`0`–`9` window with a radix bound. The seven per-base digit-value functions are
proved equal to this one at their radix (`BaseN.RadixAlphabets`).

`2 ≤ radix` is a hypothesis on everything that *uses* the layer; `digitVal` itself
is total, and a radix below 2 simply admits only the `0`/`1` window (or, at
radix 0 or 1, no digit at all), which is a caller error rather than a silent
misbehaviour. -/
def digitVal (radix : Nat) (b : UInt8) : Option Nat :=
  let c := b.toNat
  if radix = 2 then
    (if inWin 48 49 c then some (c - 48) else none)
  else if radix = 4 then
    (if inWin 48 51 c then some (c - 48) else none)
  else if radix = 8 then
    (if inWin 48 55 c then some (c - 48) else none)
  else if radix = 10 then
    (if inWin 48 57 c then some (c - 48) else none)
  else if radix = 16 then
    (if inWin 48 57 c then some (c - 48)
     else if inWin 65 70 c then some (c - 55) else none)
  else if radix = 32 then
    (if inWin 65 90 c then some (c - 65)
     else if inWin 50 55 c then some (c - 50 + 26) else none)
  else if radix = 64 then
    (if inWin 65 90 c then some (c - 65)
     else if inWin 97 122 c then some (c - 97 + 26)
     else if inWin 48 57 c then some (c - 48 + 52)
     else if c = 43 then some 62
     else if c = 47 then some 63 else none)
  else none

/-- `digitVal`'s `if`-chain, restated as one equation so proofs can `rw` it and then
case on each condition with `ite_eq_left`/`ite_eq_right`. -/
theorem digitVal_eq (r : Nat) (b : UInt8) : digitVal r b =
    (let c := b.toNat
     if r = 2 then (if inWin 48 49 c then some (c - 48) else none)
     else if r = 4 then (if inWin 48 51 c then some (c - 48) else none)
     else if r = 8 then (if inWin 48 55 c then some (c - 48) else none)
     else if r = 10 then (if inWin 48 57 c then some (c - 48) else none)
     else if r = 16 then
       (if inWin 48 57 c then some (c - 48)
        else if inWin 65 70 c then some (c - 55) else none)
     else if r = 32 then
       (if inWin 65 90 c then some (c - 65)
        else if inWin 50 55 c then some (c - 50 + 26) else none)
     else if r = 64 then
       (if inWin 65 90 c then some (c - 65)
        else if inWin 97 122 c then some (c - 97 + 26)
        else if inWin 48 57 c then some (c - 48 + 52)
        else if c = 43 then some 62
        else if c = 47 then some 63 else none)
     else none) := rfl

/-- `inWin` is exactly the interval. -/
theorem inWin_iff {lo hi c : Nat} : inWin lo hi c = true ↔ lo ≤ c ∧ c ≤ hi :=
  ⟨inWin_eq_true, fun h => by unfold inWin; exact decide_eq_true h⟩

/-! ## `toNat` — the fold

`toNat` is a **structural** right fold over the digit list, not a `List.foldl` over
an `Option` accumulator. That is a deliberate proof-engineering choice, and the
reason is `AGENTS.md`'s: a `foldl` over an opaque accumulator does not reduce at a
variable list, so every downstream equation would need an accumulator lemma before
the first `cons` case could fire. A right fold's `cons` equation is `rfl`. -/

/-- `toNat radix ds` — the number the digit sequence `ds` denotes in the given
radix, most significant digit first: `Σ dᵢ · radixⁱ`.

`none` on any byte outside the radix's alphabet, and **not** a partial result:
`none` anywhere in the sequence makes the whole conversion `none`.

`toNat radix [] = some 0` is a by-product of the fold's base case; it is **not**
the canonical spelling of zero and no theorem in this layer claims the empty
sequence is a numeral. `ofNat` spells zero as the radix's single zero digit. -/
def toNat (radix : Nat) : List UInt8 → Option Nat
  | [] => some 0
  | d :: ds =>
      ((digitVal radix d).map
        (fun v => (toNat radix ds).map (fun a => v * radix ^ ds.length + a))).bind id

/-- `toNat` on a cons whose head digit is `v`: the head's value is folded into the
tail's. The form the `Iso` needs, and `rfl`-adjacent by construction. -/
theorem toNat_cons_some (radix : Nat) (d : UInt8) (ds : List UInt8) (v : Nat)
    (h : digitVal radix d = some v) :
    toNat radix (d :: ds) = (toNat radix ds).map (fun a => v * radix ^ ds.length + a) := by
  show ((digitVal radix d).map (fun v => (toNat radix ds).map (fun a => v * radix ^ ds.length + a))).bind id = _
  rw [h]
  rfl

/-- `toNat` on a cons whose head digit is out of the alphabet: `none`, with the
tail **not** partially converted. -/
theorem toNat_cons_none (radix : Nat) (d : UInt8) (ds : List UInt8)
    (h : digitVal radix d = none) : toNat radix (d :: ds) = none := by
  show ((digitVal radix d).map (fun v => (toNat radix ds).map (fun a => v * radix ^ ds.length + a))).bind id = _
  rw [h]
  rfl

/-! ## `ofNat` — canonical digits -/

/-- `natDigits radix m` — the digits of `m` in `radix`, most significant first.
`[]` exactly for `m = 0`.

Well-founded recursion: the recursive call is on `m / radix`, not a structurally
smaller subterm. The `2 ≤ radix` bound is discharged in `decreasing_by`; below it
no positional numeral exists and the function answers `[m]` so it stays total. -/
def natDigits (radix : Nat) (m : Nat) : List Nat :=
  if m = 0 then []
  else if radix < 2 then [m]
  else natDigits radix (m / radix) ++ [m % radix]
termination_by m
decreasing_by
  have hm : m ≠ 0 := by assumption
  exact Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by omega)

/-- `natVal radix ds` — the value of a `Nat`-digit list, most significant first.
The `Nat`-valued mirror of `toNat`, used to state `ofNat`'s correctness before the
byte alphabet enters. -/
def natVal (radix : Nat) : List Nat → Nat
  | [] => 0
  | v :: vs => v * radix ^ vs.length + natVal radix vs

/-- `byteOfDigit radix d` — the alphabet byte for digit value `d` in `radix`: the
inverse of `digitVal radix` on `d < radix`.

This **is** the generic encoder's alphabet, and it is per-radix because the
alphabets are. At radices 2/4/8/10 the byte is `48 + d` — the same shape as
`Base4.valToQuartet`, `Base8.valToOct` and `Base10.valToDig`. At 16 it is `48 + d`
for `d ≤ 9` and `55 + d` above, matching `Base16.nibbleToHex`. At 32 and 64 it is
the RFC 4648 alphabet, matching `Base32.valToB32` and `Base64.valToB64`.

An out-of-alphabet `d` answers `48` (`'0'`). That case is unreachable from `ofNat`:
`natDigits` only ever emits `d < radix`. It is a total fallback, not a silent
aliasing — the same discipline `Base2.valToBit`'s docstring records for its own
sentinel, and `ofNat` is this layer's own encoder rather than a claim that
`valToBit` is one of its copies. -/
def byteOfDigitNat (radix : Nat) (d : Nat) : Nat :=
  if radix = 32 then (if d ≤ 25 then 65 + d else 50 + d - 26)
  else if radix = 64 then
    (if d ≤ 25 then 65 + d
     else if d ≤ 51 then 97 + d - 26
     else if d ≤ 61 then 48 + d - 52
     else if d = 62 then 43 else 47)
  else if radix = 16 then (if d ≤ 9 then 48 + d else 55 + d)
  else 48 + d

/-- `byteOfDigit radix d` — the alphabet byte for digit value `d` in `radix`. -/
def byteOfDigit (radix : Nat) (d : Nat) : UInt8 :=
  UInt8.ofNat (byteOfDigitNat radix d)

/-- The `Nat` value of an alphabet byte is its `Nat` spelling. -/
theorem byteOfDigit_toNat (radix : Nat) (d : Nat) :
    (byteOfDigit radix d).toNat = byteOfDigitNat radix d % 256 := by
  unfold byteOfDigit
  rw [UInt8.toNat_ofNat']

/-! ### Alphabet facts -/

/-- `byteOfDigitNat` is a plain `if`-chain; this restates it as one equation so
every proof below can `rw` it and then `split_ifs` on a *literal* condition list. -/
theorem byteOfDigitNat_eq (r d : Nat) : byteOfDigitNat r d =
    (if r = 32 then (if d ≤ 25 then 65 + d else 50 + d - 26)
     else if r = 64 then
       (if d ≤ 25 then 65 + d
        else if d ≤ 51 then 97 + d - 26
        else if d ≤ 61 then 48 + d - 52
        else if d = 62 then 43 else 47)
     else if r = 16 then (if d ≤ 9 then 48 + d else 55 + d)
     else 48 + d) := rfl

/-- Every alphabet byte is ASCII: `byteOfDigitNat` in range is below 256, so the
`UInt8` embedding is exact. -/
theorem byteOfDigitNat_lt (radix : Nat) (hd2 : 2 ≤ radix) (hd64 : radix ≤ 64) (d : Nat)
    (hd : d < radix) : byteOfDigitNat radix d < 256 := by
  rw [byteOfDigitNat_eq]
  by_cases h1 : radix = 32
  · rw [ite_eq_left h1]
    by_cases h2 : d ≤ 25
    · rw [ite_eq_left h2]; omega
    · rw [ite_eq_right h2]; omega
  · rw [ite_eq_right h1]
    by_cases h3 : radix = 64
    · rw [ite_eq_left h3]
      by_cases h4 : d ≤ 25
      · rw [ite_eq_left h4]; omega
      · rw [ite_eq_right h4]
        by_cases h5 : d ≤ 51
        · rw [ite_eq_left h5]; omega
        · rw [ite_eq_right h5]
          by_cases h6 : d ≤ 61
          · rw [ite_eq_left h6]; omega
          · rw [ite_eq_right h6]
            by_cases h7 : d = 62
            · rw [ite_eq_left h7]; omega
            · rw [ite_eq_right h7]; omega
    · rw [ite_eq_right h3]
      by_cases h8 : radix = 16
      · rw [ite_eq_left h8]
        by_cases h9 : d ≤ 9
        · rw [ite_eq_left h9]; omega
        · rw [ite_eq_right h9]; omega
      · rw [ite_eq_right h8]; omega

/-- The `Nat` value of an in-range alphabet byte is its `Nat` spelling, exactly (no
modulus), because the spelling is already below 256. -/
theorem byteOfDigit_toNat_eq (radix : Nat) (hd2 : 2 ≤ radix) (hd64 : radix ≤ 64) (d : Nat)
    (hd : d < radix) : (byteOfDigit radix d).toNat = byteOfDigitNat radix d := by
  rw [byteOfDigit_toNat, Nat.mod_eq_of_lt (byteOfDigitNat_lt radix hd2 hd64 d hd)]



/-! ### The alphabet round trip, at each of the seven radices

`digitVal b (byteOfDigit b d) = some d` for `d < b`. This is what makes `ofNat`'s
output readable by `toNat`, and it is proved per radix because each alphabet has
its own windows — a single generic proof would have to case on the radix anyway. -/


set_option maxHeartbeats 2000000 in
/-- The alphabet round trip at radix 2: `digitVal` recovers every digit
`byteOfDigit` emits, so `ofNat`'s output is readable by `toNat`. -/
theorem digitVal_byteOfDigit_2 (d : Nat) (hd : d < 2) :
    digitVal 2 (byteOfDigit 2 d) = some d := by
  have hb := byteOfDigitNat_lt 2 (by omega) (by omega) d hd
  have bc : byteOfDigitNat 2 d = (48 + d) := by
    rw [byteOfDigitNat_eq]
    rw [ite_eq_right (by decide : ¬ ((2:Nat) = 32)), ite_eq_right (by decide : ¬ ((2:Nat) = 64)), ite_eq_right (by decide : ¬ ((2:Nat) = 16))]
  have hbt : (byteOfDigit 2 d).toNat = (48 + d) := by
    rw [byteOfDigit_toNat, Nat.mod_eq_of_lt hb, bc]
  rw [digitVal_eq]
  dsimp only
  rw [ite_eq_left (by decide : (2:Nat) = 2)]
  rw [hbt]
  rw [show inWin 48 49 (48 + d) = true from inWin_iff.2 ⟨by omega, by omega⟩]
  rw [ite_eq_left rfl]; congr 1; omega

set_option maxHeartbeats 2000000 in
/-- The alphabet round trip at radix 4: `digitVal` recovers every digit
`byteOfDigit` emits, so `ofNat`'s output is readable by `toNat`. -/
theorem digitVal_byteOfDigit_4 (d : Nat) (hd : d < 4) :
    digitVal 4 (byteOfDigit 4 d) = some d := by
  have hb := byteOfDigitNat_lt 4 (by omega) (by omega) d hd
  have bc : byteOfDigitNat 4 d = (48 + d) := by
    rw [byteOfDigitNat_eq]
    rw [ite_eq_right (by decide : ¬ ((4:Nat) = 32)), ite_eq_right (by decide : ¬ ((4:Nat) = 64)), ite_eq_right (by decide : ¬ ((4:Nat) = 16))]
  have hbt : (byteOfDigit 4 d).toNat = (48 + d) := by
    rw [byteOfDigit_toNat, Nat.mod_eq_of_lt hb, bc]
  rw [digitVal_eq]
  dsimp only
  rw [ite_eq_right (by decide : ¬ ((4:Nat) = 2)),
      ite_eq_left (by decide : (4:Nat) = 4)]
  rw [hbt]
  rw [show inWin 48 51 (48 + d) = true from inWin_iff.2 ⟨by omega, by omega⟩]
  rw [ite_eq_left rfl]; congr 1; omega

set_option maxHeartbeats 2000000 in
/-- The alphabet round trip at radix 8: `digitVal` recovers every digit
`byteOfDigit` emits, so `ofNat`'s output is readable by `toNat`. -/
theorem digitVal_byteOfDigit_8 (d : Nat) (hd : d < 8) :
    digitVal 8 (byteOfDigit 8 d) = some d := by
  have hb := byteOfDigitNat_lt 8 (by omega) (by omega) d hd
  have bc : byteOfDigitNat 8 d = (48 + d) := by
    rw [byteOfDigitNat_eq]
    rw [ite_eq_right (by decide : ¬ ((8:Nat) = 32)), ite_eq_right (by decide : ¬ ((8:Nat) = 64)), ite_eq_right (by decide : ¬ ((8:Nat) = 16))]
  have hbt : (byteOfDigit 8 d).toNat = (48 + d) := by
    rw [byteOfDigit_toNat, Nat.mod_eq_of_lt hb, bc]
  rw [digitVal_eq]
  dsimp only
  rw [ite_eq_right (by decide : ¬ ((8:Nat) = 2)),
      ite_eq_right (by decide : ¬ ((8:Nat) = 4)),
      ite_eq_left (by decide : (8:Nat) = 8)]
  rw [hbt]
  rw [show inWin 48 55 (48 + d) = true from inWin_iff.2 ⟨by omega, by omega⟩]
  rw [ite_eq_left rfl]; congr 1; omega

set_option maxHeartbeats 2000000 in
/-- The alphabet round trip at radix 10: `digitVal` recovers every digit
`byteOfDigit` emits, so `ofNat`'s output is readable by `toNat`. -/
theorem digitVal_byteOfDigit_10 (d : Nat) (hd : d < 10) :
    digitVal 10 (byteOfDigit 10 d) = some d := by
  have hb := byteOfDigitNat_lt 10 (by omega) (by omega) d hd
  have bc : byteOfDigitNat 10 d = (48 + d) := by
    rw [byteOfDigitNat_eq]
    rw [ite_eq_right (by decide : ¬ ((10:Nat) = 32)), ite_eq_right (by decide : ¬ ((10:Nat) = 64)), ite_eq_right (by decide : ¬ ((10:Nat) = 16))]
  have hbt : (byteOfDigit 10 d).toNat = (48 + d) := by
    rw [byteOfDigit_toNat, Nat.mod_eq_of_lt hb, bc]
  rw [digitVal_eq]
  dsimp only
  rw [ite_eq_right (by decide : ¬ ((10:Nat) = 2)),
      ite_eq_right (by decide : ¬ ((10:Nat) = 4)),
      ite_eq_right (by decide : ¬ ((10:Nat) = 8)),
      ite_eq_left (by decide : (10:Nat) = 10)]
  rw [hbt]
  rw [show inWin 48 57 (48 + d) = true from inWin_iff.2 ⟨by omega, by omega⟩]
  rw [ite_eq_left rfl]; congr 1; omega

set_option maxHeartbeats 2000000 in
/-- The alphabet round trip at radix 16: `digitVal` recovers every digit
`byteOfDigit` emits, so `ofNat`'s output is readable by `toNat`. -/
theorem digitVal_byteOfDigit_16 (d : Nat) (hd : d < 16) :
    digitVal 16 (byteOfDigit 16 d) = some d := by
  have hb := byteOfDigitNat_lt 16 (by omega) (by omega) d hd
  have bc : byteOfDigitNat 16 d = (if d ≤ 9 then 48 + d else 55 + d) := by
    rw [byteOfDigitNat_eq]
    rw [ite_eq_right (by decide : ¬ ((16:Nat) = 32)), ite_eq_right (by decide : ¬ ((16:Nat) = 64)), ite_eq_left (by decide : (16:Nat) = 16)]
  have hbt : (byteOfDigit 16 d).toNat = (if d ≤ 9 then 48 + d else 55 + d) := by
    rw [byteOfDigit_toNat, Nat.mod_eq_of_lt hb, bc]
  rw [digitVal_eq]
  dsimp only
  rw [ite_eq_right (by decide : ¬ ((16:Nat) = 2)),
      ite_eq_right (by decide : ¬ ((16:Nat) = 4)),
      ite_eq_right (by decide : ¬ ((16:Nat) = 8)),
      ite_eq_right (by decide : ¬ ((16:Nat) = 10)),
      ite_eq_left (by decide : (16:Nat) = 16)]
  rw [hbt]
  by_cases hd9 : d ≤ 9
  · rw [ite_eq_left hd9]
    rw [show inWin 48 57 (48 + d) = true from inWin_iff.2 ⟨by omega, by omega⟩]
    rw [ite_eq_left rfl]; congr 1; omega
  · rw [ite_eq_right hd9]
    rw [ite_eq_right (show ¬ (inWin 48 57 ((55 + d)) = true) from by

      rw [show inWin 48 57 ((55 + d)) = false from inWin_eq_false (by omega)]

      decide)]
    rw [show inWin 65 70 (55 + d) = true from inWin_iff.2 ⟨by omega, by omega⟩]
    rw [ite_eq_left rfl]; congr 1; omega

set_option maxHeartbeats 2000000 in
/-- The alphabet round trip at radix 32: `digitVal` recovers every digit
`byteOfDigit` emits, so `ofNat`'s output is readable by `toNat`. -/
theorem digitVal_byteOfDigit_32 (d : Nat) (hd : d < 32) :
    digitVal 32 (byteOfDigit 32 d) = some d := by
  have hb := byteOfDigitNat_lt 32 (by omega) (by omega) d hd
  have bc : byteOfDigitNat 32 d = (if d ≤ 25 then 65 + d else 50 + d - 26) := by
    rw [byteOfDigitNat_eq]
    rw [ite_eq_left (by decide : (32:Nat) = 32)]
  have hbt : (byteOfDigit 32 d).toNat = (if d ≤ 25 then 65 + d else 50 + d - 26) := by
    rw [byteOfDigit_toNat, Nat.mod_eq_of_lt hb, bc]
  rw [digitVal_eq]
  dsimp only
  rw [ite_eq_right (by decide : ¬ ((32:Nat) = 2)),
      ite_eq_right (by decide : ¬ ((32:Nat) = 4)),
      ite_eq_right (by decide : ¬ ((32:Nat) = 8)),
      ite_eq_right (by decide : ¬ ((32:Nat) = 10)),
      ite_eq_right (by decide : ¬ ((32:Nat) = 16)),
      ite_eq_left (by decide : (32:Nat) = 32)]
  rw [hbt]
  by_cases hd25 : d ≤ 25
  · rw [ite_eq_left hd25]
    rw [show inWin 65 90 (65 + d) = true from inWin_iff.2 ⟨by omega, by omega⟩]
    rw [ite_eq_left rfl]; congr 1; omega
  · rw [ite_eq_right hd25]
    rw [ite_eq_right (show ¬ (inWin 65 90 ((50 + d - 26)) = true) from by

      rw [show inWin 65 90 ((50 + d - 26)) = false from inWin_eq_false (by omega)]

      decide)]
    rw [show inWin 50 55 (50 + d - 26) = true from inWin_iff.2 ⟨by omega, by omega⟩]
    rw [ite_eq_left rfl]; congr 1; omega

set_option maxHeartbeats 4000000 in
/-- The alphabet round trip at radix 64.

The block's `apply` has four nested windows, so the proof first emits the concrete
character as an *opaque* value via a case split on `d`, and then checks `digitVal`'s
window chain against that character. Reducing `byteOfDigitNat` to the arm expression
and leaving the `if`s in place does not work: `omega` cannot see through them. -/
theorem digitVal_byteOfDigit_64 (d : Nat) (hd : d < 64) :
    digitVal 64 (byteOfDigit 64 d) = some d := by
  have hb := byteOfDigitNat_lt 64 (by omega) (by omega) d hd
  have hbt : (byteOfDigit 64 d).toNat = byteOfDigitNat 64 d :=
    byteOfDigit_toNat_eq 64 (by omega) (by omega) d hd
  -- the concrete character, as an opaque `Nat`, chosen by which window `d` is in
  have hchar : ∃ c : Nat, byteOfDigitNat 64 d = c ∧
      ((inWin 65 90 c = true ∧ c - 65 = d) ∨
       (inWin 65 90 c = false ∧ inWin 97 122 c = true ∧ c - 97 + 26 = d) ∨
       (inWin 65 90 c = false ∧ inWin 97 122 c = false ∧ inWin 48 57 c = true ∧
          c - 48 + 52 = d) ∨
       (inWin 65 90 c = false ∧ inWin 97 122 c = false ∧ inWin 48 57 c = false ∧
          c = 43 ∧ d = 62) ∨
       (inWin 65 90 c = false ∧ inWin 97 122 c = false ∧ inWin 48 57 c = false ∧
          c ≠ 43 ∧ c = 47 ∧ d = 63)) := by
    rw [byteOfDigitNat_eq]
    rw [ite_eq_right (by decide : ¬ ((64:Nat) = 32)),
        ite_eq_left (by decide : (64:Nat) = 64)]
    by_cases h1 : d ≤ 25
    · rw [ite_eq_left h1]
      exact ⟨65 + d, rfl, Or.inl ⟨inWin_iff.2 ⟨by omega, by omega⟩, by omega⟩⟩
    · rw [ite_eq_right h1]
      by_cases h2 : d ≤ 51
      · rw [ite_eq_left h2]
        exact ⟨97 + d - 26, rfl,
          Or.inr (Or.inl ⟨inWin_eq_false (by omega), inWin_iff.2 ⟨by omega, by omega⟩, by omega⟩)⟩
      · rw [ite_eq_right h2]
        by_cases h3 : d ≤ 61
        · rw [ite_eq_left h3]
          exact ⟨48 + d - 52, rfl, Or.inr (Or.inr (Or.inl
            ⟨inWin_eq_false (by omega), inWin_eq_false (by omega), inWin_iff.2 ⟨by omega, by omega⟩,
              by omega⟩))⟩
        · rw [ite_eq_right h3]
          by_cases h4 : d = 62
          · rw [ite_eq_left h4]
            exact ⟨43, rfl, Or.inr (Or.inr (Or.inr (Or.inl
              ⟨inWin_eq_false (by omega), inWin_eq_false (by omega),
                inWin_eq_false (by omega), rfl, by omega⟩)))⟩
          · rw [ite_eq_right h4]
            exact ⟨47, rfl, Or.inr (Or.inr (Or.inr (Or.inr
              ⟨inWin_eq_false (by omega), inWin_eq_false (by omega),
                inWin_eq_false (by omega), by omega, rfl, by omega⟩)))⟩
  obtain ⟨c, hc, hcases⟩ := hchar
  rw [digitVal_eq]
  dsimp only
  rw [hbt, hc]
  rw [ite_eq_right (by decide : ¬ ((64:Nat) = 2)),
      ite_eq_right (by decide : ¬ ((64:Nat) = 4)),
      ite_eq_right (by decide : ¬ ((64:Nat) = 8)),
      ite_eq_right (by decide : ¬ ((64:Nat) = 10)),
      ite_eq_right (by decide : ¬ ((64:Nat) = 16)),
      ite_eq_right (by decide : ¬ ((64:Nat) = 32)),
      ite_eq_left (by decide : (64:Nat) = 64)]
  rcases hcases with ⟨h65, hd65⟩ | ⟨h65, h97, hd97⟩ | ⟨h65, h97, h48, hd48⟩ |
    ⟨h65, h97, h48, h43, hd62⟩ | ⟨h65, h97, h48, h43, h47, hd63⟩
  · rw [ite_eq_left h65]; rw [hd65]
  · rw [ite_eq_right (show ¬ (inWin 65 90 c = true) from by rw [h65]; decide),
        ite_eq_left h97]; rw [hd97]
  · rw [ite_eq_right (show ¬ (inWin 65 90 c = true) from by rw [h65]; decide),
        ite_eq_right (show ¬ (inWin 97 122 c = true) from by rw [h97]; decide),
        ite_eq_left h48]; rw [hd48]
  · rw [ite_eq_right (show ¬ (inWin 65 90 c = true) from by rw [h65]; decide),
        ite_eq_right (show ¬ (inWin 97 122 c = true) from by rw [h97]; decide),
        ite_eq_right (show ¬ (inWin 48 57 c = true) from by rw [h48]; decide),
        ite_eq_left h43]; rw [hd62]
  · rw [ite_eq_right (show ¬ (inWin 65 90 c = true) from by rw [h65]; decide),
        ite_eq_right (show ¬ (inWin 97 122 c = true) from by rw [h97]; decide),
        ite_eq_right (show ¬ (inWin 48 57 c = true) from by rw [h48]; decide),
        ite_eq_right (show ¬ (c = 43) from h43),
        ite_eq_left h47]; rw [hd63]

/-- The alphabet round trip, dispatched over the seven radices: `isRadix r` names the
radices this layer serves. `digitVal` recovers every digit `byteOfDigit` emits, which
is what makes `ofNat`'s output readable by `toNat`. -/
inductive IsRadix : Nat → Prop
  | b2 : IsRadix 2
  | b4 : IsRadix 4
  | b8 : IsRadix 8
  | b10 : IsRadix 10
  | b16 : IsRadix 16
  | b32 : IsRadix 32
  | b64 : IsRadix 64

theorem isRadix_ge2 {r : Nat} (h : IsRadix r) : 2 ≤ r := by cases h <;> omega

theorem isRadix_le64 {r : Nat} (h : IsRadix r) : r ≤ 64 := by cases h <;> omega

/-- `digitVal` at an in-range digit of an alphabet this layer serves. -/
theorem digitVal_byteOfDigit {r : Nat} (hr : IsRadix r) (d : Nat) (hd : d < r) :
    digitVal r (byteOfDigit r d) = some d := by
  cases hr with
  | b2 => exact digitVal_byteOfDigit_2 d hd
  | b4 => exact digitVal_byteOfDigit_4 d hd
  | b8 => exact digitVal_byteOfDigit_8 d hd
  | b10 => exact digitVal_byteOfDigit_10 d hd
  | b16 => exact digitVal_byteOfDigit_16 d hd
  | b32 => exact digitVal_byteOfDigit_32 d hd
  | b64 => exact digitVal_byteOfDigit_64 d hd

/-- `natDigits`' recursion equation, at a radix this layer serves. -/
theorem natDigits_eq {radix : Nat} (hr : IsRadix radix) (m : Nat) (hm : m ≠ 0) :
    natDigits radix m = natDigits radix (m / radix) ++ [m % radix] := by
  rw [natDigits]
  have h2 : 2 ≤ radix := isRadix_ge2 hr
  simp only [hm, ite_false, Nat.not_lt.mpr h2]

/-- `natVal` splits over an append. -/
theorem natVal_append (radix : Nat) (xs ys : List Nat) :
    natVal radix (xs ++ ys) = natVal radix xs * radix ^ ys.length + natVal radix ys := by
  induction xs with
  | nil => simp [natVal]
  | cons x xs ih =>
      simp only [List.cons_append, natVal, List.length_append, ih]
      rw [Nat.pow_add, ← Nat.mul_assoc, Nat.add_mul, Nat.add_assoc]

/-- **`natDigits` is correct**: its digits denote `m`. -/
theorem natVal_natDigits {radix : Nat} (hr : IsRadix radix) (m : Nat) :
    natVal radix (natDigits radix m) = m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    by_cases hm : m = 0
    · subst hm; rw [natDigits]; simp [natVal]
    · rw [natDigits_eq hr m hm, natVal_append]
      have hlt : m / radix < m :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by have := isRadix_ge2 hr; omega)
      rw [ih (m / radix) hlt]
      simp only [natVal, List.length_singleton, Nat.pow_one, List.length_nil, Nat.pow_zero,
        Nat.mul_one, Nat.add_zero]
      rw [Nat.mul_comm (m / radix) radix, Nat.div_add_mod m radix]

/-- **`natDigits` is in range**: every digit is below the radix, which is what makes
`byteOfDigit` an alphabet character rather than a fallback. -/
theorem natDigits_lt {radix : Nat} (hr : IsRadix radix) (m : Nat) :
    ∀ d ∈ natDigits radix m, d < radix := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    by_cases hm : m = 0
    · subst hm; rw [natDigits]; intro d hd; simp at hd
    · rw [natDigits_eq hr m hm]
      intro d hd
      rw [List.mem_append] at hd
      rcases hd with hd | hd
      · exact ih (m / radix)
          (Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by have := isRadix_ge2 hr; omega)) d hd
      · simp only [List.mem_singleton] at hd
        subst hd
        exact Nat.mod_lt _ (by have := isRadix_ge2 hr; omega)

/-- `natDigits` is empty exactly at zero. -/
theorem natDigits_eq_nil {radix : Nat} (hr : IsRadix radix) (m : Nat) :
    natDigits radix m = [] ↔ m = 0 := by
  constructor
  · intro hl
    by_cases hm : m = 0
    · exact hm
    · rw [natDigits_eq hr m hm] at hl
      simp at hl
  · intro hm; subst hm; rw [natDigits]; simp

/-- **`toNat` of `natDigits`'s image**: the fold and the digit producer agree. -/
theorem toNat_map_byteOfDigit {radix : Nat} (hr : IsRadix radix) (ds : List Nat)
    (hds : ∀ d ∈ ds, d < radix) :
    toNat radix (ds.map (byteOfDigit radix)) = some (natVal radix ds) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      rw [List.map_cons, natVal]
      have hdl : d < radix := hds d (List.mem_cons_self ..)
      have htl : ∀ x ∈ ds, x < radix := fun x hx => hds x (List.mem_cons_of_mem _ hx)
      rw [toNat_cons_some radix _ _ d (digitVal_byteOfDigit hr d hdl), ih htl]
      simp

/-- `ofNat radix n` — the canonical, minimal-width numeral of `n` in the given
radix: no leading zeros, and `ofNat radix 0` is the radix's **single zero digit**
(`'0'`, ASCII 48) — never the empty sequence (design D4).

`natDigits` already returns the minimal digits and `[]` exactly for `0`, so the
only work `ofNat` does beyond mapping digits to bytes is the zero case. -/
def ofNat (radix : Nat) (n : Nat) : List UInt8 :=
  if n = 0 then [byteOfDigit radix 0]
  else (natDigits radix n).map (byteOfDigit radix)

/-! ## The round trip

`toNat ∘ ofNat = some` at every radix this layer serves, and `ofNat ∘ toNat` returns
the canonical form. Together these are the pair the `Iso` is built from. -/

/-- **`toNat` reads back what `ofNat` writes.** -/
theorem toNat_ofNat {radix : Nat} (hr : IsRadix radix) (n : Nat) :
    toNat radix (ofNat radix n) = some n := by
  unfold ofNat
  by_cases hn : n = 0
  · subst hn
    rw [ite_eq_left rfl]
    show toNat radix [byteOfDigit radix 0] = some 0
    rw [toNat_cons_some radix _ _ 0
      (digitVal_byteOfDigit hr 0 (by have := isRadix_ge2 hr; omega))]
    show (toNat radix []).map (fun a => 0 * radix ^ ([] : List UInt8).length + a) = some 0
    simp [toNat]
  · rw [ite_eq_right hn]
    rw [toNat_map_byteOfDigit hr _ (fun d hd => natDigits_lt hr n d hd), natVal_natDigits hr n]


/-- `natDigits` of a positive multiple of the radix ends in zero: the
division-remainder fact canonicity needs. -/
theorem natDigits_mul {radix : Nat} (hr : IsRadix radix) (m : Nat) (hm : m ≠ 0) :
    natDigits radix (radix * m) = natDigits radix m ++ [0] := by
  have h2 : 2 ≤ radix := isRadix_ge2 hr
  have hpos : 0 < radix := by omega
  have hmul : radix * m ≠ 0 := Nat.mul_ne_zero (by omega) hm
  rw [natDigits_eq hr (radix * m) hmul]
  rw [Nat.mul_div_right m hpos, Nat.mul_mod_right radix m]

/-- `natDigits` of a positive value is non-empty. -/
theorem natDigits_ne_nil {radix : Nat} (hr : IsRadix radix) (m : Nat) (hm : m ≠ 0) :
    natDigits radix m ≠ [] := by
  intro h
  exact hm ((natDigits_eq_nil hr m).1 h)

/-- **Digits are minimal**: `natDigits` has no leading zero for a positive value.

Induction on the value. The digits are the quotient's digits followed by
`m % radix`; when the quotient is zero the list is the single digit `m % radix = m`,
which is nonzero, and otherwise the head is the quotient's head, which the
induction hypothesis covers. -/
theorem natDigits_head_ne_zero {radix : Nat} (hr : IsRadix radix) (m : Nat) (hm : m ≠ 0) :
    (natDigits radix m).head? ≠ some 0 := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    have h2 : 2 ≤ radix := isRadix_ge2 hr
    have hlt : m / radix < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by omega)
    have hmod := Nat.mod_lt m (show 0 < radix by omega)
    rw [natDigits_eq hr m hm]
    by_cases hq : m / radix = 0
    · have hmlt : m < radix := by
        have := Nat.div_mul_le_self m radix
        rw [hq, Nat.zero_mul] at this
        -- `0 ≤ m` gives nothing; use `Nat.div_eq_of_lt`'s converse instead
        by_cases hlt' : m < radix
        · exact hlt'
        · exfalso
          have hge : radix ≤ m := by omega
          have : 0 < m / radix := Nat.div_pos hge (by omega)
          omega
      have hmodm : m % radix = m := Nat.mod_eq_of_lt hmlt
      have hz : natDigits radix 0 = ([] : List Nat) := by
        rw [natDigits]; exact ite_eq_left rfl
      rw [hq, hz]
      simp only [List.nil_append, List.head?_cons]
      rw [hmodm]
      simp only [ne_eq, Option.some.injEq]
      omega
    · have hne := ih (m / radix) hlt hq
      cases hh : natDigits radix (m / radix) with
      | nil => exact absurd hh (natDigits_ne_nil hr (m / radix) hq)
      | cons x xs =>
          rw [hh] at hne
          simp only [List.cons_append, List.head?_cons]
          rw [show (x :: xs) = natDigits radix (m / radix) from hh.symm] at *
          simpa using hne

/-- `byteOfDigit` is injective at in-range digits: two alphabet bytes that agree are
the same digit. -/
theorem byteOfDigit_inj {radix : Nat} (hr : IsRadix radix) {x y : Nat} (hx : x < radix)
    (hy : y < radix) (h : byteOfDigit radix x = byteOfDigit radix y) : x = y := by
  have hx' := digitVal_byteOfDigit hr x hx
  have hy' := digitVal_byteOfDigit hr y hy
  rw [h] at hx'
  rw [hy'] at hx'
  exact (Option.some.inj hx').symm

/-- **`ofNat` is minimal**: a positive value's numeral does not start with the zero
digit, which is what makes it the *canonical* spelling rather than merely *a*
spelling. -/
theorem ofNat_head_ne_zero {radix : Nat} (hr : IsRadix radix) (n : Nat) (hn : n ≠ 0) :
    (ofNat radix n).head? ≠ some (byteOfDigit radix 0) := by
  unfold ofNat
  rw [ite_eq_right hn]
  have h2 : 2 ≤ radix := isRadix_ge2 hr
  rcases hd : natDigits radix n with _ | ⟨x, xs⟩
  · exact absurd hd (natDigits_ne_nil hr n hn)
  · have hx : x ≠ 0 := by
      have := natDigits_head_ne_zero hr n hn
      rw [hd] at this
      simpa using this
    simp only [List.map_cons, List.head?_cons, ne_eq, Option.some.injEq]
    intro h
    -- `byteOfDigit` is injective where the digit is in range, and `x < radix`
    have hxr : x < radix := natDigits_lt hr n x (by rw [hd]; exact List.mem_cons_self ..)
    exact hx (byteOfDigit_inj hr hxr (by omega) h)

end BaseN.Radix
