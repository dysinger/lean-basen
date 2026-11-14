/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import BaseN.Radix
import BaseN.Base2
import BaseN.Base4
import BaseN.Base8
import BaseN.Base10
import BaseN.Base16
import BaseN.Base32
import BaseN.Base64

/-!
# BaseN.RadixAlphabets — the generic digit-value function against the seven copies

Each base carries its own `Nat → Nat` digit-value function with an out-of-range
sentinel (`2`, `4`, `8`, `10`, `16`, `32`, `64`). `BaseN.Radix` supplies **one**
radix-parameterised `digitVal : Nat → UInt8 → Option Nat`. This module proves the two
spellings agree, one theorem per radix:

> at a byte on the base's alphabet, `digitVal b c` is `some` of the base's own digit
> value, and the two agree

so no base carries an independent alphabet definition that could disagree with the
generic one.

**This is the decode direction only**, which is what the requirement asks for. The
encode direction is *not* unified: `Base2.valToBit`'s fallback is deliberately
non-injective (its own docstring records why), and `BaseN.Radix.ofNat` is that layer's
own encoder rather than a claim that `valToBit` is one of its copies.

The module is separate from `BaseN.Radix` because it needs the seven base modules while
`BaseN.Radix` is imported before them — one module would be a cycle.

Every law here is `[propext, Quot.sound]`-only.
-/

namespace BaseN.RadixAlphabets

open BaseN.Radix

/-! ## The seven agreements

Each proof is the same shape: `inWin lo hi c` is definitionally
`decide (lo ≤ c ∧ hi ≥ c)` (the `e`/`e1` lemmas below are `rfl`), so rewriting the
window tests to that form makes both sides case splits on the **same** propositions.
The base's own function is then reduced window by window.

The statement is the in-alphabet direction with the base's own validity predicate as
the hypothesis — `bitVal c ≤ 1`, `quartetVal c ≤ 3`, and so on. That is exactly the
domain on which the two can disagree, so it is the direction with content. -/

/-! ### Radix 2 — `bitVal` (`0`/`1`, sentinel `2`) -/

theorem digitVal_two (c : Nat) (hc : c < 256) (hv : BaseN.Base2.bitVal c ≤ 1) :
    digitVal 2 (UInt8.ofNat c) = some (BaseN.Base2.bitVal c) := by
  have h1 : c = 48 ∨ c = 49 := by
    unfold BaseN.Base2.bitVal at hv
    by_cases a : c = 48
    · exact Or.inl a
    · by_cases b : c = 49
      · exact Or.inr b
      · simp [a, b] at hv
  have e1 : inWin 48 49 c = decide (48 ≤ c ∧ c ≤ 49) := rfl
  rw [digitVal_eq]; dsimp only
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hc, e1]
  rw [ite_eq_left (by decide : (2:Nat) = 2)]
  rcases h1 with h | h
  · subst h
    rw [decide_eq_true (show 48 ≤ 48 ∧ 48 ≤ 49 from ⟨by omega, by omega⟩)]
    unfold BaseN.Base2.bitVal
    rw [ite_eq_left rfl]
    rfl
  · subst h
    rw [decide_eq_true (show 48 ≤ 49 ∧ 49 ≤ 49 from ⟨by omega, by omega⟩)]
    unfold BaseN.Base2.bitVal
    rw [ite_eq_right (by decide : ¬ (49 = 48)), ite_eq_left rfl]
    rfl

theorem digitVal_four (c : Nat) (hc : c < 256) (hv : BaseN.Base4.quartetVal c ≤ 3) :
    digitVal 4 (UInt8.ofNat c) = some (BaseN.Base4.quartetVal c) := by
  have h1 : 48 ≤ c ∧ c ≤ 51 := by
    unfold BaseN.Base4.quartetVal at hv
    by_cases a : c ≤ 51
    · simp only [a, ite_true] at hv
      by_cases b : 48 ≤ c
      · exact ⟨b, a⟩
      · simp only [b, ite_false] at hv
        omega
    · simp only [a, ite_false] at hv
      omega
  have e1 : inWin 48 51 c = decide (48 ≤ c ∧ c ≤ 51) := rfl
  rw [digitVal_eq]; dsimp only
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hc, e1]
  rw [ite_eq_right (by decide : ¬ ((4:Nat) = 2)), ite_eq_left (by decide : (4:Nat) = 4)]
  rw [decide_eq_true h1]
  unfold BaseN.Base4.quartetVal
  rw [ite_eq_left h1.2, ite_eq_left h1.1]
  rfl

-- radix 8

theorem digitVal_eight (c : Nat) (hc : c < 256) (hv : BaseN.Base8.octToVal c ≤ 7) :
    digitVal 8 (UInt8.ofNat c) = some (BaseN.Base8.octToVal c) := by
  have h1 : 48 ≤ c ∧ c ≤ 55 := by
    unfold BaseN.Base8.octToVal at hv
    by_cases a : c ≤ 55
    · simp only [a, ite_true] at hv
      by_cases b : 48 ≤ c
      · exact ⟨b, a⟩
      · simp only [b, ite_false] at hv
        omega
    · simp only [a, ite_false] at hv
      omega
  have e1 : inWin 48 55 c = decide (48 ≤ c ∧ c ≤ 55) := rfl
  rw [digitVal_eq]; dsimp only
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hc, e1]
  rw [ite_eq_right (by decide : ¬ ((8:Nat) = 2)),
      ite_eq_right (by decide : ¬ ((8:Nat) = 4)),
      ite_eq_left (by decide : (8:Nat) = 8)]
  rw [decide_eq_true h1]
  unfold BaseN.Base8.octToVal
  rw [ite_eq_left h1.2, ite_eq_left h1.1]
  rfl

-- radix 10

theorem digitVal_ten (c : Nat) (hc : c < 256) (hv : BaseN.Base10.digVal c ≤ 9) :
    digitVal 10 (UInt8.ofNat c) = some (BaseN.Base10.digVal c) := by
  have h1 : 48 ≤ c ∧ c ≤ 57 := by
    unfold BaseN.Base10.digVal at hv
    by_cases a : c ≤ 57
    · simp only [a, ite_true] at hv
      by_cases b : 48 ≤ c
      · exact ⟨b, a⟩
      · simp only [b, ite_false] at hv
        omega
    · simp only [a, ite_false] at hv
      omega
  have e1 : inWin 48 57 c = decide (48 ≤ c ∧ c ≤ 57) := rfl
  rw [digitVal_eq]; dsimp only
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hc, e1]
  rw [ite_eq_right (by decide : ¬ ((10:Nat) = 2)),
      ite_eq_right (by decide : ¬ ((10:Nat) = 4)),
      ite_eq_right (by decide : ¬ ((10:Nat) = 8)),
      ite_eq_left (by decide : (10:Nat) = 10)]
  rw [decide_eq_true h1]
  unfold BaseN.Base10.digVal
  rw [ite_eq_left h1.2, ite_eq_left h1.1]
  rfl

/-! ### Radix 16 — `hexToNibble` (uppercase only) -/

theorem digitVal_sixteen (c : Nat) (hc : c < 256) (hv : BaseN.Base16.hexToNibble c ≤ 15) :
    digitVal 16 (UInt8.ofNat c) = some (BaseN.Base16.hexToNibble c) := by
  have h1 : (48 ≤ c ∧ c ≤ 57) ∨ (65 ≤ c ∧ c ≤ 70) := by
    unfold BaseN.Base16.hexToNibble at hv
    by_cases a : c ≤ 57
    · simp only [a, ite_true] at hv
      by_cases b : 48 ≤ c
      · exact Or.inl ⟨b, a⟩
      · simp only [b, ite_false] at hv
        omega
    · simp only [a, ite_false] at hv
      by_cases b : c ≤ 70
      · simp only [b, ite_true] at hv
        by_cases d : 65 ≤ c
        · exact Or.inr ⟨d, b⟩
        · simp only [d, ite_false] at hv
          omega
      · simp only [b, ite_false] at hv
        omega
  have e1 : inWin 48 57 c = decide (48 ≤ c ∧ c ≤ 57) := rfl
  have e2 : inWin 65 70 c = decide (65 ≤ c ∧ c ≤ 70) := rfl
  rw [digitVal_eq]; dsimp only
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hc, e1, e2]
  rw [ite_eq_right (by decide : ¬ ((16:Nat) = 2)),
      ite_eq_right (by decide : ¬ ((16:Nat) = 4)),
      ite_eq_right (by decide : ¬ ((16:Nat) = 8)),
      ite_eq_right (by decide : ¬ ((16:Nat) = 10)),
      ite_eq_left (by decide : (16:Nat) = 16)]
  rcases h1 with ⟨hd, hd2⟩ | ⟨hu, hu2⟩
  · rw [decide_eq_true (show 48 ≤ c ∧ c ≤ 57 from ⟨hd, hd2⟩)]
    unfold BaseN.Base16.hexToNibble
    rw [ite_eq_left hd2, ite_eq_left hd]
    rfl
  · rw [decide_eq_false (show ¬ (48 ≤ c ∧ c ≤ 57) from by omega)]
    rw [decide_eq_true (show 65 ≤ c ∧ c ≤ 70 from ⟨hu, hu2⟩)]
    unfold BaseN.Base16.hexToNibble
    rw [ite_eq_right (by omega : ¬ c ≤ 57), ite_eq_left hu2, ite_eq_left hu]
    rfl

/-! ### Radix 32 — `b32ToVal` (RFC 4648 §6: `A`-`Z`, `2`-`7`) -/

theorem digitVal_thirtytwo (c : Nat) (hc : c < 256) (hv : BaseN.Base32.b32ToVal c ≤ 31) :
    digitVal 32 (UInt8.ofNat c) = some (BaseN.Base32.b32ToVal c) := by
  have h1 : (65 ≤ c ∧ c ≤ 90) ∨ (50 ≤ c ∧ c ≤ 55) := by
    unfold BaseN.Base32.b32ToVal at hv
    by_cases a : c ≤ 55
    · simp only [a, ite_true] at hv
      by_cases b : 50 ≤ c
      · exact Or.inr ⟨b, a⟩
      · simp [b] at hv
    · simp only [a, ite_false] at hv
      by_cases b : c ≤ 90
      · simp only [b, ite_true] at hv
        by_cases d : 65 ≤ c
        · exact Or.inl ⟨d, b⟩
        · simp [d] at hv
      · simp [b] at hv
  have e1 : inWin 65 90 c = decide (65 ≤ c ∧ c ≤ 90) := rfl
  have e2 : inWin 50 55 c = decide (50 ≤ c ∧ c ≤ 55) := rfl
  rw [digitVal_eq]; dsimp only
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hc, e1, e2]
  rw [ite_eq_right (by decide : ¬ ((32:Nat) = 2)),
      ite_eq_right (by decide : ¬ ((32:Nat) = 4)),
      ite_eq_right (by decide : ¬ ((32:Nat) = 8)),
      ite_eq_right (by decide : ¬ ((32:Nat) = 10)),
      ite_eq_right (by decide : ¬ ((32:Nat) = 16)),
      ite_eq_left (by decide : (32:Nat) = 32)]
  rcases h1 with ⟨hu, hu2⟩ | ⟨hd, hd2⟩
  · rw [decide_eq_true (show 65 ≤ c ∧ c ≤ 90 from ⟨hu, hu2⟩)]
    unfold BaseN.Base32.b32ToVal
    rw [ite_eq_right (by omega : ¬ c ≤ 55), ite_eq_left hu2, ite_eq_left hu]
    rfl
  · rw [decide_eq_false (show ¬ (65 ≤ c ∧ c ≤ 90) from by omega)]
    rw [decide_eq_true (show 50 ≤ c ∧ c ≤ 55 from ⟨hd, hd2⟩)]
    unfold BaseN.Base32.b32ToVal
    rw [ite_eq_left hd2, ite_eq_left hd]
    rfl

theorem b64_class (c : Nat) (hv : BaseN.Base64.b64ToVal c ≤ 63) :
    (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) ∨ (48 ≤ c ∧ c ≤ 57) ∨ c = 43 ∨ c = 47 := by
  unfold BaseN.Base64.b64ToVal at hv
  split at hv
  · rename_i hle90
    split at hv
    · rename_i hge65
      exact Or.inl ⟨hge65, hle90⟩
    · rename_i hn65
      split at hv
      · rename_i hle57
        split at hv
        · rename_i hge48
          exact Or.inr (Or.inr (Or.inl ⟨hge48, hle57⟩))
        · rename_i hn48
          split at hv
          · rename_i he43
            exact Or.inr (Or.inr (Or.inr (Or.inl he43)))
          · rename_i hne43
            split at hv
            · rename_i he47
              exact Or.inr (Or.inr (Or.inr (Or.inr he47)))
            · rename_i hne47
              omega
      · rename_i hn57
        omega
  · rename_i hn90
    split at hv
    · rename_i hge97
      split at hv
      · rename_i hle122
        exact Or.inr (Or.inl ⟨hge97, hle122⟩)
      · rename_i hn122
        omega
    · omega

theorem digitVal_sixtyfour (c : Nat) (hc : c < 256) (hv : BaseN.Base64.b64ToVal c ≤ 63) :
    digitVal 64 (UInt8.ofNat c) = some (BaseN.Base64.b64ToVal c) := by
  have h1 := b64_class c hv
  have e1 : inWin 65 90 c = decide (65 ≤ c ∧ c ≤ 90) := rfl
  have e2 : inWin 97 122 c = decide (97 ≤ c ∧ c ≤ 122) := rfl
  have e3 : inWin 48 57 c = decide (48 ≤ c ∧ c ≤ 57) := rfl
  rw [digitVal_eq]; dsimp only
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hc, e1, e2, e3]
  rw [ite_eq_right (by decide : ¬ ((64:Nat) = 2)),
      ite_eq_right (by decide : ¬ ((64:Nat) = 4)),
      ite_eq_right (by decide : ¬ ((64:Nat) = 8)),
      ite_eq_right (by decide : ¬ ((64:Nat) = 10)),
      ite_eq_right (by decide : ¬ ((64:Nat) = 16)),
      ite_eq_right (by decide : ¬ ((64:Nat) = 32)),
      ite_eq_left (by decide : (64:Nat) = 64)]
  rcases h1 with ⟨hu, hu2⟩ | ⟨hl, hl2⟩ | ⟨hd, hd2⟩ | h | h
  · rw [decide_eq_true (show 65 ≤ c ∧ c ≤ 90 from ⟨hu, hu2⟩)]
    unfold BaseN.Base64.b64ToVal
    rw [ite_eq_left hu2, ite_eq_left hu]
    rfl
  · rw [decide_eq_false (show ¬ (65 ≤ c ∧ c ≤ 90) from by omega)]
    rw [decide_eq_true (show 97 ≤ c ∧ c ≤ 122 from ⟨hl, hl2⟩)]
    unfold BaseN.Base64.b64ToVal
    rw [ite_eq_right (by omega : ¬ c ≤ 90), ite_eq_left hl2, ite_eq_left hl]
    rfl
  · rw [decide_eq_false (show ¬ (65 ≤ c ∧ c ≤ 90) from by omega)]
    rw [decide_eq_false (show ¬ (97 ≤ c ∧ c ≤ 122) from by omega)]
    rw [decide_eq_true (show 48 ≤ c ∧ c ≤ 57 from ⟨hd, hd2⟩)]
    unfold BaseN.Base64.b64ToVal
    rw [ite_eq_left (by omega : c ≤ 90), ite_eq_right (by omega : ¬ (65 ≤ c)),
        ite_eq_left hd2, ite_eq_left hd]
    rfl
  · rw [decide_eq_false (show ¬ (65 ≤ c ∧ c ≤ 90) from by omega)]
    rw [decide_eq_false (show ¬ (97 ≤ c ∧ c ≤ 122) from by omega)]
    rw [decide_eq_false (show ¬ (48 ≤ c ∧ c ≤ 57) from by omega)]
    unfold BaseN.Base64.b64ToVal
    rw [ite_eq_left (by omega : c ≤ 90), ite_eq_right (by omega : ¬ (65 ≤ c)),
        ite_eq_left (by omega : c ≤ 57), ite_eq_right (by omega : ¬ (48 ≤ c)),
        ite_eq_left h]
    simp only [Bool.false_eq_true, ite_false, h, ite_true]
  · rw [decide_eq_false (show ¬ (65 ≤ c ∧ c ≤ 90) from by omega)]
    rw [decide_eq_false (show ¬ (97 ≤ c ∧ c ≤ 122) from by omega)]
    rw [decide_eq_false (show ¬ (48 ≤ c ∧ c ≤ 57) from by omega)]
    unfold BaseN.Base64.b64ToVal
    rw [ite_eq_left (by omega : c ≤ 90), ite_eq_right (by omega : ¬ (65 ≤ c)),
        ite_eq_left (by omega : c ≤ 57), ite_eq_right (by omega : ¬ (48 ≤ c)),
        ite_eq_right (by omega : ¬ (c = 43)), ite_eq_left h]
    simp only [Bool.false_eq_true, ite_false, h, ite_true]
    rfl

end BaseN.RadixAlphabets
