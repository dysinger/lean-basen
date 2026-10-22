/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Combinators

/-!
# The `Bytes n ↔ List UInt8` substrate bridge

The `codec` substrate is `Bytes n := Fin n → UInt8`; the `basen` surface (and its
consumers, `Bench.lean` and the `BaseN` facade) is `List UInt8`.  This module
bridges the two: `decodeAll` materializes a whole finite `Bytes n` as a
`List UInt8` (via the `takeWhile`/`satisfy_many0` run scanner), and `encodeAll`
re-encodes a `List UInt8` back into a length-indexed `Bytes n`.

The bridge is the *always-true* run (`takeWhile (fun _ => true)`), so the
productivity witness is `satisfyConsumesByte` — no new proof, the inherited
`decodeTakeWhile_spec`/`encodeTakeWhile_rel` laws apply unchanged.
-/

namespace BaseN.Bridge

open Codec

/-- The always-true byte predicate: accept every byte. -/
def allBytes (_b : UInt8) : Bool := true

/-- Decode the whole finite `Bytes n` as a `List UInt8` (all-prefix enumeration
over the always-true run). -/
def decodeAll {n : Nat} (s : Bytes n) : List (List UInt8 × Suffix n) :=
  decodeTakeWhile allBytes s

/-- Encode a `List UInt8` back into a length-indexed `Bytes n`. -/
def encodeAll (bs : List UInt8) : Option (Sigma fun n => Bytes n) :=
  encodeTakeWhile allBytes bs

/-- Materialize a finite `Bytes n` as a `List UInt8` (the total, plain
conversion — no run scanner, no `Option`). -/
def bytesToList {n : Nat} (s : Bytes n) : List UInt8 :=
  List.ofFn s

/-- Lift a `List UInt8` into a length-indexed `Bytes (l.length)`. -/
def listToBytes (l : List UInt8) : Bytes l.length :=
  fun i => l[i]

end BaseN.Bridge
