import Lake
open Lake DSL
open System

/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

package basen

require codec from git "https://github.com/dysinger/lean-codec.git" @ "master"

@[default_target]
lean_lib basen where
  roots := #[`BaseN]

lean_exe bench where
  root := `Bench
