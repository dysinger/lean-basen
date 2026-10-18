# Copyright 2026 Department of Code LLC.
# SPDX-License-Identifier: AGPL-3.0-or-later

# basen — a verified base-2/4/8/10/16/32/64 encoding library in Lean 4.
#
# Takes the Lean 4 toolchain (the `lean4` derivation) as concrete inputs — no
# `pkgs` blob, no overlay assumption — and returns:
#   - `native` — the `lake build` library (`.olean` artifacts + `libbasen.a`),
#   - `check`  — the Lean proof-validation gate (`lake build` with no `sorry`).
#
# `native`/`check` are the SAME `lake build`; `check` is the proof gate and
# `native` is the installable library.  The `codec` dependency is injected as a
# flake input by the consumer, and via `require codec from git` for the
# no-flakes dev loop (see `lakefile.lean`).
#
# Plain nixpkgs `lean4`; the codecs are pure Lean (no per-format C, no
# @[extern] seam), so every law stays `[propext, Quot.sound]`-only.

{
  lean4,
  lib,
  stdenv,
}:

let
  inherit (stdenv) mkDerivation;

  pname = "basen";

  meta = {
    description = "A verified base-2/4/8/10/16/32/64 encoding library in Lean 4";
    license = lib.licenses.agpl3Plus;
    maintainers = [
      {
        name = "Tim Dysinger";
        email = "tim@dysinger.net";
      }
    ];
    platforms = lib.platforms.all;
  };

  mkLakeBuild =
    {
      name,
      description,
      install,
      targets ? "",
      mainProgram ? null,
    }:
    mkDerivation {
      pname = "${pname}-${name}";
      version = "0.1.0";
      src = ./.;
      nativeBuildInputs = [ lean4 ];
      meta =
        meta
        // {
          inherit description;
        }
        // lib.optionalAttrs (mainProgram != null) {
          inherit mainProgram;
        };
      buildPhase = ''
        runHook preBuild
        lake build ${targets}
        runHook postBuild
      '';
      installPhase = install;
    };

in
{
  # The `lean4` toolchain shared by every path: one source of truth.
  inherit lean4;

  native = mkLakeBuild {
    name = "native";
    description = "${meta.description} (native library)";
    install = ''
      runHook preInstall
      mkdir -p "$out/lib/lean" "$out/lib"
      cp -r .lake/build/lib/* "$out/lib/lean/" 2>/dev/null || true
      if [ -e ".lake/build/lib/${pname}.a" ]; then
        cp ".lake/build/lib/${pname}.a" "$out/lib/lib${pname}.a"
      fi
      runHook postInstall
    '';
  };

  check = mkLakeBuild {
    name = "check";
    description = "${meta.description} (proof-validation gate)";
    install = ''
      runHook preInstall
      # The check is the build itself (zero `sorry`); produce an empty `$out`.
      mkdir -p "$out"
      runHook postInstall
    '';
  };
}
