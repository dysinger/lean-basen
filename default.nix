# Copyright 2026 Department of Code LLC.
# SPDX-License-Identifier: AGPL-3.0-or-later

# basen — a verified base-2/4/8/10/16/32/64 encoding library in Lean 4.
#
# Takes the Lean 4 toolchain (the `lean4` derivation) as concrete inputs — no
# `pkgs` blob, no overlay assumption — and returns:
#   - `native` — the `lake build` library (`.olean` artifacts + `libbasen.a`),
#   - `check`  — the Lean proof-validation gate (`lake build` with no `sorry`),
#   - `bench`  — the byte-exact vector bench lane (`lake build bench`).
#
# `native`/`check` are the SAME `lake build`; `check` is the proof gate and
# `native` is the installable library.  `bench` is a *separate* target on
# purpose: it is the RFC 4648 §10 / hand-vector value check, not a proof, so it
# must not be able to fail the gate and must not be required by it.
#
# `bench` is an `lean_exe` whose value checks are **all compile-time**: `example … :=
# rfl` and `example … := by native_decide` both fire while Lake elaborates the module.
# There are 12 of the latter, sanctioned and recorded in `Bench.lean` (bench-only,
# outside the axiom gate; `Axioms.lean` asserts the count). `Bench.lean`'s `main` is
# `pure ()` — the lane has no runtime work — so **building it is what runs the checks**.
#
# So what `nix build .#bench` proves is that the lane **builds in the sandbox**: the
# dependency injection resolves, the module elaborates, every vector is checked at
# compile time, and the executable links. It does *not* prove anything about runtime
# output, because there is none. Three documents used to say the lane must be *run*
# for its checks to happen; that was false of this code (`codec-audit-round-six`
# R7-16, design §D4) and is corrected here. `installPhase` still executes the binary
# only as a smoke check that it starts and exits 0.
#
# The `codec` dependency is injected as a flake input by the consumer, and via
# `require codec from git` for the no-flakes dev loop (see `lakefile.lean`).
#
# Plain nixpkgs `lean4`; the codecs are pure Lean (no per-format C, no
# @[extern] seam), so every law stays `[propext, Quot.sound]`-only.

{
  lean4,
  lib,
  stdenv,
  codecSrc ? null,
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
        # Inject the `codec` dependency as a local path dependency when a
        # flake input provides its source (the no-flakes `import ./default.nix`
        # loop leaves `require codec from git` untouched). The path form makes
        # Lake resolve the package directly, so the sandbox needs no `git` or
        # network (see flake.nix / the `ecosystem` dependency-injection spec).
        # The injected source is a read-only store path, so copy it into the
        # (writable) build sandbox for Lake to build its `.lake` into.
        ${lib.optionalString (codecSrc != null) ''
          cp -r "${codecSrc}" ./codec-src
          chmod -R u+w ./codec-src
          substituteInPlace lakefile.lean \
            --replace-quiet \
              'require codec from git "https://github.com/dysinger/lean-codec.git" @ "master"' \
              'require codec from "./codec-src"'
        ''}
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

  bench = mkLakeBuild {
    name = "bench";
    description = "${meta.description} (byte-exact vector bench lane)";
    targets = "bench";
    mainProgram = "bench";
    install = ''
      runHook preInstall
      mkdir -p "$out/bin"
      cp .lake/build/bin/bench "$out/bin/bench"
      # The checks all fired at *build* time (Lake elaborates every `example`), so
      # this execution is a smoke test that the binary starts and exits 0 — not the
      # thing that verifies the vectors.  See the header comment.
      "./.lake/build/bin/bench"
      runHook postInstall
    '';
  };
}
