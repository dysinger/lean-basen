# Copyright 2026 Department of Code LLC.
# SPDX-License-Identifier: AGPL-3.0-or-later

# demo — a minimal verified Lean 4 library skeleton.
#
# Takes the Lean 4 toolchain (the `lean4` derivation) as concrete inputs — no
# `pkgs` blob, no overlay assumption — and returns:
#   - `native` — the `lake build` library (`.olean` artifacts + `libdemo.a`),
#   - `check`  — the Lean proof-validation gate (`lake build` with no `sorry`),
#   - `cli`    — the packaged command-line executable (`lake build cli`,
#                `Example.Count.CLI.main`), mirroring the F* template's
#                `cli` deliverable.
#
# `native`/`check` are the SAME `lake build`; `check` is the proof gate,
# `native` is the installable library, `cli` is the extraction vehicle.
#
# Plain nixpkgs `lean4`.  No C seams in the template (the `codec` bulk fast
# path is the shape a project may add back via `@[extern]` + `buildLeanO`);
# here the build is pure `lake build`.

{
  lean4,
  lib,
  stdenv,
}:

let
  inherit (stdenv) mkDerivation;

  pname = "demo";

  meta = {
    description = "A minimal verified Lean 4 library skeleton";
    license = lib.licenses.agpl3Plus;
    maintainers = [
      {
        name = "Tim Dysinger";
        email = "tim@dysinger.net";
      }
    ];
    platforms = lib.platforms.all;
  };

  # One build action: `lake build <targets>` (empty targets = the library +
  # proof-verify, no `sorry`). `targets` selects the explicit build target(s).
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
  # The `lean4` toolchain shared by every path (dev shell, proof gate, cli):
  # one source of truth for the `lean4` build configuration.
  inherit lean4;

  # `native` — the installable library artifact.
  native = mkLakeBuild {
    name = "native";
    description = "${meta.description} (native library)";
    install = ''
      runHook preInstall
      mkdir -p "$out/lib/lean" "$out/lib"
      cp -r .lake/build/lib/* "$out/lib/lean/" 2>/dev/null || true
      # The library archive (if any) is the loadable `lib${pname}.a`.
      if [ -e ".lake/build/lib/${pname}.a" ]; then
        cp ".lake/build/lib/${pname}.a" "$out/lib/lib${pname}.a"
      fi
      runHook postInstall
    '';
  };

  # `check` — the Lean proof-validation gate (the same `lake build`, zero `sorry`).
  check = mkLakeBuild {
    name = "check";
    description = "${meta.description} (proof-validation gate)";
    install = ''
      runHook preInstall
      # The check is the build itself (zero `sorry`); produce an (empty) `$out`
      # so the derivation satisfies Nix's output requirement.
      mkdir -p "$out"
      runHook postInstall
    '';
  };

  # `cli` — the packaged command-line executable (`Example.Count.CLI.main`).
  cli = mkLakeBuild {
    name = "cli";
    description = "${meta.description} (command-line executable)";
    targets = "cli";
    mainProgram = "cli";
    install = ''
      runHook preInstall
      mkdir -p "$out/bin"
      if [ -e ".lake/build/bin/cli" ]; then
        cp ".lake/build/bin/cli" "$out/bin/cli"
      fi
      runHook postInstall
    '';
  };
}
