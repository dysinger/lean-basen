# Copyright 2026 Department of Code LLC.
# SPDX-License-Identifier: AGPL-3.0-or-later

{
  description = "demo — a minimal verified Lean 4 library template";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    treefmt-nix.url = "github:numtide/treefmt-nix";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      treefmt-nix,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };

        # Lean package: the `default.nix` native derivation + proof check.
        _pkg = import ./default.nix {
          inherit (pkgs) lean4;
          inherit (pkgs) lib;
          inherit (pkgs) stdenv;
        };

        treefmtModule = treefmt-nix.lib.evalModule pkgs ./treefmt.nix;
      in
      {
        # The default target builds the native library (`lake build` → `.olean`).
        packages.default = _pkg.native;
        packages.native = _pkg.native;
        # The packaged command-line executable (Example.Count.CLI.main).
        packages.cli = _pkg.cli;

        # `nix run .#cli` — the same entry point the `cli` package wraps.
        apps.default = flake-utils.lib.mkApp { drv = _pkg.cli; };
        apps.cli = flake-utils.lib.mkApp { drv = _pkg.cli; };

        # Lean proof validation: the same `lake build`, no `sorry` (the gate).
        checks.lean = _pkg.check;
        # Formatting check (treefmt).
        checks.formatting = treefmtModule.config.build.check self;

        formatter = treefmtModule.config.build.wrapper;

        devShells.default = pkgs.mkShellNoCC {
          name = "demo";
          packages = [
            _pkg.lean4 # lean, lake, leanc, and the Lean 4 LSP (lean --server)
            pkgs.stdenv.cc # the Nix clang wrapper (provides cc/clang/c++ with libc++)
            pkgs.elan # toolchain manager
            pkgs.git
          ];
          shellHook = ''
            echo "demo dev shell — lean $(lean --version | head -1 | awk '{print $2}')"
            # Activate the repo's pre-commit hook (runs `nix fmt` and fails if
            # staged files would be reformatted). Stored under .githooks/.
            git config core.hooksPath "$PWD/.githooks"
          '';
        };
      }
    )
    // {
      # Nix flake template (`nix flake init -t .`). The path is the repository
      # root: `init` copies flake.nix, default.nix, lakefile.lean, Example/,
      # and the prose/config files directly.
      templates.default = {
        path = ./.;
        description = "Minimal verified Lean 4 library: lean_lib proof gate + a CLI executable";
        welcomeText = ''
          # Lean 4 verified project template

          A minimal verified Lean 4 library (one `lean_lib` + a `cli`
          executable) with a Nix flake exposing native/check/cli targets.

          Create a new project (see the README):

          1. nix flake init -t github:dysinger/lean-nix-flake-template
          2. rename `demo`/`Example` (see "Renaming" in the README)
          3. nix build .#native .#cli

          - Dev loop:   nix develop && lake build
          - Run the CLI: nix run .#cli
        '';
      };
    };
}
