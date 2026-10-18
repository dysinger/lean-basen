# Copyright 2026 Department of Code LLC.
# SPDX-License-Identifier: AGPL-3.0-or-later

{
  description = "basen — verified base-2/4/8/10/16/32/64 encodings in Lean 4";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    treefmt-nix.url = "github:numtide/treefmt-nix";
    # The `codec` dependency, injected as a flake input (its source dir) so the
    # sandboxed `lake build` never `git clone`s it (the `require codec from
    # "<path>"` rewrite in default.nix resolves the dependency locally).
    codec.url = "github:dysinger/lean-codec";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      treefmt-nix,
      codec,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };

        # The `codec` dependency's source dir (Lake builds it from source via
        # the `require codec from "<path>"` rewrite — no pre-built `.olean`
        # needed, no git clone).
        codecSrc = codec.outPath;

        # Lean package: the `default.nix` native derivation + proof check.
        _pkg = import ./default.nix {
          inherit (pkgs) lean4;
          inherit (pkgs) lib;
          inherit (pkgs) stdenv;
          inherit codecSrc;
        };

        treefmtModule = treefmt-nix.lib.evalModule pkgs ./treefmt.nix;
      in
      {
        # The default target builds the native library (`lake build` → `.olean`).
        packages.default = _pkg.native;
        packages.native = _pkg.native;

        # Lean proof validation: the same `lake build`, no `sorry` (the gate).
        checks.lean = _pkg.check;
        # Formatting check (treefmt).
        checks.formatting = treefmtModule.config.build.check self;

        formatter = treefmtModule.config.build.wrapper;

        devShells.default = pkgs.mkShellNoCC {
          name = "basen";
          packages = [
            _pkg.lean4 # lean, lake, leanc, and the Lean 4 LSP (lean --server)
            pkgs.stdenv.cc # the Nix clang wrapper (provides cc/clang/c++ with libc++)
            pkgs.elan # toolchain manager
            pkgs.git
          ];
          shellHook = ''
            echo "basen dev shell — lean $(lean --version | head -1 | awk '{print $2}')"
            git config core.hooksPath "$PWD/.githooks"
          '';
        };
      }
    );
}
