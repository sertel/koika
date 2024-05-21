{
  description = "A core language for rule-based hardware design";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/release-23.11";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, flake-utils, nixpkgs, ... }:
    with flake-utils.lib;
    let
      koikaPkg = { lib, mkCoqDerivation, coq, boost, python3, sphinx }: mkCoqDerivation rec {
        pname = "koika";
        defaultVersion = "0.0.1";

        opam-name = "koika";
        useDune = true;

        release."0.0.1" = {
          src = lib.const (lib.cleanSourceWith {
            src = lib.cleanSource ./.;
            filter = let inherit (lib) hasSuffix; in path: type:
              (! hasSuffix ".gitignore" path)
              && (! hasSuffix "flake.nix" path)
              && (! hasSuffix "flake.lock" path)
              && (! hasSuffix "_build" path);
          });
        };

        enableParallelBuilding = true;

        nativeBuildInputs = [
          python3
          sphinx
        ];

        buildInputs = [
          boost
        ];

        propagatedBuildInputs = with coq.ocamlPackages; [
          findlib
          base
          core
          core_unix
          stdio
          parsexp
          hashcons
          zarith
        ];

        preInstall = ''
          dune build README.html
          mkdir -p $out/share/doc/koika
          cp README.html $out/share/doc/koika/
        '';

        postInstall = ''
          mkdir -p "$OCAMLFIND_DESTDIR"
          mv "$out/lib/koika" "$OCAMLFIND_DESTDIR"
        '';

        # NOTE: Also build the examples, because they use additional parts of
        # the Dune toolchain.
        checkPhase = ''
          runHook preCheck
          ./coq.kernel.hack.sh
          dune build @runtest
          runHook postCheck
        '';

        shellHook = ''
          [ -x coq.kernel.hack.sh ] && ./coq.kernel.hack.sh
        '';
      };

    in eachDefaultSystem (system: let

      pkgs = import nixpkgs {
        inherit system;
        overlays = [ self.overlays.default ];
      };


    in {

      checks = {
        koika = self.packages.${system}.default.overrideAttrs (_: {
          doCheck = true;
        });
      };

      devShells.default = self.checks.${system}.koika;

      packages = {
        default = self.packages.${system}.coq8_14-koika;
        coq8_14-koika = pkgs.coqPackages_8_14.koika;
        coqDev-koika = pkgs.coqPackages_koika.koika;
      };

    }) // {

      # NOTE: To use this flake, apply the following overlay to nixpkgs and use
      # koika from its respective coqPackages_VER attribute set!
      overlays.default = final: prev: let
        injectKoika = name: set:
          prev.${name}.overrideScope (self: _: {
            koika = self.callPackage koikaPkg {};
          });
      in (nixpkgs.lib.mapAttrs injectKoika {
        inherit (final) coqPackages_8_14;
      }) // {
        coqPackages_koika = prev.coqPackages_8_14.overrideScope (self: super: {
          coq = super.coq.override { customOCamlPackages = prev.ocaml-ng.ocamlPackages_4_09; };
          koika = self.callPackage koikaPkg {};
        });
      };
    };
}
