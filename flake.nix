{
  description = "A core language for rule-based hardware design";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/release-23.11";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = {
    self,
    flake-utils,
    nixpkgs,
    ...
  }:
    with flake-utils.lib;
      eachDefaultSystem (system: let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [self.overlays.default];
        };
      in {
        checks = {
          koika = self.packages.${system}.default.override {
            doCheck = true;
          };
        };

        devShells.default = self.checks.${system}.koika;

        packages = {
          default = self.packages.${system}.coq8_18-koika;
          coq8_14-koika = pkgs.coqPackages_8_14.koika;
          coq8_18-koika = pkgs.coqPackages_8_18.koika;
          coqDev-koika = pkgs.coqPackages_koika.koika;
        };
      })
      // {
        # NOTE: To use this flake, apply the following overlay to nixpkgs and use
        # koika from its respective coqPackages_VER attribute set!
        overlays.default = import ./overlay.nix;
      };
}
