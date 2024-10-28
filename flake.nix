{
  description = "A core language for rule-based hardware design";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    makes.url = "github:fluidattacks/makes/24.02";
    nixpkgs.url = "github:nixos/nixpkgs/release-24.05";
  };

  outputs = { self, flake-parts, makes, nixpkgs, ... } @ inputs:
    flake-parts.lib.mkFlake { inherit inputs; } {
      # Original flake.outputs attribute set. Everything in this set behaves like
      # usual flake outputs.
      flake = {
        # NOTE: To use this flake, apply the following overlay to nixpkgs and use
        # koika from its respective coqPackages_VER attribute set!
        # See _module.args.pkgs = ... below for an example!
        overlays.default = import ./overlay.nix;
      };
      systems = [ "x86_64-linux" "x86_64-darwin" "aarch64-darwin" ];
      perSystem = { inputs', self', system, pkgs, ... }: {
        _module.args.pkgs = import inputs.nixpkgs {
          inherit system;
          overlays = [ inputs.self.overlays.default ];
        };

        checks = {
          koika = self.packages.${system}.default.override {
            doCheck = true;
          };
        };

        devShells.default = self'.checks.koika;

        packages = {
          default = self'.packages.coq8_18-koika;
          coq8_18-koika = pkgs.coqPackages_8_18.koika;
          coqDev-koika = pkgs.coqPackages_koika.koika;
        };

        apps.makes = inputs'.makes.apps.default;
      };
    };
}
