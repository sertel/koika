final: prev: let
  koikaPkg = ./default.nix;
  injectKoika = name: set:
    prev.${name}.overrideScope (self: _: {
      koika = self.callPackage koikaPkg {};
    });
in
  prev.lib.mapAttrs injectKoika {
    inherit (final) coqPackages_8_18;
  }
