final: prev: let
  koikaPkg = ./default.nix;
  injectKoika = name: set:
    prev.${name}.overrideScope (self: _: {
      koika = self.callPackage koikaPkg {};
    });
in
  (prev.lib.mapAttrs injectKoika {
    inherit (final) coqPackages_8_14;
  })
  // {
    coqPackages_koika = prev.coqPackages_8_14.overrideScope (self: super: {
      coq = super.coq.override {customOCamlPackages = prev.ocaml-ng.ocamlPackages_4_09;};
      koika = self.callPackage koikaPkg {};
    });
  }
