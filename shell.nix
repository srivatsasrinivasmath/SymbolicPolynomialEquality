{pkgs ? import <nixpkgs> {}}:

pkgs.mkShell{
  buildInputs = with pkgs; [
    cabal-install
    (haskell-language-server.override{
      supportedGhcVersions = ["98"];
    })
    haskell.compiler.ghc98
    libpoly
  ];

  packages = with pkgs; [
    git
    z3_4_12
    (cvc5.overrideAttrs (final : prev: { cmakeFlags = prev.cmakeFlags ++ ["-DUSE_POLY=1"];
      buildInputs = prev.buildInputs ++ [pkgs.libpoly];
    }))
#    (callPackage ./withPoly.nix {})
  ];
}
