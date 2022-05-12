{ system ? builtins.currentSystem, sources ? import ./nix/sources.nix, ghcVersion ? "902" }:

let
  selectHls = self: super: {
    haskell-language-server = super.haskell-language-server.override { supportedGhcVersions = [ "${ghcVersion}" ]; };
  };
  pkgs = import sources.nixpkgs { inherit system; overlays = [ selectHls ]; };
  stack-wrapped = pkgs.symlinkJoin {
    name = "stack";
    paths = [ pkgs.stack ];
    buildInputs = [ pkgs.makeWrapper ];
    postBuild = ''
      wrapProgram $out/bin/stack \
        --add-flags "\
          --nix \
          --nix-path=\\"nixpkgs=${pkgs.path}\\"
          --nix-shell-file nix/shell-stack.nix \
        "
    '';
  };
in with pkgs;

mkShell {
  # Set UTF-8 local so that run-tests can parse GHC's unicode output.
  LANG="C.UTF-8";
  NIX_PATH = "nixpkgs=${pkgs.path}";

  buildInputs = [
    haskell.compiler."ghc${ghcVersion}"
    stack-wrapped
    nix
    pkgs.haskell-language-server
    ghcid
  ];
}
