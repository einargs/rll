{
  description = "Compiler for RLL language";

  inputs = {
    # nixpkgs.url = "nixpkgs/nixos-23.11";
    haskellNix.url = "github:input-output-hk/haskell.nix";
    nixpkgs.follows = "haskellNix/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  nixConfig = {
    bash-prompt = ''\[\033[1;32m\][\[\e]0;\u@\h: \w\a\]dev-shell:\w]\$\[\033[0m\] '';
    # This sets the flake to use the IOG nix cache.
    # Nix should ask for permission before using it,
    # but remove it here if you do not want it to.
    extra-substituters = ["https://cache.iog.io"];
    extra-trusted-public-keys = ["hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ="];
    allow-import-from-derivation = "true";
  };

  outputs = { self, nixpkgs, flake-utils, haskellNix }:
  let systems = [ "x86_64-linux" "x86_64-darwin" ]; in
  flake-utils.lib.eachSystem systems (system: let
    overlays = [ haskellNix.overlay
      (final: prev: {
        # This overlay adds our project to pkgs
        rllProject = final.haskell-nix.project' {
          shell.name = "rll";
          name = "rll";
          src = ./.;
          # compiler-nix-name = "ghc948";
          #compiler-nix-name = "ghc943";
          compiler-nix-name = "ghc964";
          # This is used by `nix develop .` to open a shell for use with
          # `cabal`, `hlint` and `haskell-language-server`
          shell.tools = {
            # I don't think I can use stack anymore
            cabal = {};
            hlint = {};
            haskell-language-server = {};
          };
          # Non-Haskell shell tools go here
          shell.buildInputs = with pkgs; [
            zlib
            llvmPackages_15.libllvm
            nixpkgs-fmt
            stack
            # stack-wrapped
          ];
          modules = with pkgs; [{
            packages.llvm-hs.components.library.libs =
              pkgs.lib.mkForce [llvmPackages_15.libllvm];
          }];
          # This adds `js-unknown-ghcjs-cabal` to the shell.
          # shell.crossPlatforms = p: [p.ghcjs];
        };
      })
    ];
    pkgs = import nixpkgs { inherit system overlays; inherit (haskellNix) config; };
    flake = pkgs.rllProject.flake {
      # This adds support for `nix build .#js-unknown-ghcjs:hello:exe:hello`
      # crossPlatforms = p: [p.ghcjs];
    };
    in flake // {
      # Built by `nix build .`
      packages.default = flake.packages."hello:exe:hello";
    });

/*
  outputs = { self, nixpkgs }: 
  let system = "x86_64-linux"; in
  # with import nixpkgs {
  #   inherit system;
  #   config.allowBroken = true;
  # };
  with nixpkgs.legacyPackages.${system};
  let
    compiler = "ghc943";
    stack-wrapped = symlinkJoin {
      name = "stack";
      paths = [ stack ];
      buildInputs = [ makeWrapper ];
      postBuild = ''
        wrapProgram $out/bin/stack --add-flags \
          "--no-nix --system-ghc --no-install-ghc"
      '';
    };
    hPkgs = haskell.packages.${compiler};
    hls = haskell-language-server.override { supportedGhcVersions = ["943"]; };
  in {
    devShells.x86_64-linux.default = mkShell {
      buildInputs = [ stack-wrapped zlib ispell llvmPackages_15.libllvm hls ]
          ++ (with hPkgs; [
            ghc
          ])
          ++ (with haskellPackages; [
            # Required by spacemacs haskell layer
            apply-refact stylish-haskell hasktags hlint hoogle
          ]);
       src = [
         ./flake.nix
         ./flake.lock
        ];

      unpackPhase = ''
        for srcFile in $src; do
          cp $srcFile $(stripHash $srcFile)
        done
      ''; 
      # Hack to make c stuff available to GHC
      # see: https://docs.haskellstack.org/en/stable/nix_integration/
      # LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath [ zlib hPkgs.ghc ];
    };

  };*/
}
