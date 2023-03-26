{
  description = "Compiler for RLL language";

  inputs = {
    nixpkgs.url = "nixpkgs/nixos-22.11";
  };
  nixConfig = {
    bash-prompt = ''\[\033[1;32m\][\[\e]0;\u@\h: \w\a\]dev-shell:\w]\$\[\033[0m\] '';
  };

  outputs = { self, nixpkgs }: 
  let system = "x86_64-linux"; in
  with nixpkgs.legacyPackages.${system};
  let
    compiler = "ghc943";
    hPkgs = haskell.packages.${compiler};
    stack-wrapped = symlinkJoin {
      name = "stack";
      paths = [ stack ];
      buildInputs = [ makeWrapper ];
      postBuild = ''
        wrapProgram $out/bin/stack --add-flags \
          "--no-nix --system-ghc --no-install-ghc"
      '';
    };

  in {
    devShells.x86_64-linux.default = mkShell {
      buildInputs = [ stack-wrapped haskell.compiler.${compiler} ispell ]
          ++ (with hPkgs; [
            ghc ghcid
            # Required by spacemacs haskell layer
            apply-refact hlint stylish-haskell hasktags hoogle
          ]);
      # Hack to make c stuff available to GHC
      # see: https://docs.haskellstack.org/en/stable/nix_integration/
      LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath [ zlib hPkgs.ghc ];
    };

  };
}
