let
   hostPkgs = import <nixpkgs> {};
   # Generated through:
   # nix-shell -p nix-prefetch-git --run "nix-prefetch-git  https://github.com/nixos/nixpkgs.git --rev {rev} > nixpkgs-version.json"
   pinnedVersion = hostPkgs.lib.importJSON ./nixpkgs-version.json;

   pinnedPkgs = hostPkgs.fetchFromGitHub {
     owner = "NixOS";
     repo = "nixpkgs";
     inherit (pinnedVersion) rev sha256;
   };
 in pinnedPkgs
