{
  description = "A devShell example";

  inputs = {
    nixpkgs.url      = github:nixos/nixpkgs/nixos-21.11;
    flake-utils.url  = github:numtide/flake-utils;
    jpdoyle-vf.url     = github:jpdoyle/verifast/master;
  };

  outputs = { self, nixpkgs, flake-utils, jpdoyle-vf, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [];
        pkgs = import nixpkgs {
          inherit system overlays;
        };
      in
      with pkgs;
      {
        devShell = mkShell {
          buildInputs = [
              jpdoyle-vf.packages.${system}.verifast
          ];
        };
      }
    );
}

