{
  description = "A devShell example";

  inputs = {
    nixpkgs.url      = github:nixos/nixpkgs/nixos-21.11;
    flake-utils.url  = github:numtide/flake-utils;
    verifast.url     = github:jpdoyle/verifast;
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
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
              verifast
          ];
        };
      }
    );
}

