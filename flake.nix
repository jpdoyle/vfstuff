{
  description = "VeriFast proofs, verified with the VeriFast checkout in ../verifast";

  inputs = {
    # VeriFast itself: the git checkout next to this repo. Its flake provides
    # a `packages.verifast` verifier (vfconsole.exe + stdlib manifests) and a
    # devShell for building VeriFast itself from source.
    # Absolute path instead of `../verifast` because relative `path:` inputs
    # do not resolve outside a git-worktree flake in pure evaluation mode.
    verifast.url = "path:/home/joe/verifast";
    # Build everything with one nixpkgs revision.
    nixpkgs.follows = "verifast/nixpkgs";
    flake-utils.follows = "verifast/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, verifast, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [
            # The VeriFast from ../verifast: `verifast` CLI verifier. Its stdlib
            # manifests and headers live next to the binary (its bindir/vroot
            # "CRT"), where the verifier looks for #include'd .h/.gh files and
            # auto-links crt.dll.vfmanifest.
            verifast.packages.${system}.verifast
            pkgs.gnumake # rules in the Makefile
            pkgs.gcc # ${CC}: bin/fibber etc. get compiled by some make targets
          ];
        };
      });
}
