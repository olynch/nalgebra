{
  description = "numerical linear algebra for lean";

  inputs.lean.url = "github:leanprover/lean4/v4.0.0-rc4";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  nixConfig = {
    extra-trusted-public-keys = "lean4.cachix.org-1:mawtxSxcaiWE24xCXXgh3qnvlTkyU7evRRnGeAhD4Wk=";
    extra-substituters = "https://lean4.cachix.org";
  };

  outputs = { self, lean, flake-utils }: flake-utils.lib.eachDefaultSystem (system:
    let
      leanPkgs = lean.packages.${system};
      pkg = leanPkgs.buildLeanPackage {
        name = "nalgebra";  # must match the name of the top-level .lean file
        src = ./src;
      };
    in {
      packages = pkg // {
        inherit (leanPkgs) lean;
      };

      defaultPackage = pkg.modRoot;
    });
}
