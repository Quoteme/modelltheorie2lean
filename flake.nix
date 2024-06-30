{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/080a4a27f206d07724b88da096e27ef63401a504";
    flake-utils = {
      inputs.nixpkgs.follows = "nixpkgs";
      url = "github:numtide/flake-utils";
    };
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
      in
      {
        devShells.default = pkgs.mkShell
          {
            buildInputs = with pkgs; [
              lean4
              git
              curl
              cmake
            ];
          };
      }
    );
}
