{
  description = "miniKanren semantics formalized in Rocq";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

  outputs = {
    self,
    nixpkgs,
  }: let
    systems = ["x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin"];
    forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f system);
  in {
    packages = forAllSystems (system: let
      pkgs = nixpkgs.legacyPackages.${system};
      coq = pkgs.coqPackages.coq;
    in {
      default = pkgs.stdenv.mkDerivation {
        pname = "miniKanren-coq";
        version = "0.1";
        src = self;

        nativeBuildInputs = [coq pkgs.coqPackages.stdlib];

        buildPhase = ''
          runHook preBuild
          make Makefile.coq
          make -f Makefile.coq all
          runHook postBuild
        '';

        installPhase = ''
          runHook preInstall
          make -f Makefile.coq install COQLIB=$out/lib/coq/
          runHook postInstall
        '';
      };
    });

    checks = forAllSystems (system: {
      build = self.packages.${system}.default;
    });

    devShells = forAllSystems (system: let
      pkgs = nixpkgs.legacyPackages.${system};
      coqPackages = pkgs.coqPackages;
    in {
      default = pkgs.mkShell {
        packages = [
          coqPackages.coq
          coqPackages.stdlib
          coqPackages.coq-lsp
        ];
        shellHook = ''
          make Makefile.coq
        '';
      };
    });
  };
}
