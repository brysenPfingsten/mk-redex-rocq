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
        pname = "mk-redex-rocq";
        version = "0.1";
        # Keep local pre-push checks independent of existing .vo/.cmo files.
        src = pkgs.lib.cleanSourceWith {
          src = self;
          filter = path: type:
            pkgs.lib.cleanSourceFilter path type
            && (let
              name = baseNameOf path;
            in
              !(builtins.elem name [
                "Makefile.coq"
                "Makefile.coq.conf"
                ".Makefile.coq.d"
                "search.ml"
                "search.mli"
                "mk-search"
                "demo"
                "interface-tests"
                "relation-tests"
                "benchmark_search.ml"
                "benchmark_search.mli"
                "benchmark-bytecode"
                "benchmark-native"
                "unifier-benchmark-bytecode"
                "unifier-benchmark-native"
              ])
              && builtins.match ".*\\.(vo|vos|vok|glob|cmi|cmo|cmx|o|aux|cache)$" name == null);
        };

        nativeBuildInputs = [coq pkgs.coqPackages.stdlib pkgs.ocaml];
        doCheck = true;

        buildPhase = ''
          runHook preBuild
          coq_makefile -f _CoqProject -o Makefile.coq
          make -f Makefile.coq all
          make -C extract all
          runHook postBuild
        '';

        checkPhase = ''
          runHook preCheck
          make -C extract check
          runHook postCheck
        '';

        installPhase = ''
          runHook preInstall
          make -f Makefile.coq install COQLIBINSTALL=$out/lib/coq/user-contrib
          install -Dm755 extract/mk-search $out/bin/mk-search
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
          pkgs.ocaml
        ];
        shellHook = ''
          coq_makefile -f _CoqProject -o Makefile.coq
        '';
      };
    });
  };
}
