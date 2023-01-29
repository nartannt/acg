{
  description = "the flake for this project";

  inputs = {
    # Convenience functions for writing flakes
    flake-utils.url = "github:numtide/flake-utils";
    # nixpkgs
    nixpkgs.url = "github:NixOs/nixpkgs/nixpkgs-unstable";
  };


  outputs = {
    self,
    flake-utils,
    nixpkgs
  }:
    flake-utils .lib.eachDefaultSystem (system:
    let 
      pkgs = import nixpkgs { inherit system; };
      ocamlPackages = pkgs.ocamlPackages;
      lib = nixpkgs.lib;
      ocaml = ocamlPackages.ocaml;
      ocaml-syntax-shims = ocamlPackages.ocaml-syntax-shims;
      ppx_let = pkgs.ppx_let;
    in {

    devShell = pkgs.mkShell {
      buildInputs = with pkgs; [
        ocaml
        dune_3
      ]
        ++ (with ocamlPackages; [
          merlin
          findlib
          utop
      ]);
    };
    #packages.default = ocamlPackages.buildDunePackage rec {

    # model for importing packages
    /*pname = "angstrom";
    version = "0.15.0";
    duneVersion = "3";
    minimalOCamlVersion = "4.04";

    src = pkgs.fetchFromGitHub {
      owner  = "inhabitedtype";
      repo   = pname;
      rev    = version;
      sha256 = "1hmrkdcdlkwy7rxhngf3cv3sa61cznnd9p5lmqhx20664gx2ibrh";
    };

    buildInputs = [ ocaml-syntax-shims ];
    doCheck = lib.versionAtLeast ocaml.version "4.05";

    meta = {
      homepage = "https://github.com/inhabitedtype/angstrom";
      description = "OCaml parser combinators built for speed and memory efficiency";
      license = lib.licenses.bsd3;
      maintainers = with lib.maintainers; [ sternenseemann ];
    };*/

    #};

  });

}
