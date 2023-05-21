{ nixpkgs ?  <nixpkgs> }:
with (import nixpkgs {});
agdaPackages.mkDerivation {
  version = "1.0.1";
  pname = "parallel-algorithms";
  meta="";
  src = ./src;
  buildInputs = [
    agdaPackages.standard-library
    (agdaPackages.mkDerivation {
      pname = "felix";
      version = "1.0.1";
      meta = "";
      src = /home/atticusk/.agda/felix/src;
      buildInputs = [
        agdaPackages.standard-library
      ];
    })
  ];
}
