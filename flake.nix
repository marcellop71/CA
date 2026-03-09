{
  description = "CA - Content-Addressing for Lean 4";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # Platform-specific Lean 4 binary
        leanVersion = "4.29.0-rc1";
        leanPlatform = if pkgs.stdenv.isDarwin then "darwin" else "linux";
        leanSha256 = if pkgs.stdenv.isDarwin
          then "sha256-NUg4msNdykMY6zZob+IUdSY19yx6kbreEuQqst1DIAM="
          else "sha256-JEwQa9R9TkVOkJSKQs0WAG0YIfB8f2WGyOi2n6IceNQ=";

        lean4Bin = pkgs.stdenv.mkDerivation {
          pname = "lean4";
          version = leanVersion;
          src = pkgs.fetchurl {
            url = "https://github.com/leanprover/lean4/releases/download/v${leanVersion}/lean-${leanVersion}-${leanPlatform}.tar.zst";
            sha256 = leanSha256;
          };
          nativeBuildInputs = [ pkgs.zstd ]
            ++ pkgs.lib.optionals pkgs.stdenv.isLinux [ pkgs.autoPatchelfHook ];
          buildInputs = pkgs.lib.optionals pkgs.stdenv.isLinux [ pkgs.stdenv.cc.cc.lib pkgs.zlib ];
          unpackPhase = ''
            tar --zstd -xf $src
          '';
          installPhase = ''
            mkdir -p $out
            cp -r lean-${leanVersion}-${leanPlatform}/* $out/
          '';
        };
        leanBin = lean4Bin;
        lakeBin = lean4Bin;

        # Library path variable name (different on Darwin vs Linux)
        libPathVar = if pkgs.stdenv.isDarwin then "DYLD_LIBRARY_PATH" else "LD_LIBRARY_PATH";

        # Native C dependencies (only openssl for sha256_shim.c FFI)
        nativeDeps = [
          pkgs.openssl
          pkgs.gmp
        ];

      in {
        devShells.default = pkgs.mkShell {
          buildInputs = nativeDeps ++ [
            leanBin
            lakeBin
            pkgs.clang
            pkgs.lld
          ];

          LIBRARY_PATH = pkgs.lib.makeLibraryPath nativeDeps;
          C_INCLUDE_PATH = "${pkgs.openssl.dev}/include";

          shellHook = ''
            export ${libPathVar}="${pkgs.lib.makeLibraryPath nativeDeps}"
            echo "CA development environment"
            echo "Lean version: $(lean --version 2>/dev/null || echo 'Lean not found')"
          '';
        };
      }
    );
}
