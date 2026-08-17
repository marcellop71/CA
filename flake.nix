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

        # Lean 4 release binary. Keep `leanVersion` equal to
        # `lean-toolchain` (leanprover/lean4:v4.33.0) and refresh the
        # four hashes together:
        #   curl -sL https://github.com/leanprover/lean4/releases/download/v$V/lean-$V-$P.tar.zst \
        #     | sha256sum | cut -d' ' -f1 | xxd -r -p | base64      # → sha256-…
        # (or `nix hash file` on the downloaded tarball).
        leanVersion = "4.33.0";
        leanPlatform = {
          "x86_64-linux"   = "linux";
          "aarch64-linux"  = "linux_aarch64";
          "x86_64-darwin"  = "darwin";
          "aarch64-darwin" = "darwin_aarch64";
        }.${system} or (throw "CA: no Lean release tarball for ${system}");
        leanSha256 = {
          "linux"          = "sha256-Sz+wPCmh4KJT+x0R+brjcl8ZoNxvwJs+oW0snfM0niw=";
          "linux_aarch64"  = "sha256-+WGkF8uhC26gqdE2cS1ZUoE4F//WaABB8JojNSb4A6k=";
          "darwin"         = "sha256-GMSt/S5FOMNmj34HDojHohV23un730beffLvFsl//vM=";
          "darwin_aarch64" = "sha256-21J0tmm+JwrwSLXk8eDOVx32dQ5BGVaz4eb8wgEkEMI=";
        }.${leanPlatform};

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

        # Library path variable name (different on Darwin vs Linux)
        libPathVar = if pkgs.stdenv.isDarwin then "DYLD_LIBRARY_PATH" else "LD_LIBRARY_PATH";

        # Native dependencies.
        #   CA library : OpenSSL (CA/sha256/sha256_shim.c; -lssl -lcrypto)
        #   ca CLI     : hiredis + zlog, pulled in by redis-lean / zlog-lean
        #                (the library never imports them — see README,
        #                "Building")
        # arrow-cpp was dropped with arrow-lean (no longer a dependency).
        libDeps = [
          pkgs.openssl
          pkgs.hiredis
          pkgs.zlog
        ];
        nativeDeps = libDeps ++ [ pkgs.gmp pkgs.libuv ];   # Lean runtime

        # Lake's link lines name the Ubuntu paths
        # (`-L/usr/lib/x86_64-linux-gnu`, `-L/usr/local/lib`); inside the
        # shell the same libraries are found through LIBRARY_PATH and the
        # stray `-L` flags are harmless.
      in {
        devShells.default = pkgs.mkShell {
          buildInputs = nativeDeps ++ [
            lean4Bin
            pkgs.clang
            pkgs.lld
            pkgs.git       # lake fetches the git requires
            pkgs.redis     # `redis-server` for the ca CLI's fetch/address (optional)
          ];

          LIBRARY_PATH = pkgs.lib.makeLibraryPath nativeDeps;
          C_INCLUDE_PATH = pkgs.lib.makeSearchPath "include" [
            pkgs.openssl.dev
            pkgs.hiredis
            pkgs.zlog
          ];

          shellHook = ''
            export ${libPathVar}="${pkgs.lib.makeLibraryPath nativeDeps}"
            echo "CA development environment — Lean $(lean --version 2>/dev/null | sed 's/^Lean (version //; s/,.*//' || echo 'not found'), toolchain pin $(cat lean-toolchain 2>/dev/null)"
          '';
        };
      }
    );
}
