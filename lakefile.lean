import Lake
open System Lake DSL

package "ca" where
  moreLinkArgs := #[
    "-L/usr/lib/x86_64-linux-gnu",
    "-lhiredis", "-lhiredis_ssl", "-lssl", "-lcrypto"
  ]

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "main"

require redisLean from git
  "https://github.com/marcellop71/redis-lean.git" @ "main"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.29.0-rc1"

lean_lib CA where
  extraDepTargets := #[`libsha256_shim]

@[default_target]
lean_exe "ca" where
  root := `Main

target sha256_shim_o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "sha256_shim.o"
  IO.FS.createDirAll oFile.parent.get!
  compileO oFile (pkg.dir / "CA" / "sha256" / "sha256_shim.c")
    #["-fPIC", "-O2", "-I", (← getLeanIncludeDir).toString]
  return .pure oFile

extern_lib libsha256_shim pkg := do
  let obj ← sha256_shim_o.fetch
  let name := nameToStaticLib "sha256_shim"
  buildStaticLib (pkg.staticLibDir / name) #[obj]
