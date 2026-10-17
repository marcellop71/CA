import Lake
open System Lake DSL

package "ca" where
  moreLinkArgs := #["-Wl,--allow-shlib-undefined", "-lssl", "-lcrypto"]

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.35.0"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "v4.35.0"

-- Needed only by the `ca` CLI executable (`fetch`/`address` store to
-- Redis); the CA library never imports it.
require redisLean from git
  "https://github.com/marcellop71/redis-lean" @ "v4.35.0"

@[default_target]
lean_lib CA where
  extraDepTargets := #[`libsha256_shim]

lean_exe "ca" where
  root := `Main
  supportInterpreter := true
  -- supportInterpreter makes undefined symbols fatal at link time, so the
  -- native deps of the transitive redis-lean/zlog-lean shims must be
  -- resolved here explicitly.
  moreLinkArgs := #[
    "-L/usr/lib/x86_64-linux-gnu", "-lhiredis", "-lhiredis_ssl",
    "-L/usr/local/lib", "-Wl,-rpath,/usr/local/lib", "-lzlog",
    "-lssl", "-lcrypto"]

/-- Compile `src` into `oFile` with a build trace over `src` and `deps` (local headers,
    `#include`d `.c` files), so editing any of them rebuilds the object and the archives
    that use it. `weakArgs` (include paths) are kept out of the trace. -/
def tracedO (oFile src : FilePath) (deps : Array FilePath := #[])
    (weakArgs traceArgs : Array String := #[]) : SpawnM (Job FilePath) := do
  let inputs ← (#[src] ++ deps).mapM inputTextFile
  let srcJob ← (Job.collectArray inputs).mapM fun _ => pure src
  buildO oFile srcJob weakArgs traceArgs

target sha256_shim_o pkg : FilePath := do
  tracedO (pkg.buildDir / "c" / "sha256_shim.o") (pkg.dir / "CA" / "sha256" / "sha256_shim.c")
    (weakArgs := #["-I", (← getLeanIncludeDir).toString])
    (traceArgs := #["-fPIC", "-O2"])

extern_lib libsha256_shim pkg := do
  let obj ← sha256_shim_o.fetch
  let name := nameToStaticLib "sha256_shim"
  buildStaticLib (pkg.staticLibDir / name) #[obj]

/-- Property tests for `CA.RefHash` (elaborates a small source against `Init`). -/
lean_exe "refhash-test" where
  root := `RefHashTest
  supportInterpreter := true
  -- Links the whole CA lib, whose Registry modules pull redis-lean's shim.
  moreLinkArgs := #["-L/usr/lib/x86_64-linux-gnu", "-lhiredis", "-lhiredis_ssl", "-lssl", "-lcrypto"]
