# Decentralized Registry Design

## Overview

The global registry of formal mathematics is the union of project-local
registries. Each participating Lean project hosts a `registry/` folder
containing an append-only manifest of its published declarations. There is
no central server — publication is `git push`, verification is `lake build`,
and discovery is a curated list of known registry-hosting repositories.

This design follows from two properties of content-addressing:

1. **Determinism.** The same mathematical content always produces the same
   address, regardless of who computes it or where.
2. **Monotonic consensus.** A declaration is proved if *any* registry has a
   valid proof. Proofs are monotonic — once proved, always proved. No
   conflict resolution protocol is needed.

## Architecture

Three pieces compose the system, all living in the `CA` repository:

1. **The content-addressing engine** (`CA.*`) — canonicalization, hashing,
   serialization. The core library that computes addresses.

2. **The registry module** (`CA.Registry.*`) — `@[publish]` and
   `@[open_point]` attributes, status classification, and the
   `registry generate` command that scans the environment and writes the
   local registry folder.

3. **The sources list** — a file listing known registry-hosting GitHub
   repositories. Resolution tools (`use`, `resolve%`) consult this list to
   find declarations across the ecosystem.

### Module layout

Everything lives in the `CA` repository. Downstream projects depend on
a single package:

```lean
require ca from git "https://github.com/marcellop71/CA" @ "main"
```

Source tree (items marked *planned* are not yet implemented):

```
CA/
├── lakefile.lean
├── CA.lean                        # re-exports all modules
├── CA/
│   ├── Canonical.lean             # L0/L1 canonicalization
│   ├── SHA256.lean                # SHA-256 FFI (OpenSSL)
│   ├── ExprHash.lean              # Expr serialization, DeclHash, batch hashing
│   ├── Export.lean                # JSON manifest, edge list, summary stats
│   ├── Util.lean                  # collectConstants, constantKind
│   └── Registry/
│       ├── Basic.lean             # entry types, extensions, query API
│       ├── Attributes.lean        # @[publish], @[open_point]
│       ├── Status.lean            # proved/open/conditional classification (planned)
│       ├── Generate.lean          # registry generate command (planned)
│       ├── Resolve.lean           # use, use!, resolve% elaborators (planned)
│       └── Sources.lean           # sources.json parsing, cache management (planned)
├── Main.lean                      # CLI: ca fetch, ca address
├── sources.json                   # default sources list (planned)
└── docs/
    └── ...
```

### Why a single repo

The attribute library and the content-addressing engine are tightly
coupled: `@[publish]` needs to invoke the CA hashing pipeline to generate
registry entries, and the `registry generate` command uses `CA.ExprHash`
directly. Keeping them in separate repos means version-syncing two
packages that share core logic.

A single repo with two `lean_lib` targets gives both:

- **One dependency** for downstream projects (`require ca`).
- **Separate compilation** — Lake only builds what's needed. A project
  that only uses `CA.Registry.Attributes` (for `@[publish]`) does not
  need to build the CLI or the Redis integration.

### Downstream project structure

A project using the registry:

```
my-project/
├── lakefile.lean                  # requires ca
├── MyProject/
│   └── Theorems.lean              # @[publish], @[open_point] annotations
└── registry/                      # auto-generated, committed to git
    ├── declarations.json          # append-only manifest
    └── meta.json                  # toolchain, project URL, last indexed commit
```

Every project that opts in becomes a registry node. The global registry is
the union of all project-local registries.

## Registry Folder Format

### `meta.json`

Project-level metadata. Updated on each `registry generate` run.

```json
{
  "project": "my-project",
  "url": "https://github.com/user/my-project",
  "lean_toolchain": "leanprover/lean4:v4.29.0-rc4",
  "generated_at": "2026-03-09T12:00:00Z",
  "commit": "abc123...",
  "generator_version": "0.1.0"
}
```

### `declarations.json`

Array of published declarations. Each entry contains the content address,
human-readable metadata, status, and dependency information.

```json
[
  {
    "address": "a7f3b2c1e4d5...",
    "name": "MyProject.foo_comm",
    "module": "MyProject.Theorems",
    "kind": "theorem",
    "status": "proved",
    "pp_type": "∀ (a b : Nat), a + b = b + a",
    "type_deps": ["e1f2a3...", "b4c5d6..."],
    "value_deps": ["c7d8e9..."],
    "level": 0,
    "toolchain": "leanprover/lean4:v4.29.0-rc4"
  },
  {
    "address": "f8e7d6c5b4a3...",
    "name": "MyProject.MyConjecture",
    "module": "MyProject.Theorems",
    "kind": "definition",
    "status": "open",
    "pp_type": "∀ n : Nat, ∃ p, Nat.Prime p ∧ n < p ∧ p < 2 * n",
    "type_deps": ["a1b2c3..."],
    "value_deps": [],
    "level": 0,
    "toolchain": "leanprover/lean4:v4.29.0-rc4"
  },
  {
    "address": "1a2b3c4d5e6f...",
    "name": "MyProject.conditional_result",
    "module": "MyProject.Theorems",
    "kind": "theorem",
    "status": "conditional",
    "status_deps": ["f8e7d6c5b4a3..."],
    "pp_type": "MyConjecture → SomeConsequence",
    "type_deps": ["f8e7d6c5b4a3...", "d4e5f6..."],
    "value_deps": [],
    "level": 0,
    "toolchain": "leanprover/lean4:v4.29.0-rc4"
  }
]
```

#### Status classification

Status is computed automatically from the environment during
`registry generate`:

| Pattern | Status | Rule |
|---|---|---|
| `theorem foo : P := proof` (no `sorry`) | `proved` | Type-checks, no sorry in transitive closure |
| `def P : Prop := ...` with `@[open_point]` | `open` | Explicitly marked as open problem |
| `def P : Prop := ...` with no theorem of type `P` | `open` | Stated, no proof exists |
| `theorem bar (h : OpenP) : Q := ...` | `conditional` | Proved modulo open hypotheses |

For conditional declarations, `status_deps` lists the addresses of the
open hypotheses — the declarations whose proof would promote this entry
from conditional to proved.

#### Append-only convention

Entries are never removed from `declarations.json`. New declarations are
appended. If a declaration's type changes (e.g. due to a refactor that
alters the statement), a new entry with a new address is added; the old
entry remains as history.

Status updates (open → proved) are reflected by updating the `status`
field in place. This is the only mutation allowed. The git history
provides a full audit trail of when each status transition occurred.

## Sources List

The sources list is a JSON file enumerating known registry-hosting
repositories. A default `sources.json` ships with the `CA` package; users
can override it with a project-local `sources.json`.

### `sources.json`

```json
{
  "version": 1,
  "registries": [
    {
      "name": "mathlib4",
      "url": "https://github.com/leanprover-community/mathlib4",
      "registry_path": "registry/",
      "description": "Lean 4 Mathlib"
    },
    {
      "name": "EM",
      "url": "https://github.com/marcellop71/EM",
      "registry_path": "registry/",
      "description": "Euclid-Mullin formalization"
    }
  ]
}
```

### Adding a project to the ecosystem

A project joins the global registry by:

1. Adding `require ca from git "https://github.com/marcellop71/CA" @ "main"`
   to its `lakefile.lean`.
2. Annotating declarations with `@[publish]` or `@[open_point]`.
3. Running `lake exe ca registry generate` to produce `registry/`.
4. Committing `registry/` to git and pushing.
5. Opening a PR to add one entry to `sources.json` in the CA repo.

Step 5 is the only coordination point. Everything else is local.

### Discovery alternatives

The static `sources.json` is the simplest approach. Alternatives for
later:

- **GitHub topic tag.** Projects tag themselves with `lean-formal-registry`.
  The tool discovers registries via GitHub API search. More automatic but
  adds a GitHub API dependency.
- **DNS-based.** A TXT record or well-known URL convention
  (`https://example.com/.well-known/lean-registry.json`). Over-engineered
  for now.

The static list is the right starting point. It can be replaced later
without changing any other part of the design.

## Resolution Protocol

When a user writes `use Nat.add_comm` or `resolve% Nat.add_comm`, the
resolution proceeds in stages:

```
1. Check local environment
   → found? done.

2. Check local registry cache (~/.lean/registry-cache/)
   → found? return address, module, source repo.

3. Fetch registry/ from known sources
   (GitHub raw file URLs or git sparse checkout)
   → merge into local cache.

4. Find matching name across all registries
   → return address, module, source repo.

5. Optionally: clone source, load .olean, import into environment
   (this is what use! does)
```

### Cache structure

The local cache aggregates declarations from all known registries into a
single queryable index:

```
~/.lean/registry-cache/
├── index.json          # merged index: name → address → source registry
├── addresses.json      # address → [names, modules, repos]
└── sources-etag.json   # HTTP ETags for cache invalidation
```

The cache is rebuilt on `registry update` (explicit) or when a resolution
misses the cache (lazy).

### Name conflicts

Two projects may define the same name with different types (different
addresses). This is not a conflict — they are different declarations.
Resolution disambiguates by source:

```
use Nat.add_comm              -- first match in sources order
use Nat.add_comm from mathlib -- explicit source qualifier
```

Two projects proving the same address under different names is also not a
conflict — they are aliases. The resolution result includes all known
aliases.

## Verification Model

Trust is optional. Every claim in the registry is independently
verifiable:

1. Clone the source project.
2. Run `lake build`.
3. If it compiles, the declarations are valid (Lean's kernel is the
   authority).
4. Re-run `registry generate` and compare the output with the committed
   `registry/` folder.

No trust in the registry operator is required. A consumer who wants
maximum assurance verifies locally. A consumer who trusts the source
project can use the registry data directly.

### Proof certificates

For lightweight verification without a full `lake build`, a future
extension could include proof certificates — serialized proof terms or
.olean fragments that Lean's kernel can check independently. This is
not needed for the initial design.

## Status Cascade

When a proof is submitted for an open point, conditional declarations
downstream may become unconditional. The cascade works as follows:

1. `registry generate` detects that a previously open `Prop` now has a
   proof (a theorem of that type exists in the environment).
2. It updates the status of that address from `open` to `proved`.
3. It scans all `conditional` entries whose `status_deps` included the
   newly proved address.
4. For each, it checks: are all `status_deps` now proved? If so, promote
   to `proved`.
5. This cascades: a newly proved entry may itself be in the `status_deps`
   of further downstream entries.

The cascade is local to the project's own registry. Cross-project cascades
happen when a consumer merges multiple registries: an open point in project
A may be proved in project B, which promotes conditional entries in
project C.

### Cross-project cascade example

```
Project A:  DeterministicStabilityLemma          → status: open
Project B:  proof_of_dsl : DSL := ...            → status: proved (proves A's open point)
Project C:  full_chain (h : DSL) : MC := ...     → status: conditional (depends on A's address)
```

A consumer merging all three registries sees:

1. A's address is proved (B has a proof).
2. C's `status_deps` are all proved.
3. C is promoted to proved.

No coordination between A, B, and C is needed. The cascade emerges from
the union of their registries.

## Impact Metric

Impact is computable from the merged dependency graph:

- The **impact** of an open point is the number of conditional declarations
  (transitively) downstream of it.
- Proving a high-impact open point cascades to close the most chains.
- `registry work --sort impact` ranks open points by impact.

This is a pure graph computation on the merged registry data. No special
infrastructure is needed.

## Lean Version Handling

Content addresses depend on normalization behavior, which could change
across Lean versions. The registry handles this by:

- Every entry records its `toolchain` and `level`.
- L0 addresses are pure (no MetaM) and extremely stable across versions.
  These are the safest for cross-version references.
- L1 addresses depend on `whnf` behavior. If Lean changes `whnf`, L1
  addresses may change. The registry treats different toolchain versions
  as potentially producing different addresses for the same declaration.
- Re-indexing on toolchain upgrades is straightforward:
  `registry generate` recomputes all addresses and appends new entries
  if any addresses changed.

## Generation Command

The `registry generate` subcommand is part of the `ca` CLI (`Main.lean`):

1. Loads the compiled environment.
2. Scans for `@[publish]` and `@[open_point]` declarations (or all
   declarations if `--all` is passed).
3. Computes content addresses using the CA library.
4. Classifies status (proved / open / conditional).
5. Writes `registry/declarations.json` and `registry/meta.json`.

```bash
# Generate registry for annotated declarations
lake exe ca registry generate

# Generate registry for all declarations in the environment
lake exe ca registry generate --all

# Generate with L1 normalization
lake exe ca registry generate --level 1

# Dry run: print what would be published without writing files
lake exe ca registry generate --dry-run
```

### When to run

- **Explicitly**, after significant changes: `lake exe registry generate`.
- **In CI**, as a post-build step. A GitHub Action regenerates the registry
  on each push to main and commits the result.
- **Not on every `lake build`**. Generation involves hashing every published
  declaration, which is fast but not free. It should be a deliberate step.

## Summary

| Aspect | Design |
|---|---|
| **Storage** | `registry/` folder in each project's git repo |
| **Publication** | `git push` |
| **Verification** | `lake build` (Lean's kernel) |
| **Discovery** | Static `sources.json` listing known repos |
| **Resolution** | `use` / `resolve%` queries local cache, fetches from sources on miss |
| **Consensus** | Monotonic: one valid proof is enough |
| **Coordination** | Minimal: PR to add one line to `sources.json` |
| **Cascade** | Emerges from union of registries, computed locally |
| **Versioning** | Toolchain recorded per entry; L0 stable across versions |
