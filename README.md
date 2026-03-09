# CA — Content-Addressing for Lean 4

### Warning: this is an early prototype, still subject to conceptual and implementation flaws and API churn.

Content-addressed hashing and decentralized registry for Lean 4
declarations. Assigns a stable SHA-256 identity to every declaration based
on its mathematical content (type structure), not its human-chosen name,
file, or project.

Two declarations with different names but identical mathematical content
receive the same address.

## Why

Lean declarations are identified by name — a human-chosen path like
`Finset.sum_comm`. Renaming, moving, or reorganizing a library breaks all
downstream references, even though the mathematics hasn't changed.

The underlying issue is conceptual: **one should import a result, not a
file.** A mathematician using a lemma does not care which file it lives in,
which project hosts it, or what namespace convention was chosen. What
matters is the mathematical content — the statement itself.

Content addresses decouple identity from naming:

- **Stable** — refactors don't break addresses if the math is unchanged
- **Universal** — no project, file, or import context required
- **Cross-project** — shared key space across the entire ecosystem
- **Decentralized** — no central authority; anyone can verify by re-hashing

See [paper/main.pdf](paper/main.pdf) for the full motivation.

## How it works

### Content addressing

1. **Canonicalize** the type expression (strip metadata, rename universe
   params to positional indices, optionally unfold reducibles via `whnf`)
2. **Serialize** the canonical `Expr` to a tagged byte format
3. **Hash** with SHA-256 (OpenSSL FFI)

Two canonicalization levels:

| Level | What it does | Requires |
|-------|-------------|----------|
| L0 (default) | Universe renaming + mdata stripping | Pure |
| L1 | L0 + reducible-transparency `whnf` normalization | MetaM |

Two hashing modes:

| Mode | `.const` references become | Effect |
|------|---------------------------|--------|
| Name-based (default) | The declaration's `Name` string | Fast, stable within a single library |
| Content-based (Merkle DAG) | The 32-byte content hash of the dependency | True content identity across libraries |

For theorems, the value hash is the sentinel `PROOF_IRRELEVANT` — identity
is determined by what is proved, not how.

See [docs/address.md](docs/address.md) for the full addressing design.

### Decentralized registry

Each participating Lean project hosts a `registry/` folder containing an
append-only manifest of its published declarations. The global registry is
the union of all project-local registries — no central server required.

- **Publication** is `git push`
- **Verification** is `lake build` (Lean's kernel is the authority)
- **Consensus** is trivial: one valid proof is enough
- **Discovery** is a curated `sources.json` listing known repos

Authors annotate their code with `@[publish]` and `@[open_point]`
attributes. A generation command (not yet implemented) will scan the
environment, compute content addresses, classify declaration status
(proved / open / conditional), and write the registry folder.

See [docs/registry-design.md](docs/registry-design.md) for the full
registry architecture.

## Using CA in your project

This section explains how to use CA in your own Lean project to annotate
theorems and participate in the decentralized registry.

### Step 1: Add the dependency

In your project's `lakefile.lean`:

```lean
require ca from git
  "https://github.com/marcellop71/CA" @ "main"
```

Then fetch dependencies:

```bash
lake update
lake build
```

### Step 2: Annotate your declarations

Import `CA` in any `.lean` file where you want to annotate declarations:

```lean
import CA
```

Use `@[open_point]` to mark a `Prop` definition as an open problem — a
mathematical statement that you are publishing without a proof:

```lean
@[open_point "Bertrand's postulate, elementary form"]
def BertrandPostulate : Prop :=
  ∀ n : Nat, n ≥ 1 → ∃ p, Nat.Prime p ∧ n < p ∧ p < 2 * n
```

Use `@[publish]` to mark any declaration (theorem, definition, axiom) for
publication to the registry:

```lean
@[publish "Commutativity of addition over naturals"]
theorem my_add_comm : ∀ a b : Nat, a + b = b + a := Nat.add_comm
```

A theorem that depends on an open point is automatically classified as
**conditional** — proved modulo unproved hypotheses:

```lean
@[publish "Consequence of Bertrand's postulate"]
theorem prime_between (n : Nat) (h : BertrandPostulate) (hn : n ≥ 1) :
    ∃ p, Nat.Prime p ∧ n < p ∧ p < 2 * n :=
  h n hn
```

#### Retroactive annotation

You can annotate declarations from other files or even upstream
dependencies without modifying their source:

```lean
import CA
import MyProject.Theorems

attribute [open_point "My conjecture"] MyProject.SomeConjecture
attribute [publish "Key lemma"] MyProject.some_lemma
```

### Step 3: Query annotations

You can inspect which declarations are annotated in the current
environment:

```lean
open CA.Registry Lean in

-- Check individual declarations
#eval isOpenPoint (← getEnv) `BertrandPostulate       -- true
#eval isPublished (← getEnv) `my_add_comm             -- true

-- List all annotated declarations
#eval getOpenPoints (← getEnv)
#eval getPublished (← getEnv)
```

### Step 4: Generate the registry folder

Add `#ca_registry "registry/"` at the end of your registry file. The
registry is generated automatically during `lake build` — no separate
command or external binary needed:

```lean
import CA
import MyProject.Theorems

attribute [open_point] MyProject.SomeConjecture
attribute [publish] MyProject.some_lemma

#ca_registry "registry/"
```

When `lake build` compiles this file, it writes:

```
my-project/
└── registry/
    ├── declarations.json    # address, name, status, type, deps for each declaration
    └── meta.json            # project summary (open points, proved, conditional)
```

### Step 5: Publish

Commit the `registry/` folder to your git repo and push. Your project is
now a node in the decentralized registry. Anyone can discover your
declarations by their content address.

To make your registry discoverable by resolution tools (`use`, `resolve%`),
add your project to the `sources.json` in the CA repository — a one-line
PR.

### What your project looks like

```
my-project/
├── lakefile.lean                  # require ca from git "..." @ "main"
├── MyProject/
│   ├── Definitions.lean           # @[open_point] annotations
│   └── Theorems.lean              # @[publish] annotations
├── MyProject/Registry.lean        # (optional) retroactive annotations
└── registry/                      # auto-generated, committed to git
    ├── declarations.json
    └── meta.json
```

### Summary of the workflow

| Step | What you do | What happens |
|------|-------------|--------------|
| 1 | Add `require ca` to `lakefile.lean` | CA library available in your project |
| 2 | Add `@[publish]` / `@[open_point]` to declarations | Declarations marked for the registry |
| 3 | Add `#ca_registry "registry/"` to your registry file | Registry generated during `lake build` |
| 4 | `git add registry/ && git push` | Your project is a registry node |

## CLI

The `ca` executable provides batch indexing and registry generation
commands.

```bash
# Generate registry from @[publish]/@[open_point] annotations
ca registry -m MyProject.Registry -o registry/

# Load a module, compute addresses, store to Redis
ca fetch -m Mathlib

# Compute addresses and export a JSON manifest
ca address -m Mathlib

# Level 1 canonicalization with Merkle DAG hashing
ca address --level 1 --mode content

# Single declaration lookup (checks Redis first, falls back to env)
ca address --name Nat.add_comm
```

### `registry`

Generates `declarations.json` and `meta.json` from `@[publish]` and
`@[open_point]` annotations. Standalone alternative to `#ca_registry` for
environments where the CA binary shares the same toolchain and search paths.

### `fetch`

Loads a Lean environment, computes name-based content addresses, and stores
every declaration (name, kind, type, address, dependencies) to Redis.
Requires a running Redis instance.

### `address`

Computes content addresses and exports a JSON manifest and optional TSV edge
list. Supports both name-based and content-based (Merkle DAG) modes. Can
also look up a single declaration by name. Requires a running Redis instance
for single-declaration lookups.

## Modules

### Core — content addressing engine

| Module | Description |
|--------|-------------|
| `CA.Canonical` | L0 (pure) and L1 (MetaM) canonicalization |
| `CA.SHA256` | SHA-256 FFI wrapper (OpenSSL EVP) |
| `CA.ExprHash` | Expr serialization, `DeclHash`, name-based and content-based batch hashing |
| `CA.Export` | JSON manifest, TSV edge list, summary statistics |
| `CA.Util` | `collectConstants`, `constantKind` helpers |

### Registry — decentralized publication

| Module | Status | Description |
|--------|--------|-------------|
| `CA.Registry.Basic` | implemented | `OpenPointEntry`, `PublishEntry` structures, `NameMapExtension`s, query API |
| `CA.Registry.Attributes` | implemented | `@[publish]` and `@[open_point]` attribute registration and validation |
| `CA.Registry.Generate` | implemented | `#ca_registry` command: status classification, content hashing, JSON output |
| `CA.Registry.Resolve` | not yet | `use`, `use!`, `resolve%` elaborators |
| `CA.Registry.Sources` | not yet | `sources.json` parsing, remote registry fetching, local cache |

## Building

Requires OpenSSL dev headers (for SHA-256 FFI). Redis is only needed for
the `fetch` and `address` CLI commands — the library and registry
attributes work without it.

```bash
# Install OpenSSL dev headers (Ubuntu/Debian)
sudo apt install libssl-dev

# Build
lake update
lake build
```

## Dependencies

| Dependency | Purpose |
|---|---|
| [lean4-cli](https://github.com/leanprover/lean4-cli) | CLI argument parsing |
| [redis-lean](https://github.com/marcellop71/redis-lean) | Redis FFI (hiredis) for `fetch`/`address` commands |
| [batteries](https://github.com/leanprover-community/batteries) | `NameMapExtension` for registry attributes |
| OpenSSL (`libssl`, `libcrypto`) | SHA-256 via EVP API (C FFI) |

Lean toolchain: `leanprover/lean4:v4.29.0-rc1`

## Project structure

```
CA/
├── lakefile.lean                  # package config, FFI build targets
├── lean-toolchain
├── CA.lean                        # re-exports all modules
├── CA/
│   ├── Canonical.lean             # L0/L1 canonicalization
│   ├── SHA256.lean                # SHA-256 FFI binding
│   ├── ExprHash.lean              # Expr serialization, batch hashing
│   ├── Export.lean                # JSON manifest, edge list, stats
│   ├── Util.lean                  # collectConstants, constantKind
│   ├── sha256/
│   │   └── sha256_shim.c         # OpenSSL EVP wrapper
│   └── Registry/
│       ├── Basic.lean             # entry types, extensions, query API
│       ├── Attributes.lean        # @[publish], @[open_point]
│       └── Generate.lean          # #ca_registry command, status classification
├── Main.lean                      # CLI entry point (fetch, address, registry)
├── paper/
│   └── main.tex                   # paper source
└── docs/
    ├── address.md                 # addressing pipeline design
    ├── registry-design.md         # decentralized registry architecture
    ├── l1-batching.md             # L1 micro-batching strategy
    ├── whnf-native-crash.md       # whnf SIGSEGV investigation
    ├── decentralized-formal-math.md  # vision document
    └── mathlib_content_hash_instructions.md  # original implementation notes
```

## Docs

- [address.md](docs/address.md) — design of the addressing pipeline
- [registry-design.md](docs/registry-design.md) — decentralized registry architecture
- [l1-batching.md](docs/l1-batching.md) — L1 normalization technique and micro-batching
- [whnf-native-crash.md](docs/whnf-native-crash.md) — `whnf` SIGSEGV crash investigation
- [decentralized-formal-math.md](docs/decentralized-formal-math.md) — vision for decentralized formal mathematics
- [paper/main.pdf](paper/main.pdf) — paper
