# CA — Content-Addressing for Lean 4

### Warning: this is an early prototype, still subject to conceptual and implementation flaws and API churn.

Content-addressed identity for Lean 4 declarations: a SHA-256 address
derived from what a declaration *is* — its elaborated type and value,
with everything it references addressed the same way — rather than from
the name, file or project it happens to live in.

Two declarations with different names but identical mathematical
content receive the same address. A declaration whose statement quietly
changes — because a constant it mentions was redefined — does not.

## What it is for

The unit a mathematician cares about is a result, not a file. CA makes
that unit addressable, which is what the following need:

- **Referencing a result you cannot locate.** You know the statement;
  you do not know the repository, package, module or revision that
  holds it. A statement id is computable from the proposition alone, by
  anyone, without knowing who proved it.
- **Asking "has this already been proved?"** Two libraries that prove
  the same theorem produce the same statement id, so duplication is a
  lookup rather than a literature search. This is the question an agent
  must answer both before starting work and before offering it back.
- **Citing across refactors.** Renaming a declaration, moving it
  between files, reorganising namespaces, or renaming anything it
  references leaves its address unchanged.
- **Knowing when a statement was weakened.** Because a reference is
  embedded by *its own* address, a redefined constant produces a
  different statement id. "This proves the same thing it did before" is
  a comparison of two hashes.
- **Alternative proofs as first-class objects.** Two proofs of one
  theorem share a statement id and differ in their declaration id, so a
  store can hold both instead of overwriting one with the other.
- **Incremental work that stops where mathematics stops.** Since a
  dependent embeds a theorem's *statement*, re-proving a theorem
  invalidates nothing downstream; changing a definition's value
  invalidates everything that could unfold it.
- **Metadata that follows the statement.** A LaTeX rendering, a prose
  description or a translation belongs to a statement, not to a file
  path — keyed by statement id it is written once and shared by every
  proof of it and every project that uses it.
- **Decentralised publication.** Addresses are computed, not assigned:
  no registrar, no coordination, and anyone can verify by re-hashing.

CA is the addressing layer only. Building a store, a verifier or a
registry on top of it is a separate concern — see *Related work* below.

## The identity: three ids per declaration

`CA.RefHash` computes, for every declaration, three ids over canonical
serialisations in which each referenced constant is replaced by its own
id (names never enter) and mutual or inductive families are hashed as
one strongly connected component:

| id | of what | answers |
|----|---------|---------|
| `stmt` | the type, with universe arity | *what does this claim?* |
| `decl` | the whole `ConstantInfo` — kind, flags, type, value, structural fields | *which declaration is this, exactly?* |
| `ref` | `stmt` for theorems, `decl` otherwise | *what may a dependent rely on?* |

`ref` is the interesting one. A dependent of a theorem can observe only
its statement — by proof irrelevance no term can distinguish two proofs
of one proposition — while a dependent of a definition may unfold it.
Embedding `ref` therefore makes identity propagate exactly as far as
mathematical dependence does.

The price is exactness with respect to the toolchain: because
references are by id, a change in Lean's core propagates upward. The
older name-based hash below was stable across releases precisely
because it was blind to what a name pointed at.

See [`docs/ref-hash.md`](docs/ref-hash.md) for the full construction,
and `lake exe refhash-test` for the properties it is tested against
(α-renaming invariance, proof irrelevance, value sensitivity, blocks,
determinism, order independence).

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

`CA.ExprHash` also keeps two older, weaker hashing modes, still used
for indexing and for compatibility with addresses computed before
`RefHash` existed:

| Mode | `.const` references become | Effect |
|------|---------------------------|--------|
| Name-based | The declaration's `Name` string | Fast and stable across toolchains, but blind: two libraries whose `IsSolvable` differ hash a theorem about it identically |
| Content-based (Merkle DAG) | The 32-byte content hash of the dependency's *type* | Content identity across libraries, but type-only: every definition of a given type collides |

`CA.RefHash` supersedes both for identity purposes; the name-based hash
is worth keeping as a coarse, version-spanning handle.

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
attributes; `#ca_registry` (or `ca registry`) scans the environment,
computes content addresses, classifies each declaration (proved / open
/ conditional) and writes the registry folder during `lake build`.
Resolution from the other side — `use`, `resolve%`, and reading other
projects' registries through `sources.json` — is designed but not yet
implemented, so today the registry is publishable but not yet
consumable.

See [docs/registry-design.md](docs/registry-design.md) for the full
registry architecture.

## Using CA in your project

This section explains how to use CA in your own Lean project to annotate
theorems and participate in the decentralized registry.

### Step 1: Add the dependency

In your project's `lakefile.lean`:

```lean
require ca from git
  "https://github.com/marcellop71/CA" @ "v4.33.0"
```

The tag tracks the Lean toolchain: use the tag matching your
`lean-toolchain`, or `@ "main"` if you are following development.

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
├── lakefile.lean                  # require ca from git "..." @ "v4.33.0"
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
| `CA.RefHash` | `stmt` / `decl` / `ref` ids: name-free content identity per declaration (proof-irrelevant references for theorems, value-inclusive otherwise), Merkle-hashed expressions, SCC blocks for mutual/inductive families — see [`docs/ref-hash.md`](docs/ref-hash.md); tests: `lake exe refhash-test` |
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

## Where this is used, and what it is not

CA is the addressing layer. It computes ids and can generate a
project-local registry folder; it does not store declarations, run the
kernel, or serve queries.

- [declbuild](https://github.com/proofinity-it) builds on it: a
  declaration-granular store keyed by these ids, a kernel re-checker
  that re-verifies a stored declaration against an explicitly trusted
  cone, statement-keyed annotations, and a registry whose unit of
  sharing is a declaration rather than a repository. Public release
  intended shortly.

### Related work

[LeanArchitect](https://github.com/hanwenzhu/LeanArchitect) (Zhu, ITP
2026) predates this repository and is worth reading before this one. It
extracts a *blueprint* — the informal-statement dependency graph that
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) projects
plan with — directly from Lean source: declarations carry a
`@[blueprint]` attribute, the edges between nodes are inferred from the
elaborated declarations instead of being maintained by hand in LaTeX,
and the result is exported as JSON and LaTeX with progress trackable by
humans and by provers. It does two things this library does not: it
keeps a human-authored mathematical narrative attached to formal code,
and it fits a workflow mathematicians already use.

It is complementary rather than competing. A blueprint node is
identified by name plus an author-chosen label and lives in one
repository, so it is exactly as portable as that project's names; a
content address belongs to no repository but authors nothing. If a
blueprint node recorded the statement ids of the declarations that
discharge it, the node would survive renames and become comparable
across projects — and its informal text is the best available content
for anything keyed by statement rather than by file path.

### What an address covers, and what it cannot

An address is a hash of a *canonical form*, so the honest question is
never "is it exact?" but "what does the canonical form erase?".

**Erased by construction (L0).** Binder names (de Bruijn), universe
parameter names (positional), `mdata` and source positions, the
declaration's own name, and — because `RefHash` embeds each reference
by *its* id — the names of everything it refers to, wherever those live
and however they were later renamed or moved. Two structurally
identical declarations therefore coincide even across libraries, under
whatever names each of them chose. For a *reference* to a theorem the
proof is erased as well, by proof irrelevance, so re-proving a theorem
changes nothing for anything that uses it.

**Erased with L1.** Reducible-transparency `whnf` before hashing:
`abbrev`s, `@[reducible]` definitions and type synonyms collapse, so
statements that differ only by such a synonym share an address.

**Not erased today, but reachable by more normalisation.** Binder info
currently enters the hash, and a level that ignored it would merge API
variants stating the same proposition. Unfolding at *default*
transparency would merge more; Lean's kernel decides that equality
pairwise, but hashing needs a canonical representative, and normalising
at default transparency neither terminates cheaply nor stays stable
across library refactors — which is why L1 stops at reducible.
Structure-eta and instance-argument normalisation sit in the same
category: possible, each with a cost in time and in false merges.

**Not reachable by any normal form.** Two genuinely different
formalisations of the same mathematics are related by a *proof*, not by
a normal form, and finding that proof is theorem proving. No hashing
scheme will merge them, and one that appeared to would be lying.

The productive way to cover that last case is to record it rather than
hash it: a proof of `A ↔ B` is itself a declaration with its own
address, so "these two statements are equivalent, and here is the
term that shows it" becomes ordinary data in the same store, checkable
by the same kernel. Search layers (type fingerprints, embeddings) can
propose such links; only a proof establishes one.

**Operationally**: identity is exact with respect to the toolchain's
core, since references are by id — a change in Lean's core propagates
upward, where the older name-based hash was stable precisely because it
was blind. And computing ids for a whole Mathlib-sized environment is a
single-threaded pass of minutes, worth caching.

## Building

The default target is the `CA` library. Redis is only needed for the
`ca` CLI executable (`fetch` and `address` subcommands).

### With Nix (recommended, any platform)

```bash
nix develop    # enter the dev shell (or use direnv with the included .envrc)
lake build     # build the CA library
lake build ca  # build the CLI executable (requires Redis native libs)
```

The Nix flake provides Lean 4, OpenSSL, hiredis, and all other native
dependencies. Works on Linux and macOS.

### Without Nix (Ubuntu/Debian)

```bash
# Install OpenSSL dev headers
sudo apt install libssl-dev

# Build the library
lake update
lake build

# Build the CLI (also needs hiredis)
sudo apt install libhiredis-dev
lake build ca
```

### Build targets

| Command | What it builds | Native deps required |
|---------|---------------|---------------------|
| `lake build` | `CA` library (default) | OpenSSL (`libssl`, `libcrypto`) |
| `lake build ca` | CLI executable | OpenSSL + hiredis |

## Dependencies

| Dependency | Required for | Purpose |
|---|---|---|
| [batteries](https://github.com/leanprover-community/batteries) | library | `NameMapExtension` for registry attributes |
| OpenSSL (`libssl`, `libcrypto`) | library | SHA-256 via EVP API (C FFI) |
| [lean4-cli](https://github.com/leanprover/lean4-cli) | CLI only | CLI argument parsing |
| [redis-lean](https://github.com/marcellop71/redis-lean) | CLI only | Redis FFI (hiredis) for `fetch`/`address` commands |

Lean toolchain: `leanprover/lean4:v4.33.0` (see `lean-toolchain`; the
git tag `v4.33.0` of this repository tracks that toolchain, and
`batteries` / `Cli` are pinned to the matching releases).

