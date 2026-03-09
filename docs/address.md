# Content Addressing

The `address` subcommand computes a content address for every declaration in the environment. A content address identifies a declaration by its mathematical content rather than its human-chosen name. Two declarations with different names but identical mathematical content receive the same address.

## Overview

The address of a declaration is computed in two stages:

1. **Canonicalization** — reduce the expression to a canonical form that erases irrelevant differences
2. **Hashing** — compute a deterministic hash of the canonical expression

The result is a hex-encoded SHA-256 (256-bit) address for the type (and optionally the value) of each declaration.

## Stage 1: Canonicalization

Canonicalization transforms an `Expr` so that expressions that differ only in irrelevant ways become identical. Two levels are available.

### Level 0 (default)

Level 0 is pure (no `MetaM`) and ensures alpha-equivalence:

- **Universe parameter renaming.** Universe parameters are renamed to positional indices (`u_0`, `u_1`, ...) based on first-occurrence order in the expression. This ensures `theorem foo.{u, v} : ...` and `theorem bar.{α, β} : ...` with the same body get the same address.
- **Metadata stripping.** `.mdata` annotations are removed. These carry source-location and elaboration metadata that is irrelevant to mathematical content.
- **Binder names.** Lean 4 `Expr` uses de Bruijn indices for bound variables, so alpha-equivalence is already built in. Binder names do not affect the hash.

### Level 1

Level 1 extends Level 0 with reducible-transparency normalization (requires `MetaM`):

- **Reducible unfolding.** All `@[reducible]` definitions are unfolded.
- **Beta-reduction.** Function applications `(fun x => body) arg` are reduced.
- **Iota-reduction.** Match/recursor applications are reduced.
- **Zeta-reduction.** Let bindings are substituted away.

Normalization uses `whnf` at every subexpression under `TransparencyMode.reducible`. This collapses type-level abbreviations and reducible definitions to the same canonical form.

Instance arguments (typically `@[semireducible]` or `@[instance]`) are **not** unfolded under reducible transparency, which is the correct behavior — `Add Nat` stays as `Add Nat`.

## Stage 2: Hashing

After canonicalization, the expression is serialized into a `ByteArray` with a unique tag byte per `Expr` constructor followed by the serialized children. The serialization:

- Tags each `Expr` constructor with a distinct byte (`.bvar` → `0x01`, `.const` → `0x05`, `.app` → `0x06`, etc.)
- Ignores binder names (they are not mathematically significant)
- Strips `.mdata` transparently
- Includes `BinderInfo` (default, implicit, strict implicit, instance implicit) in lambda and forall serializations

The serialized bytes are then hashed with SHA-256 (via OpenSSL EVP API) and formatted as a 64-character hexadecimal string, providing robust collision resistance for large corpora.

### Addressing modes

Two modes determine how references to other declarations (`.const name levels`) are handled:

| Mode | `.const` hash input | Use case |
|------|---------------------|----------|
| **Name-based** (default) | The declaration's `Name` | Stable across runs; address changes if dependencies are renamed |
| **Content-based** (Merkle DAG) | The content address of the referenced declaration | True content addressing; address depends only on transitive mathematical content |

Content-based mode processes declarations in topological (dependency) order so that each declaration's address incorporates the addresses of its dependencies, forming a Merkle DAG.

## Proof irrelevance

For theorems (declarations in `Prop`), all proofs are definitionally equal. The value address is set to the sentinel `PROOF_IRRELEVANT` rather than hashing the proof term. This means a theorem's identity is determined entirely by its type address — what it proves, not how.

## Output

The `address` subcommand produces:

- **JSON manifest** (`manifest.json` by default) — contains metadata (toolchain, transparency, hash mode) and an array of declaration records, each with `name`, `kind`, `type_hash`, `value_hash`, `type_deps`, `value_deps`.
- **Edge list** (optional, `--edges` flag) — TSV of `source_type_hash → target_type_hash` edges for graph analysis.
- **Redis storage** — each declaration's address data is stored in `ca:decl:{name}` with fields `addr_type`, `addr_value`, `addr_type_deps`, `addr_value_deps`.

## Usage

```bash
# Default: level 0, name-based (all declarations)
ca address

# Level 1 canonicalization with Merkle DAG addressing
ca address --level 1 --mode content

# Custom output paths
ca address --output hashes.json --edges edges.tsv

# Single declaration lookup
ca address --name Nat.add_comm
ca address --name Nat.add_comm --level 1 --mode content -m Mathlib.Data.Nat.Defs
```

When `--name` is provided, the command computes the address for just that declaration, prints it, stores it to Redis, and exits without writing a manifest file. In content-based mode, dependencies of the named declaration use name-based fallback (since only one declaration is computed). For fully content-based addresses, use the batch mode.

## Source modules

| Module | Role |
|--------|------|
| `CA.Canonical` | Canonicalization (L0 pure, L1 MetaM) |
| `CA.SHA256` | SHA-256 FFI binding (OpenSSL EVP) and hex formatting |
| `CA.ExprHash` | Expr serialization, content-based hashing, `DeclHash` structure, batch computation |
| `CA.Export` | JSON manifest, edge list, summary statistics |
| `CA.Util` | `collectConstants`, `constantKind` helpers |
