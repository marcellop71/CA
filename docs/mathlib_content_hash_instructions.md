# Mathlib Content-Addressed Hashing: Implementation Instructions

> **Historical document.** This was the original design brief written before
> the CA codebase existed (when the project was called `mathlib-stats`). It is
> preserved for reference. For the current design, see the other docs and the
> source code directly.

## Goal

Expand the existing `mathlib-stats` project with a content-addressing module that computes content-addressed hashes for every declaration's type and value, and exports a manifest and analysis data. This is the foundation for a content-addressed mathematical library where theorem identity is determined by mathematical content, not by name or file path.

## Context and Motivation

Mathlib identifies declarations by human-chosen names (`Finset.sum_comm`, `IsNoetherianRing.ideal_fg`). We want to separate **identity** (what a theorem says) from **naming** (how humans refer to it). A content hash of the type expression gives identity; names become metadata pointing to hashes.

This enables: automatic deduplication, name-independent dependencies, structural search by type, and the foundation for a decentralized Merkle-DAG of formal mathematics.

---

## Preamble: Discover the Existing Project

**Before writing any code**, explore the `mathlib-stats` project thoroughly:

1. **Find the project root.** Look for `lakefile.lean` (or `lakefile.toml`) and `lean-toolchain`. Note the exact Lean toolchain version and how Mathlib is declared as a dependency.

2. **Map the source tree.** List all `.lean` files. Understand the module hierarchy — what namespace(s) does the project use? What's the naming convention? Is there a `Main.lean` or a library-style entry point?

3. **Read existing code.** Understand what `mathlib-stats` already does — it likely traverses the `Environment` and collects statistics. Identify:
   - How it imports Mathlib (full import or selective?)
   - How it accesses the `Environment` (does it use `#eval`, `main`, a custom command?)
   - Any existing `Expr` traversal, declaration filtering, or serialization logic
   - Any existing JSON/CSV export infrastructure
   - Any existing Python analysis scripts or tooling

4. **Identify reusable infrastructure.** The content-hashing module should reuse as much as possible:
   - If there's already an environment traversal loop, extend it rather than duplicating
   - If there's already a declaration filter (skipping internal/compiler-generated names), reuse it
   - If there's already JSON export, use the same format/library
   - Match the existing code style: indentation, naming conventions, comment style

5. **Plan the integration.** Based on what you find, decide:
   - Where new files should live in the existing module hierarchy
   - Whether to add new modules under the existing namespace (e.g., `MathlibStats.ContentHash`) or a sibling namespace
   - Whether `lakefile.lean` needs changes (it probably doesn't — Mathlib is already a dependency)
   - How to wire the new functionality into the existing entry point (add a subcommand? a flag? a separate `#eval`?)

**Do not create a separate project. Integrate into the existing one, respecting its conventions.**

---

## Phase 1: Core Content-Hashing Module

### 1.1 Module Structure

Add new files under the existing project namespace. The exact paths depend on what you discover above, but the logical modules are:

```
<existing_project>/
├── ...existing files...
├── <Namespace>/
│   ├── ContentHash/
│   │   ├── Canonical.lean     # canonicalization / normalization
│   │   ├── ExprHash.lean      # core hashing of Lean Expr
│   │   ├── Traversal.lean     # environment traversal (or extend existing)
│   │   └── Export.lean         # JSON export of the manifest
│   └── ...existing modules...
```

If the project already has an environment traversal module, the content-hashing logic may fit as an extension of that module rather than a separate `Traversal.lean`. Use your judgment based on what's already there.

### 1.2 Expression Canonicalization (`Canonical.lean`)

Implement a function `canonicalize : Expr → MetaM Expr` that produces a canonical representative suitable for hashing. This is the most important and subtle part.

**Level 0 — De Bruijn baseline:**

Lean `Expr` already uses de Bruijn indices for bound variables, so α-equivalence is free. However, free variables (`fvar`) and metavariables (`mvar`) need handling:

- For completed declarations (no mvars), there should be no fvars or mvars in the stored type/value. Assert this.
- Universe parameters: declarations are polymorphic in universe variables. Canonicalize universe parameter names to positional indices (`u0`, `u1`, ... in order of first occurrence in the expression). This ensures `theorem foo.{u, v}` and `theorem bar.{α, β}` with the same body get the same hash.

**Level 1 — Reducible unfolding + reduction:**

```
canonicalizeL1 (e : Expr) : MetaM Expr := do
  -- Use Lean's withTransparency to control unfolding
  withTransparency .reducible do
    -- Unfold all @[reducible] definitions
    -- β-reduce
    -- ι-reduce (match/recursor reduction)
    -- ζ-reduce (let bindings)
    let e ← whnf e  -- weak head normal form under reducible transparency
    -- But whnf is not enough — we need to recurse into subexpressions
    -- Implement a full normalization pass that applies whnf at every subexpression
    deepNormalize e
```

`deepNormalize` should recursively descend into the expression, applying `whnf` at each node under `TransparencyMode.reducible`. Be careful about:

- **Performance**: Mathlib has ~180k+ declarations. Normalizing every type is expensive. Profile early. Consider caching normalized subexpressions by their `Expr` pointer.
- **Stability**: the normal form must be deterministic. Using `whnf` from Lean's `MetaM` should be deterministic given the same environment, but verify this.
- **Instance arguments**: typeclass instances appear as arguments in types. Under reducible transparency, instance-synthesized terms are NOT unfolded (instances are typically `@[semireducible]` or `@[instance]`). This is correct — we want `Add ℕ` to stay as `Add ℕ`, not unfold to its implementation.

**Important**: document which `TransparencyMode` you use and why. The choice of transparency determines which terms collapse to the same hash. `reducible` is the conservative choice.

### 1.3 Hashing (`ExprHash.lean`)

After canonicalization, hash the expression to a fixed-size digest.

```
exprHash (e : Expr) : MetaM UInt64 := do
  let ce ← canonicalize e
  pure (hashExpr ce)
```

For the hash function itself:

- **Option A (simple, fast)**: Use Lean's built-in `Hashable Expr` instance after canonicalization. This gives a `UInt64`. Fast, but collisions are possible (birthday bound ~2^32 declarations before collision). Fine for analysis; not for production content-addressing.
- **Option B (production)**: Serialize the canonicalized `Expr` to a canonical byte representation and apply SHA-256. For this, implement `serializeExpr : Expr → ByteArray` that produces a deterministic byte sequence. Use a tagged encoding:

  ```
  .bvar n     → [0x00] ++ varint(n)
  .fvar id    → should not appear (assert)
  .mvar id    → should not appear (assert)
  .sort u     → [0x01] ++ serializeLevel(u)
  .const n us → [0x02] ++ hash(n.toString) ++ length(us) ++ us.map(serializeLevel)
  .app f a    → [0x03] ++ serializeExpr(f) ++ serializeExpr(a)
  .lam n t b  → [0x04] ++ serializeBinderInfo ++ serializeExpr(t) ++ serializeExpr(b)
  .forallE ...→ [0x05] ++ ...
  .letE ...   → [0x06] ++ ...
  .lit l      → [0x07] ++ ...
  .proj t i e → [0x08] ++ hash(t.toString) ++ varint(i) ++ serializeExpr(e)
  ```

  **Critical design decision for `.const`**: When serializing a reference to another declaration (`.const name univs`), do we hash the *name* or the *content hash of the referenced declaration*? 

  - Hashing the name: simpler, but then renaming a dependency changes your hash even if the content is the same.
  - Hashing the content hash of the dependency: gives true content-addressing (your hash depends only on the mathematical content of your transitive dependencies), but requires computing hashes bottom-up in dependency order. **This is the correct approach for the Merkle DAG vision.** It means the hash of `add_comm` transitively includes the hashes of `ℕ`, `HAdd`, `Eq`, etc.

  Implement both modes and compare. Name-based hashing is the simpler starting point; content-based hashing is the goal.

### 1.4 Environment Traversal (`Traversal.lean` or extend existing)

**Check first**: if `mathlib-stats` already has an environment traversal loop, add content-hashing as an additional pass or field in the existing data structure. Don't duplicate traversal logic.

If no suitable traversal exists, create one:

```
structure DeclHash where
  name : Name
  kind : String           -- "theorem", "def", "axiom", "opaque", "inductive", ...
  typeHash : String        -- hex SHA-256 of canonicalized type
  valueHash : Option String -- hex SHA-256 of canonicalized value (None for axioms/opaques)
  typeDeps : List String   -- type hashes of declarations referenced in the type
  valueDeps : List String  -- type hashes of declarations referenced in the value
  module : Name            -- which Mathlib module this lives in

def traverseEnvironment : MetaM (Array DeclHash) := do
  let env ← getEnv
  let mut results := #[]
  for (name, info) in env.constants.fold ... do
    -- Skip internal/compiler-generated declarations
    -- Skip declarations not in the Mathlib namespace
    let typeHash ← computeHash info.type
    let valueHash ← match info.value? with
      | some v => some <$> computeHash v
      | none => pure none
    -- Extract dependency names from the expression
    let typeDeps ← extractConstRefs info.type
    let valueDeps ← match info.value? with
      | some v => extractConstRefs v
      | none => pure #[]
    results := results.push { ... }
  return results
```

**Important considerations:**

- **Proof irrelevance**: For theorems (declarations in `Prop`), all values are definitionally equal. So `valueHash` for theorems is irrelevant — two different proofs of the same proposition should be identified. Set `valueHash := some "PROOF_IRRELEVANT"` (or a fixed sentinel) for all theorems. This is a major simplification: for the type-level DAG, theorem identity IS its type hash.
- **Inductives**: An inductive type generates multiple declarations (the type itself, constructors, recursor). Hash them as a unit — the content hash of an inductive should include all its constructors and the recursor type.
- **Instances**: Record whether a declaration is a typeclass instance (`@[instance]`), and which class it instantiates. This metadata is critical for the "instance coherence" problem.

### 1.5 Export (`Export.lean` or extend existing)

**Check first**: if `mathlib-stats` already exports JSON or CSV, extend that format rather than creating a parallel one. The content-hash fields can be added to existing declaration records.

If building fresh, export to JSON (use Lean's `Lean.Json`):

```json
{
  "lean_toolchain": "leanprover/lean4:v4.x.0",
  "mathlib_commit": "abc123...",
  "transparency": "reducible",
  "hash_mode": "name_based",  // or "content_based"
  "total_declarations": 187432,
  "declarations": [
    {
      "name": "Finset.sum_comm",
      "kind": "theorem",
      "type_hash": "a7f3b2c1...",
      "value_hash": "PROOF_IRRELEVANT",
      "type_deps": ["e1f2a3...", "b4c5d6..."],
      "module": "Mathlib.Algebra.BigOperators.Group.Finset"
    },
    ...
  ]
}
```

Also export a separate **edge list** for graph analysis:

```
# source_type_hash  target_type_hash
a7f3b2c1...  e1f2a3b4...
a7f3b2c1...  b4c5d6e7...
```

### 1.6 Entry Point (extend existing or add subcommand)

**Check first**: how does `mathlib-stats` currently run? If it has a `main` function, add a CLI flag or subcommand (e.g., `--content-hash`). If it uses `#eval`, add a parallel `#eval` block or a new command.

The content-hash entry point should:

1. Imports `Mathlib` (or a specified subset)
2. Calls `traverseEnvironment`
3. Writes the JSON manifest to a file
4. Writes the edge list to a file
5. Prints summary statistics

---

## Phase 2: Analysis (Python)

**Check first**: does `mathlib-stats` already have Python scripts for analysis or visualization? If so, add content-hash analysis as new scripts in the same directory, following the same conventions (imports, style, output format). If the project has a `scripts/`, `analysis/`, or `python/` directory, put new scripts there.

### 2.1 Deduplication Analysis

Given the JSON manifest, compute:

- **Type hash collisions**: declarations with different names but identical type hashes. These are candidate duplicates (same mathematical statement, possibly different proofs).
- **Histogram of hash frequencies**: how many type hashes appear exactly once vs. multiple times?
- **Largest equivalence classes**: which type hashes have the most declarations mapping to them? (Likely basic lemmas that have been restated in different contexts.)

### 2.2 DAG Analysis

Using the edge list:

- **Connected components**: is the content-addressed DAG connected? How many components?
- **Depth distribution**: what's the distribution of longest-path-to-root for each declaration?
- **Centrality**: which type hashes have the highest betweenness centrality, PageRank, or in-degree? These are the "most foundational" results.
- **Compare with MathLibGraph**: the DeepMind paper analyzed the name-level dependency graph. How does the content-level DAG differ? Are there edges that disappear (because a name-level dependency was just a renaming) or new structures that emerge?

### 2.3 Naming Analysis

- **Name predictability**: given a type hash, how predictable is the name? Train a simple model (even a rule-based one) that takes a canonicalized type and predicts the Mathlib name. Measure accuracy. This tells us how much information the name carries beyond the type.
- **Naming conflicts**: are there cases where the same name maps to different type hashes across different Mathlib versions? (Use git history.)
- **Orphan hashes**: type hashes that exist but whose names are "internal" or autogenerated. How much of Mathlib is "unnamed" mathematics?

### 2.4 Tooling

Write Python scripts for all of the above. Use `networkx` for graph analysis, `matplotlib`/`plotly` for visualization. Output:

- `dedup_report.json`: list of duplicate clusters
- `dag_stats.json`: summary statistics
- `centrality_ranking.csv`: declarations ranked by DAG centrality
- Visualizations: degree distribution, depth distribution, connected component sizes

---

## Phase 3: Structural Search Prototype

### 3.1 Type Pattern Index

Build an index that allows searching by type structure:

- Serialize each canonicalized type into a "type skeleton" — replace specific types with wildcards, keep the overall structure. For example, `∀ (s : Finset ?α) (f : ?α → ?β), s.sum f = ...` becomes a searchable pattern.
- Implement unification-based search: given a query pattern, find all type hashes that unify with it.
- This is essentially `exact?` / `apply?` but running against the content-addressed store instead of the live environment.

### 3.2 Storage Backend

For the prototype, use SQLite:

```sql
CREATE TABLE declarations (
    type_hash TEXT PRIMARY KEY,
    canonical_type BLOB,      -- serialized Expr
    names TEXT,               -- JSON array of all names mapping to this hash
    kind TEXT,
    module TEXT
);

CREATE TABLE dependencies (
    source_hash TEXT,
    target_hash TEXT,
    FOREIGN KEY (source_hash) REFERENCES declarations(type_hash),
    FOREIGN KEY (target_hash) REFERENCES declarations(type_hash)
);

CREATE TABLE naming_layers (
    layer_name TEXT,          -- e.g. "mathlib_default", "bourbaki", "pedagogical"
    type_hash TEXT,
    display_name TEXT,
    PRIMARY KEY (layer_name, type_hash)
);
```

---

## Phase 4: Defeq Equivalence Certificates (Stretch Goal)

### 4.1 Defeq Oracle

Implement a service that, given two type hashes `h1` and `h2`, attempts to prove their canonical types are definitionally equal:

```lean
def checkDefeq (e1 e2 : Expr) : MetaM (Option DefeqCertificate) := do
  if ← isDefEq e1 e2 then
    -- Record the reduction trace as a certificate
    some <$> buildCertificate e1 e2
  else
    return none
```

A `DefeqCertificate` should be a serializable witness that can be verified without re-running the full `isDefEq` check. This is the formal math equivalent of a fraud proof.

### 4.2 Equivalence Class Merging

When a defeq certificate is produced, merge the two type hashes into one equivalence class (union-find over hashes). The manifest then includes:

```json
{
  "defeq_certificates": [
    {
      "hash_a": "a7f3b2...",
      "hash_b": "c8d9e0...",
      "certificate": "..."
    }
  ]
}
```

---

## Technical Notes

### Performance Budget

- Mathlib has ~180k+ declarations. Canonicalizing and hashing each type is the bottleneck.
- Budget: ~1 hour total for a full Mathlib traversal on a reasonable machine.
- Parallelize where possible: declarations can be hashed independently once the environment is loaded.
- Profile early: if Level 1 canonicalization is too slow, fall back to Level 0 for the initial analysis and add Level 1 incrementally.

### Correctness Checks

- **Idempotence**: `canonicalize (canonicalize e) = canonicalize e`. Test this.
- **Determinism**: same expression, same environment → same hash. Always. Test by running twice.
- **Proof irrelevance**: verify that for any two proofs `p1 p2 : P` where `P : Prop`, the type hashes are identical and the value hashes are both the sentinel.
- **Sanity check**: `Nat.add_comm` and `Nat.add_comm'` (if both exist) should have the same type hash. Look for known Mathlib duplicates and verify they collide.

### What NOT to Do

- Don't try to solve full defeq hashing in Phase 1. Level 0 + Level 1 is the target.
- Don't build a blockchain or token system. This is the data layer — pure analysis.
- Don't try to handle `sorry` — skip any declaration that transitively depends on `sorry`.
- Don't normalize proof terms (they're irrelevant). Only normalize types and data-valued definitions.

---

## Deliverables

1. **New modules in `mathlib-stats`** implementing content-hashing, integrated with existing project conventions
2. **JSON manifest** of all Mathlib declarations with content hashes (extending existing export format if one exists)
3. **Python analysis scripts** (in existing scripts directory) producing dedup reports, DAG statistics, centrality rankings
4. **Summary document** with key findings: how many duplicates exist, what the DAG looks like, which results are most central, and how the content-level view differs from the name-level view

## Success Criteria

The project succeeds if it can answer these questions empirically:

1. How many distinct mathematical statements does Mathlib contain? (distinct type hashes)
2. How much duplication exists? (names mapping to the same type hash)
3. What is the "shape" of the content-addressed DAG? (depth, width, centrality distribution)
4. Is the content DAG meaningfully different from the name-level dependency graph?
5. Can we identify "the same lemma stated in two different ways" via Level 1 hash collisions?
