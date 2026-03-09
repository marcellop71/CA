# L1 Normalization and Batching Strategy

## What L1 does

Level 0 canonicalization is pure: rename universe parameters to positional
indices and strip `.mdata`. It makes `theorem foo.{u, v}` and
`theorem bar.{α, β}` hash equally when their bodies are identical, but it
cannot see through `@[reducible]` aliases.

Level 1 adds reducible-transparency normalization via Lean's native `whnf`.
This collapses type-level abbreviations so that, for example, `a + b` (which
is `@HAdd.hAdd Nat Nat Nat instHAddNat a b`) and a direct call to
`@Nat.add a b` produce the same canonical form. The result is strictly larger
equivalence classes than L0.

### `deepNormalize`

`deepNormalize` (`CA.Canonical`) is a recursive normalizer that applies `whnf`
at every subexpression under `withTransparency .reducible`:

```
deepNormalize(e, depth):
  if depth ≥ 256: return e
  e ← whnf e              -- native, under reducible transparency
  match e:
    .app f a       → .app (deepNormalize f) (deepNormalize a)
    .lam n t b bi  → normalize t; open binder with withLocalDecl;
                     normalize body; re-abstract with mkLambdaFVars
    .forallE ...   → same pattern, re-abstract with mkForallFVars
    .letE _ _ v b  → normalize v; substitute into b; normalize b
    .mdata _ e     → deepNormalize e  (strip)
    .proj t i e    → normalize e; whnf the projection again
    _              → return e
```

Binders are opened with `withLocalDecl` and closed with
`mkLambdaFVars`/`mkForallFVars` to avoid loose-bvar panics from instantiating
under a binder without introducing a free variable.

`canonicalizeL1` composes `deepNormalize` with `canonicalizeL0` — normalize
first, then rename universe params and strip any remaining mdata.

## The crash problem

Native `whnf` is implemented in C (`@[extern "lean_whnf"]`). It has no
heartbeat checks, so when it overruns a resource limit the result is an
uncatchable SIGSEGV rather than a Lean exception.

Two distinct failure modes were discovered empirically on Mathlib
(`Mathlib.Algebra.Group.Basic`, ~58k declarations):

### Crash mode 1: MetaM state accumulation (types)

Processing declaration types with `whnf` in a single MetaM session crashes
after ~25k declarations. The crash point is not declaration-specific —
processing the same declarations in reverse order crashes at the same *count*
but at different declarations. Running any individual "crashing" declaration
in a fresh MetaM session succeeds.

The cause is cumulative growth of MetaM internal state: the `whnf` cache,
discriminant trees, and type-class instance tables. After ~25k reductions
the accumulated state causes the native code to exceed a stack or memory
limit.

### Crash mode 2: process-level memory growth (values)

Applying `whnf` to definition *values* (as opposed to types) causes
process-level memory growth that triggers SIGSEGV after ~30k declarations.
This crash persists **regardless of batch size** — even with a fresh MetaM
session per declaration, the process RSS grows monotonically and eventually
crashes. The likely cause is that normalizing large definition bodies
allocates `Expr` objects that survive garbage collection due to references
from the accumulated results.

## The solution

### Micro-batching (crash mode 1)

The declarations are processed in micro-batches. Each batch gets a **fresh
MetaM session** via `runMetaM`, which discards the previous session's whnf
cache and internal state.

```
for each batch of ≤10 declarations:
    runMetaM env do          -- fresh session, empty caches
      for decl in batch:
        canonicalize type    -- whnf runs in clean state
        serialize + hash
```

The default batch size for L1 is **10**. Empirically, batch 10 works; batch
20 crashes. For L0, the batch size is the entire array (single session) since
L0 is pure and never calls `whnf`.

This is implemented in `hashBatchPhase1` (`CA.ExprHash`). When L1
canonicalization throws an exception for a particular declaration, it falls
back to L0 for that declaration and continues.

### L0-only values (crash mode 2)

`hashValue` always canonicalizes values with L0 regardless of the selected
level. This avoids crash mode 2 entirely:

- **Theorems**: value hash is the sentinel `PROOF_IRRELEVANT` (proof
  irrelevance — all proofs of the same Prop are equal)
- **Definitions / opaques**: value is canonicalized with `canonicalizeL0`
  (universe renaming + mdata stripping, no whnf)

The result is an asymmetric strategy: **types get L1, values get L0**.

## Processing architecture

Hash computation is split into two phases separated by an intermediate
`PreDeclHash` structure.

### Phase 1: canonicalize + hash

`hashBatchPhase1` runs in a single `runMetaM` session. For each declaration
in the batch:

1. Canonicalize the type with the selected level's canon function
2. Serialize the canonical type to a `ByteArray`
3. SHA-256 hash the serialized bytes
4. Hash the value (always L0, as described above)
5. Collect type and value dependencies via `collectConstants`
6. Store the result as a `PreDeclHash`, which holds the canonical `Expr`
   (needed for pretty-printing) but not the pretty-printed string

Pretty-printing (`ppExpr`) is deliberately excluded from Phase 1 because it
runs in MetaM and would add pressure to the same session that runs `whnf`.

### Phase 2: pretty-print

`hashBatchPhase2` runs in a **separate fresh MetaM session**. It takes the
accumulated `PreDeclHash` array, calls `ppExpr` on each canonical type, and
produces the final `DeclHash` with the pretty-printed type string.

This separation means the `whnf`-heavy Phase 1 and the `ppExpr`-heavy Phase
2 never share MetaM state.

### Flush interval

The outer loop in `computeNameBasedHashes` accumulates `PreDeclHash` results
across batches. Every **5000 declarations** (or at the end), it flushes:
runs Phase 2 on the accumulated results and clears the pending array.

This bounds the number of live canonical `Expr` objects to ~5000 at any time,
preventing the process-level memory growth that causes crash mode 2 when
`Expr` objects from normalized types accumulate.

```
batchStart := 0
while batchStart < decls.size:
    batch := decls[batchStart .. batchStart + 10]    -- micro-batch
    (preHashes, _) ← hashBatchPhase1 env batch       -- fresh MetaM
    pendingPre += preHashes
    batchStart += 10

    if pendingPre.size ≥ 5000 or batchStart ≥ decls.size:
        allResults += hashBatchPhase2 env pendingPre  -- fresh MetaM
        pendingPre := []                              -- release Exprs
```

### Content-based hashing variant

`computeContentBasedHashes` follows the same micro-batching pattern but
differs in two ways:

1. **Topological sort**: declarations are processed in dependency order
   (foundations first) so that each declaration's hash can incorporate the
   content hashes of its dependencies rather than their names (Merkle DAG).

2. **Hash table threading**: a `HashMap Name ByteArray` maps each processed
   declaration to its 32-byte hash. This table is passed into each MetaM
   batch and extended with the batch's results. At `.const name` during
   serialization, the 32-byte hash is emitted instead of the name string.

Phase 1 is inline (not via `hashBatchPhase1`) because each batch needs the
running hash table. Phase 2 is the same `hashBatchPhase2`, run once at the
end on all accumulated `PreDeclHash` results.

## Summary of parameters

| Parameter | Value | Rationale |
|-----------|-------|-----------|
| L1 micro-batch size | 10 | Largest batch that doesn't crash with native `whnf` |
| L0 batch size | all | No crash risk; pure computation |
| Flush interval | 5000 | Bounds live `Expr` objects to prevent process memory growth |
| `deepNormalize` depth limit | 256 | Prevents runaway recursion on deeply nested types |
| Value canonicalization | always L0 | `whnf` on values crashes regardless of batch size |

## Relation to `whnf-native-crash.md`

The crash analysis in `whnf-native-crash.md` documents the investigation that
led to this micro-batching design. It also describes an alternative approach
(`safeDeltaBeta`) that reimplements reducible unfolding in pure Lean, avoiding
native `whnf` entirely. That approach is weaker (no iota/zeta/projection
reduction) but cannot crash, and remains a viable fallback if future Lean
versions change `whnf` behavior.
