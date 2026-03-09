# `whnf` native crash analysis

## Reproducer

The crash was originally demonstrated with a `Reproducer.lean` file (not included
in this repo) that loads `Mathlib.Algebra.Group.Basic`, iterates over ~58,000
theorems, and calls a recursive `whnf`-based normalizer (`deepWhnf`) on each
type. The process crashes with SIGSEGV after ~29,000 declarations.

```bash
nix develop --command lake build reproducer
nix develop --command .lake/build/bin/reproducer
# → Progress: 0/57948 ... 25000/57948 ... Segmentation fault (core dumped)
```

The crashing declaration (varies slightly with iteration order) is typically an
auto-generated recursion equation like `Lean.Meta.Grind.Arith.Cutsat.CooperSplitProof.brecOn.eq`.

## Context

Level 1 normalization unfolds `@[reducible]` definitions to collapse notation aliases
and abbreviations, producing larger equivalence classes than Level 0 (which only
renames universe parameters and strips `.mdata`).

The original implementation used `Lean.Meta.whnf` at every subexpression under
`withTransparency .reducible`. This works on small modules (`Init.Data.Nat.Basic`,
~1000 theorems) but crashes with **SIGSEGV** on large Mathlib modules
(`Mathlib.Algebra.Group.Basic`, ~57000 theorems).

## The crash

```
$ ca fetch --theorems --level 1 -m Mathlib.Algebra.Group.Basic
  Normalizing: 10000/57613
  Segmentation fault (core dumped)
```

- Exit code 139 (SIGSEGV)
- Not catchable by `try/catch` (native signal, not a Lean exception)
- `ulimit -s unlimited` does not help

## Root cause: MetaM state accumulation

The reproducer has four modes that isolate the cause:

| Experiment | Result | Conclusion |
|---|---|---|
| `all` (forward order, one MetaM) | SIGSEGV at ~25k | Baseline crash |
| `single` (crashing decl, fresh MetaM) | No crash | Not a "bad declaration" |
| `fresh` (each decl in own MetaM) | All OK | Not inherent to any expression |
| `reverse` (all in reverse, one MetaM) | SIGSEGV at ~20k-25k | Same count, different declarations |

**The crash is NOT caused by any specific expression.** No individual declaration
crashes `whnf` when processed in isolation. The crash occurs after processing
~25,000 declarations *in a single MetaM session*, regardless of order.

The `reverse` mode crashes at roughly the same *count* of processed declarations
(~20k-25k) but at completely different declarations than forward mode. This
confirms the crash threshold is cumulative, not declaration-specific.

The most likely cause is **MetaM internal state growth** — the `whnf` cache
(`whnfCache`), discriminant trees, and other internal data structures grow
with each reduction. After ~25k declarations, the accumulated state causes
the native `whnf` implementation to exceed some resource limit (stack depth
or memory) and SIGSEGV.

## Why native `whnf` is vulnerable

`whnf` is declared as:

```lean
-- in Lean.Meta.Basic
@[extern "lean_whnf"] opaque whnf : Expr → MetaM Expr
```

It is **opaque** — implemented in C/C++ as part of the native kernel. The native
code has no heartbeat checks, so Lean's timeout mechanism does not fire during
`whnf`. When the accumulated MetaM state causes excessive recursion or memory
allocation in the native code, the result is an uncatchable SIGSEGV rather than
a Lean exception.

## The call chain problem

Every MetaM reduction function eventually calls back into native `whnf`:

### `whnfCore` (Lean-implemented, but unsafe)

```
whnfCore (def, Lean code)
  └─ reduceMatcher?
       └─ whnfMatcher
            └─ whnf  ← native C, crashes
```

`whnfCore` is the Lean-implemented core of the reduction loop. `whnf` (native)
is actually defined as a loop over `whnfCore` with caching:

```
whnf (extern "lean_whnf")
  └─ whnfImp (@[export lean_whnf])
       └─ whnfCore (def)
            └─ reduceMatcher? → whnfMatcher → whnf  ← cycle back to native
```

So `whnfCore` and `whnf` are mutually recursive through `whnfMatcher`.

### `unfoldDefinition?` (Lean-implemented, but unsafe)

```
unfoldDefinition? (def, Lean code)
  └─ [smart unfolding path]
       └─ smartUnfoldingReduce?
            └─ getStructuralRecArgPos?  (extern "lean_get_structural_rec_arg_pos")
       └─ whnfMatcher
            └─ whnf  ← native C, crashes
  └─ [non-smart path: unfoldDefault]
       └─ deltaBetaDefinition  ← safe (pure substitution)
```

Even with `smartUnfolding` set to `false`, the code path through
`unfoldProjInstWhenInstances?` (the fallback for non-constant heads in the
`f.app arg` case) can still reach native code.

### `withLocalDecl` / `mkLambdaFVars` / `mkForallFVars`

These MetaM operations for opening/closing binders may also call into native
code. They were not individually tested but were eliminated as a precaution.

## Functions confirmed safe (pure Lean)

| Function | What it does |
|---|---|
| `isReducible : Name → m Bool` | Checks `@[reducible]` attribute via `getReducibilityStatus` |
| `Environment.find? : Name → Option ConstantInfo` | Environment lookup |
| `ConstantInfo.value? : Option Expr` | Get definition body |
| `Expr.instantiateLevelParams : List Name → List Level → Expr` | Substitute universe params |
| `Expr.betaRev : Array Expr → Expr` | Beta-apply arguments (reverse order) |
| `Expr.headBeta : Expr` | Beta-reduce head |
| `Expr.getAppFn : Expr` | Get head of application |
| `Expr.getAppRevArgs : Array Expr` | Get arguments in reverse |
| `canonicalizeL0 : Expr → Expr` | Universe renaming + mdata stripping (pure) |

## Solutions

Two approaches were developed. The current codebase uses **native `whnf`
with micro-batching** (see `l1-batching.md`), which preserves full reduction
power. The `safeDeltaBeta` approach below remains a viable fallback.

### Approach A: micro-batching (current)

Process declarations in batches of 10 with a fresh `MetaM` session per batch.
This discards accumulated state between batches, preventing the crash while
keeping full `whnf` reduction (iota, zeta, projections). See `l1-batching.md`
for details.

### Approach B: `safeDeltaBeta` (fallback)

Replace `whnf` with a custom `safeDeltaBeta` that uses only the safe functions above:

```lean
private def tryUnfoldHead (e : Expr) : MetaM (Option Expr) := do
  let fn := e.getAppFn
  let .const name lvls := fn | return none
  unless (← isReducible name) do return none
  let env ← getEnv
  let some cinfo := env.find? name | return none
  let some body := cinfo.value? | return none
  let body := body.instantiateLevelParams cinfo.levelParams lvls
  return some (body.betaRev e.getAppRevArgs)

private partial def safeDeltaBeta (e : Expr) (fuel : Nat := 64) : MetaM Expr := do
  if fuel == 0 then return e
  match ← tryUnfoldHead e with
  | some e' => safeDeltaBeta e' (fuel - 1)
  | none => return e
```

`deepNormalize` then applies `safeDeltaBeta` recursively at every subexpression,
with a depth limit of 256.

## What the safe reducer does and does not do

**Does:**
- Delta-reduction: unfolds `@[reducible]` definitions to their bodies
- Beta-reduction: applies lambda abstractions to their arguments
- Recursive normalization of all subexpressions

**Does not:**
- Iota-reduction: does not evaluate `match` or recursor applications
- Zeta-reduction: does not substitute `let` bindings (preserves them)
- Projection reduction: does not reduce `.proj` (would need `whnf`)
- Instance synthesis: does not resolve typeclasses

This is weaker than full `whnf` but sufficient for the intended purpose:
collapsing `@[reducible]` notation aliases and abbreviations so that types
differing only in which alias they use hash to the same value.

## Performance

On `Mathlib.Algebra.Group.Basic` with `--theorems` (57,613 theorems):
- **L0**: ~5 minutes, no crashes
- **L1 with native `whnf`**: SIGSEGV after ~10,000 declarations
- **L1 with `safeDeltaBeta`**: ~4.5 minutes, no crashes, all 57,613 processed

## Declarations that happened to be at the crash point

These were identified during debugging but are **not inherently problematic** —
they simply happened to be ~25,000th in iteration order when the MetaM state
had grown large enough to trigger the crash:

| Declaration | Pattern |
|---|---|
| `Lean.Elab.ContextInfo.mk.sizeOf_spec` | `.sizeOf_spec` |
| `Lean.Elab.Info.ofTermInfo.inj` | `.inj` |
| `Lean.Elab.InfoTree.brecOn.eq` | `.brecOn.eq` |
| `LeftCancelMonoid.toIsLeftCancelMul` | typeclass coercion |
| `LeftCancelSemigroup.ext` | `.ext` |

A suffix-based blocklist approach (`unsafeForL1`) was attempted but could not
converge — each new filter revealed another crashing declaration, precisely
because the crash is not about specific declarations but about cumulative state.

## Open questions

1. **Is this a Lean bug?** The native `whnf` should not SIGSEGV. A heartbeat check
   or stack guard in the C implementation would make it throw a catchable exception
   instead. Worth reporting upstream.

2. **`Lean.Meta.reduce`**: This function exists and has options like
   `(explicitOnly := true)`. It may provide a safer middle ground — not tested.
