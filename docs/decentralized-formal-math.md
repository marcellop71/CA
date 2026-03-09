# Decentralized Formal Mathematics

## Motivation

Content-addressing assigns a stable identity to every mathematical proposition
based on its type's structure, not its name or where it was stated. Two
researchers working independently can state the same proposition under
different names — the content addresses match, and the system knows they mean
the same thing.

Combined with Lean's type checker (which mechanically verifies proofs), this
gives us the primitives for **decentralized, trustless collaboration on formal
mathematics**:

- **No trust required** — Lean's kernel is the authority, not a person.
- **Name-independent** — content hashes identify mathematical claims.
- **Permissionless** — anyone can publish a proof; if it type-checks, it's valid.
- **Composable** — small contributions (proving one link) compose into big results.

## Core abstraction

A **declaration** is the unit of publication. Each has:

- A **content address** (type hash) — its identity.
- A **status**: proved, open, or conditional (proved assuming open hypotheses).
- A **dependency set** — which other declarations it references.

The service is a **registry of mathematical declarations** — like a package
registry, but for individual propositions and theorems.

## Three roles

### 1. Publisher (announcing theorems and open points)

A researcher has a Lean project (repo or file) with theorems and open points.

```bash
# Publish from a Lean project
ca publish --repo /path/to/project

# Publish from a single file
ca publish --file MyTheorems.lean -m Init.Data.Nat.Basic
```

The tool loads the environment, scans declarations, and classifies each one
**automatically** — no manual annotation required:

| Pattern in Lean | Classification |
|---|---|
| `theorem foo : P := proof` | **proved** — type-checks, no `sorry` |
| `def P : Prop := ...` (no theorem inhabiting it) | **open** — stated, no proof exists |
| `theorem bar (h : OpenP) : Q := ...` | **conditional** — proved modulo open hypotheses |

Each declaration is published to the registry with:

- Content address (type hash, level 0 or 1).
- Human-readable name and pretty-printed type.
- Source (repo URL, file, module).
- Status (proved / open / conditional).
- Dependency edges (what it uses, what uses it).

#### Minimal open point announcement

A single `.lean` file with just a statement is enough:

```lean
import Mathlib.Data.Nat.Basic

def MyConjecture : Prop :=
  ∀ n : Nat, ∃ p, Nat.Prime p ∧ n < p ∧ p < 2 * n
```

```bash
ca publish --file MyConjecture.lean -m Mathlib.Data.Nat.Basic
```

The service detects it as open (a `Prop` with no proof), content-addresses it,
and publishes. If someone else independently states the same proposition
(perhaps with a different name), the content addresses match — the system knows
they are the same open problem.

### 2. Contributor (looking for work, submitting proofs)

Someone wants to contribute. They query the registry:

```bash
# What's open?
ca work

# Highest impact open points (closing it unlocks the most conditional theorems)
ca work --sort impact

# Open points involving specific concepts
ca work --type "ZMod" --type "Finset"

# What does proving this open point unlock?
ca work --chain <address>
```

**Impact** is computable from the dependency graph: an open point that appears
as a hypothesis in many conditional theorems has high impact. For example, in
the Euclid–Mullin formalization, `DeterministicStabilityLemma` ranks highest
because it is the single hypothesis for the full chain
`DSL → CME → CCSB → MullinConjecture`.

#### Submitting a proof

```bash
ca submit --file MyProof.lean -m Init.Data.Nat.Basic
```

The service:

1. Loads the environment + the submitted file.
2. Finds new theorems whose types match open content addresses.
3. Type-checks them (Lean does this at load time — if it loads, it's valid).
4. Updates the registry: open → proved. Recalculates which conditional
   theorems are now unconditional.

### 3. Consumer (using results)

A Lean developer building on the ecosystem.

**From the CLI** (lookup):

```bash
ca resolve <address>
# → name, module, status, type, who proved it, dependencies
```

**From Lean** (the `use` command):

```lean
import CA

-- Resolve by name (via registry)
use Nat.add_comm

-- Resolve and dynamically import the source module
use! Nat.add_comm
```

**From a coding assistant**: an AI assistant working in Lean can query the
registry to find open points matching the user's current work, check if a
subgoal's type hash matches a known proved theorem, or auto-publish when the
user proves something.

## Attributes: `@[open_point]` and `@[publish]`

The `CA.Registry` module (part of the `CA` package) provides two attributes
that let authors explicitly annotate their code:

### `@[open_point]`

Marks a `def X : Prop` as an open problem.

```lean
import CA

@[open_point "Deterministic stability for the walk"]
def DeterministicStabilityLemma : Prop :=
  ∀ q : Nat, Nat.Prime q → ...
```

Validation: the target must be a `def` with type `Prop`. Applying it to a
theorem, inductive, or non-Prop definition is a compile-time error.

### `@[publish]`

Marks any declaration (theorem, def, axiom) for publication to the registry.

```lean
@[publish "Full reduction chain: DSL → MC"]
theorem full_chain_dsl (hdsl : DeterministicStabilityLemma) :
    MullinConjecture := ...
```

No restrictions on declaration kind — the service classifies status (proved /
open / conditional) automatically from the environment.

### Retroactive application

Both attributes support retroactive application from a separate file, following
the same pattern as Blueprint attributes in EM:

```lean
import CA
import EM.MasterReduction

attribute [open_point "Deterministic stability"] DeterministicStabilityLemma
attribute [publish "DSL → CME → CCSB → MC"] full_chain_dsl
```

This is useful when authors want to annotate existing code without modifying the
original source files.

### How `ca publish` uses attributes

When `ca publish` scans an environment, it checks the
`openPointExt` and `publishExt` environment extensions to find annotated
declarations. This replaces heuristic-based detection with **explicit author
intent**:

- **Solves the "Nat.Prime problem"**: without attributes, the tool must guess
  whether a `def X : Prop` is an intentional open problem or just a helper
  definition. With `@[open_point]`, the author's intent is unambiguous.
- **Selective publication**: `@[publish]` lets authors control which declarations
  enter the registry. Internal helper lemmas stay private unless explicitly
  marked.
- **Backward compatible**: the heuristic mode still works for projects that
  don't use attributes. Attributes simply override heuristics when present.

### Setup

Add to your `lakefile.lean`:

```lean
require ca from git
  "https://github.com/marcellop71/CA" @ "main"
```

## Declaration status lifecycle

```
                 publish
    .lean file ─────────→ [open]
                             │
                    submit   │  someone proves it
                             ▼
                          [proved]
                             │
                             │  conditional theorems that
                             │  depended on it get re-evaluated
                             ▼
              [conditional] ──→ [proved]  (if all hypotheses now proved)
```

## Identity: names vs. addresses

Both. Names are for humans, addresses are for the protocol. The registry maps
both ways. Two people proving the same thing under different names produce the
same address — the system merges them.

Content addresses also handle **equivalence classes**: declarations with the
same type hash state the same mathematical fact. The `--level 1` normalization
(reducible unfolding) collapses notation aliases and abbreviations, producing
larger equivalence classes.

## The registry

The global registry is **federated**: each participating Lean project hosts a
`registry/` folder in its git repo. The global registry is the union of all
project-local registries. Publication is `git push`, verification is
`lake build`, and discovery is a curated `sources.json` listing known repos.
See `registry-design.md` for the full architecture.

For batch indexing and single-declaration lookup, the `ca` CLI also supports
Redis as a fast local cache (the `fetch` and `address` commands).

## Dependency model

A theorem in Lean has three kinds of dependencies:

### Type dependencies

Constants referenced in the statement (`collectConstants ci.type`). These tell
you what the theorem is *about*. Content-based hashing already captures these:
each `.const name` in the type is replaced by the content hash of the
referenced declaration.

### Proof dependencies

Constants referenced in the proof term (`collectConstants ci.value`). These
tell you what the proof *uses*: which lemmas, which definitions were unfolded.
Useful for citation graphs and provenance, but not for identity.

### Hypothesis dependencies

The critical kind for the service. A theorem's type may include arrows from
named `Prop` definitions:

```lean
def DeterministicStabilityLemma : Prop := ...

theorem full_chain_dsl
    (h_equidist : ∀ q, Nat.Prime q → MinFacResidueEquidist q)
    (hdsl : DeterministicStabilityLemma) :
    MullinConjecture := ...
```

The type is `(∀ q, ...) → DeterministicStabilityLemma → MullinConjecture`.
Some hypothesis arrows are **preconditions** (quantified over bound variables,
like `Prime p` — part of the universal statement), and others are **global
assumptions** (references to named, closed `Prop` definitions that may or may
not have been proved).

A hypothesis is a global assumption (not a precondition) when:

1. Its type resolves to a top-level `def X : Prop` (a named, closed proposition).
2. No theorem in the environment has type `X`.

This is detectable automatically from the environment.

### Address is status-blind; registry tracks status

The content address of a theorem captures *what it says*, not whether its
hypotheses have been proved. The address of `full_chain_dsl` is determined by
the content of `DeterministicStabilityLemma` and `MullinConjecture` as
mathematical statements — it does not change when someone proves DSL.

This is the right design because:

- The mathematical content hasn't changed — the same implication holds.
- Address stability means references never break.
- What changed is the *context*, not the *content*.

The **registry** tracks status as a mutable overlay on the immutable address
graph:

| Layer | What it stores | Mutability |
|---|---|---|
| **Address** | Content hash of the type | Immutable |
| **Dependency graph** | Which addresses appear as hypotheses of which | Immutable (follows from types) |
| **Status** | proved / open / conditional | Mutable (updated on submit) |

When someone proves an open point:

1. The registry marks its address as proved.
2. It walks the dependency graph to find all conditional theorems that had it
   as a hypothesis.
3. For each, it checks: are *all* hypotheses now proved? If so, promote
   conditional → proved.
4. This cascades: a newly proved theorem may itself be a hypothesis of
   downstream conditional theorems.

### Impact metric

The dependency graph makes **impact** computable: the impact of an open point
is the number of conditional theorems (transitively) downstream of it. Proving
a high-impact open point cascades to close the most chains.

In the Euclid–Mullin formalization, the graph looks like:

```
DeterministicStabilityLemma  ←── sole open hypothesis
        │
        ▼
   full_chain_dsl : DSL → MC  (conditional)
        │
        ▼ (cascade on proof of DSL)
   MullinConjecture  ←── promoted to proved
```

`DeterministicStabilityLemma` has maximum impact: proving it alone would close
the entire chain to `MullinConjecture`.

## Versioning

Content addresses solve versioning. If Mathlib changes and a type's normal form
changes, the address changes — the system treats it as a different proposition.
Level 1 normalization helps: reducible aliases collapse, so superficial Mathlib
refactors don't break addresses.

## Subcommands (planned)

| Command | Role | Description |
|---|---|---|
| `publish` | Publisher | Scan a project/file, classify declarations, publish to registry |
| `work` | Contributor | Query open points, sort by impact, show dependency chains |
| `submit` | Contributor | Submit a proof, type-check it, update registry |
| `resolve` | Consumer | Look up a declaration by name or address |

These are additions to the existing `ca` CLI, which already handles
environment loading, content-addressing, and Redis storage.
