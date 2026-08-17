# `CA.RefHash` — content identity per declaration

`CA.RefHash` (2026-08) is the identity scheme intended to replace the
name-based L0 hash as the *store key* in declbuild and the *registry
key* across the network of Redis instances that forms the global
registry (federated via `declbuild peer push/pull`). It exists because
the L0 type hash

1. keeps constant **names** inside the type, so `theorem t : IsSolvable G`
   hashes the same in two libraries whose `IsSolvable` differ — the
   hole a decentralized registry cannot have; and
2. hashes the **type only**, so every `inductive Foo : Type` and every
   definition of a given type collide (measured on a Mathlib store:
   270 inductives under the id of `Type`).

The L0 hash remains the right notion of a *statement* — once its
references are ids instead of names — which is exactly `stmt` below.

## The three ids

For a constant `c`, foundations first over the reference DAG:

```
ref(c)  = stmt(c)   if c is a theorem      -- proof irrelevance: no dependent
                                           -- can observe the proof
        = decl(c)   otherwise              -- a definition IS its value

stmt(c) = H( STMT ‖ #levelParams ‖ ⟦type c⟧ )
decl(c) = H( DECL ‖ kind ‖ flags ‖ stmt(c) ‖ ⟦value c⟧? ‖ structural fields )
```

`⟦e⟧` is the id of the L0-canonical expression `e` (`mdata` stripped;
universe parameters renamed **positionally** from the declaration's
`levelParams` binder list, `levelParams[i] ↦ u_i` — renaming the
binders is erased, *reordering* them is not, because use sites
instantiate levels positionally: `def q1.{u,v} : F u v` and
`def q2.{u,v} : F v u` are different declarations and get different
ids, where per-expression first-occurrence renaming made them collide),
computed **Merkle-style**: a node's id
is `H(tag ‖ scalars ‖ ids of children)`, and a `.const r` node embeds
`ref(r)`. Shallow subterms (`approxDepth ≤ 6`) are hashed flat in one
SHA-256; deeper ones from their children with a memo on structurally
equal subterms, so `decide`-style proofs whose *tree* is huge but whose
DAG is small stay linear. `.proj S i e` embeds `ref(S)`. Binder names
never enter; binder info does. `ReducibilityHints` do not enter (they
steer the elaborator, not the theory); `DefinitionSafety`, `isUnsafe`,
inductive arity/flags, constructor index/arity, recursor arity/rules/`k`
do.

Kind-by-kind, what is proof-irrelevant to dependents: only `theorem`
(`isProofIrrelevant`). `axiom` has no value, so `decl(axiom) =
H(kind ‖ stmt)` and two axioms of one statement coincide — as they should:
nothing inside the type theory can tell them apart. `opaque` is kept
value-inclusive, deliberately conservative for a build system (a
changed body changes compiled code even though no type-checker can
tell); relax later if wanted.

## Blocks

Mutual definitions and inductive families are cyclic. Each strongly
connected component of the reference graph (Tarjan, iterative) is one
**block**:

* members are put in a canonical order: primary key the member's
  encoding with intra-block references made anonymous, tie-break by
  source position (`all` index / constructor index) — the tie-break only
  matters for members that are structurally identical up to renaming;
* intra-block references are encoded as `BLOCKREF ‖ index`;
* `block = H(BLOCK ‖ n ‖ member₀ ‖ … ‖ memberₙ₋₁)` and
  `decl(mᵢ) = H(MEMBER ‖ block ‖ i)`;
* each member's `stmt` is then computed with the sibling `decl`s as
  ordinary references.

An inductive's constructors are in its block (the type lists them, they
reference the type); its recursor is a downstream node referencing the
block. Self-recursive constants (`foo._unsafe_rec`) are one-member
blocks. Universe-polymorphic blocks are covered by the per-member
level-param count and the canonical universe naming.

## Unresolved references

`computeIds decls base` resolves references to constants outside
`decls` through `base : RefTable` (name → ref). Anything in neither is
hashed **by name** and reported in `DeclIds.unresolved`; such ids are
*not* exact and never enter the shared memo — subterm memo entries
carry a dirty flag so that a cached fallback-bearing subterm still
poisons every enclosing term (and `unresolved` stays complete even
when a term is served from the cross-declaration memo). To get exact ids for a
subset (e.g. one library on top of another), compute the base first —
`computeIds` over `Init` yields 0 unresolved.

## API

```lean
CA.RefHash.computeIds : Array (Name × ConstantInfo) → RefTable → IO (Array DeclIds × RefTable)
CA.RefHash.idsOf      : Name → ConstantInfo → RefTable → IO DeclIds
CA.RefHash.refsOf     : ConstantInfo → NameSet      -- exact reference set (incl. structural)
CA.RefHash.sccs       : Array Name → (Name → Array Name) → Array (Array Name)
CA.RefHash.toB58      : ByteArray → String
```

`DeclIds = { name, stmt, decl, ref, block? : (blockId × index), unresolved }`.

## Properties (checked by `lake exe refhash-test`, over `Init` as base)

* α-renamed declarations get equal ids (names never enter);
* theorems: same statement ⇒ same `stmt`/`ref`; different proof ⇒
  different `decl`;
* definitions: same type ⇒ same `stmt`; different value ⇒ different
  `decl`/`ref`, and statements *about* them differ accordingly;
* mutual / inductive blocks share a block id with distinct indices;
* universe binder *order* is part of the identity (positional
  instantiation), binder *names* are not;
* ordinary (non-mutual, non-self-referential) declarations are
  standalone — no block id;
* `unresolved` is complete even for subterms served from the shared
  memo;
* deterministic, input-order independent; 0 unresolved on `Init`.

Throughput: ~3.5k declarations/s single-threaded on `Init`
(66k declarations, ~18 s); SCC levels are independent, so this
parallelises when needed.

## What declbuild / the Redis registry do with it (plan)

`stmt` = registry key, convergence comparand, key of statement-level
annotations. `decl` = store key (cinfo, kind, module, deps, ext,
verifications). `ref` = what `deps:` edges and cone walks use. See
declbuild's `docs/plan-content-identity.md`.
