# Executable checked closure receipt

- Base: `8041f4f99e85db1f8ba223ad5dc679c6c0ae42c7`
- Branch: `wm-executable-checked-closure`
- Module: `DarkTower.WarMachine.ExecutableCheckedClosure`
- Follow-up module SHA-256: `d54b57f0693b98fe3723e10451d96a4f7813d5f16188a1b457d7de4552a732dc`

## Scope and algorithm

For fixed finite `S`, `iterativeClosedSet` applies `step` exactly
`Fintype.card S` times from `∅`. Each non-fixed iteration strictly increases
cardinality, so this exact bound reaches the least closure. The general proofs
establish inflationarity, monotonicity, containment in `Closed`, fixed-point
stability, and membership equivalence with `CheckedProblemMap.Closed`.

The retained reference oracle `executableClosedSet` enumerates the finite subsets of
`S`, retains exactly the structurally closed candidates, and intersects them.
It therefore examines at most `2 ^ Fintype.card S` candidates.  This is an
independent executable finite oracle for the iterative implementation.

The principal proved equivalences are:

```lean
s ∈ executableClosedSet m ↔ CheckedProblemMap.Closed m s
s ∈ iterativeClosedSet m ↔ CheckedProblemMap.Closed m s
```

It consequently proves equality with the existing noncomputable `closedSet`,
the fixed-point law for the one-step operator, and agreement with existing
`closureObs` and `returnObs`.  No interpretation `I` is evaluated; artifact
proofs are merely the already-supplied initial seeds.

## Commands and results

From `/home/joe/worktrees/mathlib4-executable-checked-closure`:

```text
lake build DarkTower.WarMachine.ExecutableCheckedClosure
```

Exit 0; 8542 jobs completed.  Existing imported modules emitted their known
declaration-uses-`sorry` warnings; this new module contains no `sorry`.

The eleven module `#eval` controls printed, in order:

```text
false
false
true
true
true
true
true
true
false
true
true
```

They cover the missing half of an AND rule, its alternative route, an
empty-tail rule, an unseeded cycle, a seeded cycle, an empty graph, repeated
edges, `update` adding the helper needed by the consumer, a chain requiring
three rounds, and equality of iterative output with the oracle. The
corresponding `native_decide` checks compiled.

Printed axioms for the general proofs, including `step_mono`,
`iterative_eq_executable`, `mem_iterative_iff_closed`,
`step_iterativeClosedSet`, and `returnObs_iterative`, were:

```text
[propext, Classical.choice, Quot.sound]
```

The two `native_decide` fixture theorems additionally report their generated
`native_decide.ax_1_1` evaluator axioms. They are computational checks and are
not conflated with the general proof boundary above.

The follow-up insufficient-iteration negative control was:

```text
lake env lean /home/joe/notes/wm-next/loop-plan/executable-checked-closure/InsufficientIteration.lean
```

Exit 1: `consumer ∈ (step chainMap)^[2] ∅` evaluated false; the same fixture
evaluates true after three rounds. SHA-256:
`1deff8163c7e101020bc9ef462754883abfa208ff6511b34f5ef22212d5a32ad`.

The deliberate negative control was:

```text
lake env lean /home/joe/notes/wm-next/loop-plan/executable-checked-closure/FalseClosure.lean
```

Exit 1, for the intended semantic reason:

```text
native_decide evaluated proposition
  consumer ∈ executableClosedSet (update m0 foundationOnly)
to be false
```

Negative-control SHA-256:
`2bad3c8bbc9a289ad4cfd485aab0d7f69b3074c5e43a4ad00376f52d3c2140ee`.

## Boundary

This refines the existing `CheckedProblemMap.Closed` relation and observation
functions.  It does not authenticate supplied artifacts, execute their
interpretations, define a score or learning rule, or claim runtime compliance.
