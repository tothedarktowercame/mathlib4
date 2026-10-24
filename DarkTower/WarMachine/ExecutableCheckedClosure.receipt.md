# Executable checked closure receipt

- Base: `8041f4f99e85db1f8ba223ad5dc679c6c0ae42c7`
- Branch: `wm-executable-checked-closure`
- Module: `DarkTower.WarMachine.ExecutableCheckedClosure`
- Module SHA-256: `c01308cff895e699af6c40ee46a156628ff8e223a3521f3e61eb1880d13a9613`

## Scope and algorithm

For fixed finite `S`, `executableClosedSet` enumerates the finite subsets of
`S`, retains exactly the structurally closed candidates, and intersects them.
It therefore examines at most `2 ^ Fintype.card S` candidates.  This is an
executable finite least-closure algorithm, but it is exhaustive candidate
enumeration rather than a repeated-saturation/worklist implementation.

The proved equivalence is:

```lean
s ∈ executableClosedSet m ↔ CheckedProblemMap.Closed m s
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

The eight module `#eval` controls printed, in order:

```text
false
false
true
true
true
true
true
true
```

They cover the missing half of an AND rule, its alternative route, an
empty-tail rule, an unseeded cycle, a seeded cycle, an empty graph, repeated
edges, and `update` adding the helper needed by the consumer.  The corresponding
`native_decide` examples compiled.

Printed axioms for `mem_executable_iff_closed`,
`executable_eq_closedSet`, `step_executableClosedSet`, and
`returnObs_executable` were:

```text
[propext, Classical.choice, Quot.sound]
```

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
