# Checked-map annotation receipt

## Pins and scope

- Lean base: `3836beefbc68cc2060ff54f88447322f64f8ad77`
- Annotation commit: `a6ddef5598a9e1283d0ad6313ef4274a55fe5356`
- Clojure source pin: futon2 `76883e815e3413644f92abe57e98bc103596e7f5`
- Additional enumerated source pin: futon3c
  `98a4ac4f53c9ef73fe833f2f7afa03649942ad76`
- `align.py` SHA-256:
  `6b17f0bf5b65f464707fc45a5fb531b3b54e6e4a7340835a2a8c37021c5110ea`
- `code_sites.clj` SHA-256:
  `3a15a082ce56dac0d4d90c9d6fe8db6bbe8b69e1544042482b22ae9c864f3ba6`

The annotation diff changes documentation comments only. Inspection of the
complete diff from the base shows no declaration or proof text changed.

## Lean build

```text
lake build DarkTower.WarMachine.CheckedProblemMap \
  DarkTower.WarMachine.ExecutableCheckedClosure \
  DarkTower.WarMachine.CheckedReturnObservation
```

Exit 0; 8542 jobs. The three annotated file SHA-256 values are respectively:

```text
75ef63f5a7901f2f1d5c61a5d91c875bc21380e673cbf04ee4597079aa349c09
4ad0d01ab3a2c29ddd2ceb71cdb28ac31e0712cefe0506bad0c54f1dd1cc11c2
2507602fc140aa4698f03db6d2099ed574bb6a5c74595282c12b316b07035774
```

## Scratch generation

`code_sites.clj` read committed source at the two source pins above. `align.py`
read the three Lean files at the full annotation commit, with all eight named
definitions required. Exit 0:

```text
sites 0/281 (0%); calls 0/599; entities 8/123 (7%);
edges 8; unresolved anchors 0; line citations 0
```

Scratch paths:

- `/home/joe/notes/wm-next/hypergraph-implementation/annotation-check/sites.json`
- `/home/joe/notes/wm-next/hypergraph-implementation/annotation-check/out/hypergraph.json`
- `/home/joe/notes/wm-next/hypergraph-implementation/annotation-check/edge-pairs.tsv`

Their first two SHA-256 values are
`60752d490f6252332254550df63ce5c1f03d3c32a02590d2a4e894cc629fd09e`
and `0d23793e601bf4313a099cff7a7f951ea80db61a342f39891e87b6a75a4466b8`.

The exact definition-anchor pairs are:

```text
CheckedProblemMap.HasReduction       -> K:has-reduction?
CheckedProblemMap.closedSet          -> K:closed-set
CheckedProblemMap.admit              -> K:admit
CheckedProblemMap.update             -> K:update
CheckedProblemMap.Open               -> K:open-obligations
ExecutableCheckedClosure.step        -> K:closure-step
ExecutableCheckedClosure.iterativeClosedSet -> K:closed-set
CheckedReturnObservation.returnObs   -> K:return-obs
```

A machine assertion confirmed exactly eight edges, seven unique K endpoints,
all basis `definition-anchor`, and all Lean endpoints of kind `def`. There are
no theorem edges and no anchors for `validate`, `closed?`, or `closureObs`.
No canonical generated artifact was replaced.

## Refusal and regression controls

- Missing required definition: exit 2, no `hypergraph.json` written.
- `(K has-reduction-typo?)` on required `HasReduction`: exit 2 because the K
  function does not resolve, no `hypergraph.json` written. The scratch typo
  commit is `c18101ae5bb513b945a044ccdbfead7f82412091`.
- Existing generator suite: 42 tests, exit 0 (`OK`), including the constructor
  regression.

This verifies only these built modules and the generator's reviewed supported
syntax. The edges state source correspondence, not proof authentication,
runtime admission, or universal parser correctness.
