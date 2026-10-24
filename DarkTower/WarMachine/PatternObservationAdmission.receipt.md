# Pattern-observation admission receipt

## Pins and scope

- Base: `e7d38a45b75f6f01afe30c1eb1f8cad383637ef9`
- Implementation: `44466e785548acc2823114f75466eefa8ebe696e`
- Branch: `wm-pattern-observation-admission`
- Module SHA-256:
  `d4ab5cedb5bac608afc3f299c98c12df8027f9593c088ef37f45a1d9c1d39ce9`

Existing `R15TemporalHierarchy.FastOutcome` carries only a parameter key,
`witnessed`, and `succeeded`; it cannot retain the occurrence/effect/revision
binding or authority evidence. `PatternTheta.witnessedOutcomes` then filters
that existing carrier by witness and parameter key. The new module therefore
adds a small pre-admission wrapper and projects into the existing carrier; it
does not change either existing definition.

`Proof2.ObservedInterpretation` concerns publication/interpretation readings,
not pattern-fire authority, so it was not reused as a runtime-attestation
claim. Authority remains a supplied predicate plus a checker proved equivalent
to that predicate.

## Behavior

`project` emits exactly one existing `FastOutcome` only when:

1. pattern key, occurrence, effect, and revision match the request;
2. a Boolean observation is present;
3. authority evidence is present; and
4. the caller-supplied authority checker accepts it.

Observed `false` remains `false` and reaches the existing failure-count update.
Missing and unqualified evidence do not admit. Occurrences are event identity,
not a theta key: admitted occurrence 0 and 19 events with the same pattern pool
under existing `PatternTheta.witnessedOutcomes`. Prediction probability is not
an input, so zero probability is neither rejected nor confused with absence.

The source boundary is inherited from `PatternTheta`: its docstring cites
`refs/friston2017.txt:352` and da Costa 2020 Appendix A.1 for count learning.
Those sources do not supply the domain authority predicate, which remains a
caller premise.

## Gates

```text
lake build DarkTower.WarMachine.PatternObservationAdmission
```

Exit 0; 8501 jobs. Printed main theorem axioms were subsets of:

```text
propext, Quot.sound
```

Several concrete arithmetic/pooling controls use no axioms. No `sorry` or
`sorryAx` occurs in the new module.

The deliberate occurrence-relabeling control was:

```text
lake env lean /home/joe/notes/wm-next/pattern-measurement-repair/OccurrenceMismatchNegative.lean
```

Exit 1 for the intended reason: `decide` established that occurrence 0 cannot
project as the occurrence 19 request. Scratch SHA-256:
`327857f0bc9e7ede39dfbb8781d4ee68352d1cdce2977c0550a2ae007ae9f30a`.

## Remaining gap

This module supplies no production witness and makes no runtime evidence
trustworthy. It does not repair falsifier accounting, interpret guards, verify
signatures, establish causal attribution, infer a fire from selection, choose
a prior, model missingness, certify R20, or deduplicate events across calls.
Runtime still lacks a reviewed producer of authority evidence bound to the
actual occurrence, effect, and revision.
