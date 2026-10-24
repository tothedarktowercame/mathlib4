# Pattern-observation admission receipt

## Pins and scope

- Base: `e7d38a45b75f6f01afe30c1eb1f8cad383637ef9`
- Implementation: `44466e785548acc2823114f75466eefa8ebe696e`
- Branch: `wm-pattern-observation-admission`
- Outcome-binding follow-up module SHA-256:
  `4394946a44c369dcd86bd243fb5a2fc125463b8b8427c1764d37ccad422504cf`

Existing `R15TemporalHierarchy.FastOutcome` carries only a parameter key,
`witnessed`, and `succeeded`; it cannot retain the occurrence/effect/revision
binding or authority evidence. `PatternTheta.witnessedOutcomes` then filters
that existing carrier by witness and parameter key. The new module therefore
adds a small pre-admission wrapper and projects into the existing carrier; it
does not change either existing definition.

`Proof2.ObservedInterpretation` concerns publication/interpretation readings,
not pattern-fire authority, so it was not reused as a runtime-attestation
claim. Authority remains a supplied predicate plus a checker proved equivalent
to that predicate. Both receive the requested identity and the actual observed
Boolean, allowing a domain caller to bind evidence to the payload.

## Behavior

`project` emits exactly one existing `FastOutcome` only when:

1. pattern key, occurrence, effect, and revision match the request;
2. a Boolean observation is present;
3. authority evidence is present; and
4. the caller-supplied authority checker accepts that evidence for that exact
   identity and Boolean payload.

`project_eq_some_only_if` proves every emitted event recovers matching identity,
the actual supplied Boolean, its evidence, and authority for that Boolean. The
generic interface may admit both outcomes if a caller explicitly defines that
policy; the bridge itself no longer makes outcome-insensitive authority
unavoidable.

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

The deliberate occurrence-relabeling and payload-flip controls were:

```text
lake env lean /home/joe/notes/wm-next/pattern-measurement-repair/OccurrenceMismatchNegative.lean
lake env lean /home/joe/notes/wm-next/pattern-measurement-repair/OutcomeFlipNegative.lean
```

Both exit 1 for the intended semantic reasons: occurrence 0 cannot project as
occurrence 19, and evidence attesting true cannot authorize an observed false
under the synthetic binding gate. Scratch SHA-256 values:
`4f429210773fab698b6372d239bd01d041d81b68bb0aec1ed18985dc947e1742`
and `8bb5e5960ec8879aec8b3021c1dfe5a9c322829be2b2cef6723b8891084f4e88`.

The positive failure-increment and cross-occurrence pooling controls now consume
the actual results of `project`, rather than independently constructed
`FastOutcome` literals.

## Remaining gap

This module supplies no production witness and makes no runtime evidence
trustworthy. It does not repair falsifier accounting, interpret guards, verify
signatures, establish causal attribution, infer a fire from selection, choose
a prior, model missingness, certify R20, or deduplicate events across calls.
Runtime still lacks a reviewed producer of authority evidence bound to the
actual occurrence, effect, and revision.
