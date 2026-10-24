# R20 supplied liveness-row formal receipt

Date: 2026-10-24 UTC.

Scope: formal correspondence for explicitly supplied values only. This is not a
runtime decoder, retention producer, provenance proof, live pin, schedule
liveness theorem, `Carries`, or whole-run certification. The runtime row
remains absent.

- Branch: `wm-r20-liveness-row`
- Worktree: `/home/joe/worktrees/mathlib4-r20-liveness-row`
- Base: `110192b90005039a63a0a5adebeed869174d8093`
- Code commit: `8d99282f47a3c9f5dd43733761cdbcb80739134d`

## Implemented

`R20LivenessRowCorrespondence.lean` defines:

- explicit `RawRow.absent` / `RawRow.present`;
- a supplied before/after/report carrier over any decidable-equality type;
- a local encoding `before -> 0`, `after -> 0` iff equal, otherwise `1`;
- equality preservation;
- supplied honesty iff the unchanged
  `R20Certificate.LivenessConforms` for every present row;
- absence remaining `none`;
- printed-case correspondence;
- synthetic changed/true, changed/false, equal/false, and equal/true controls.

The first three controls conform. Equal/true is proved refused. No existing
predicate was edited.

## Build

Command, run through `futon3c/scripts/bg.py`:

```text
lake build DarkTower.WarMachine.R20LivenessRowCorrespondence
exit 0
Build completed successfully (3373 jobs).
```

Full log:
`/home/joe/notes/wm-next/liveness-formal/build.log`
SHA-256:
`8d44eccc6b90194a3d38c16349e3d8db715f27cdb63fad76ccf63d0143f1eb6d`.

The module's `#print axioms` output reports:

```text
encodePair_preserves_equality: [propext]
suppliedHonest_iff_conforms: [propext, Quot.sound]
suppliedCase_eq_caseOf: [propext, Classical.choice, Quot.sound]
absent_stays_absent: []
changedTrue_conforms: [propext, Quot.sound]
changedFalse_conforms: [propext, Quot.sound]
equalFalse_conforms: [propext, Quot.sound]
equalTrue_refused: [propext, Quot.sound]
```

Thus only the permitted standard axioms occur; there is no `sorryAx`.

## Deliberately false theorem

Scratch:
`/home/joe/notes/wm-next/liveness-formal/equal-true-false-theorem.lean`
SHA-256:
`ffffe086e549cdd13afd029ced36b2b33df8d8536b1e4a85dc8cecdc77de5b41`.

Command:

```text
lake env lean /home/joe/notes/wm-next/liveness-formal/equal-true-false-theorem.lean
exit 1
```

Lean rejects the claim that equal/true conforms:

```text
Type mismatch
  changedTrue_conforms
has type
  LivenessConforms (project changedTrue)
but is expected to have type
  LivenessConforms (project equalTrue)
```

Bad-case log:
`/home/joe/notes/wm-next/liveness-formal/bad-case.log`
SHA-256:
`70dffcba41aebbe4cf49036ec456fab49ecbd307ab673768cde400e8c59268d9`.

