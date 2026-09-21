# Organise and Dirichlet contract repairs — 2026-09-21

Requested by claude-12 on Joe's triage, thread
`invoke-1789965267072-22903-a0f0556a`.

## Changes

`Holes.organise` now names a proposition about a candidate cascade and its
receipts. It requires selected and output patterns to belong to the recorded
repository; exact agreement with declared nodes, edges and precedence;
precedence coverage without duplicates; recorded node origins; authored
reachability and in-cascade endpoints; and validating node and wire receipts.
Node receipts identify a rule in the policy-grain temperament. The independent
node-evidence relation attests interpretation and established guards. Missing
or invalid evidence fails the contract. This is a complete-result contract;
production holes/remainders do not count as successful construction.

The informing implementation is futon2 `28a90c73`,
`futon2.aif.fold-cascade/realize`. No implementation correspondence is claimed.
Production declaration extraction, interpretation of policy rules, observation
and receipt fidelity, and coverage of calls remain obligations. Historical F12
function-type experiments remain valid but do not prove the new contract.

`dirichletAccumulationImportAbsent` is retired. Its audit finding is preserved
as a dated historical note, with no claim that absence should continue.
`dirichletAccumulationFeedsConcentrations` is the positive run-gated contract:
nonempty realised outcomes with unique receipts, nonnegative observations and
state weights, positive prior and resulting concentrations, the outer-product
accumulation equation with a nonzero contribution, and equality between the
result and the concentrations passed to the consumer. Its bridge theorems in
`MachineDirichletAccumulation` agree with the existing declared accumulation
on the machine's fixed Channel/Status coordinates. Production provenance,
consumer correspondence and coverage remain unproved. Both registry entries
remain open for these production obligations.

`OrganiseContractControls` contains a nonempty two-node accepting example and
rejects an off-repository pattern, missing node receipt, missing wire receipt,
wrong wire receipt, ignored temperament and unestablished guards.
`DirichletImportControls` accepts a nonzero receipted update and rejects no
outcomes, unrealised outcomes, duplicate receipts, ignored outcomes and an
unconnected consumer. These are Lean model controls, not production records.

The optional `wmRunsOnce` repair is deferred: its Clojure checker validates
receipt fields and that `:route` is a vector, not an explicit end-to-end
completion predicate. Its Lean carrier does not yet include the route.
No completion claim has been inferred from those shape checks. H3/H4 are
untouched as requested. Five `def ... := sorry` declarations remain in Holes.

## Validation

- Successful scoped build: `lake build DarkTower.WarMachine.Holes
  DarkTower.WarMachine.OrganiseContractControls
  DarkTower.WarMachine.DirichletImportControls
  DarkTower.WarMachine.MachineDirichletAccumulation
  DarkTower.WarMachine.F12Conformance DarkTower.WarMachine.F12D1Arms
  DarkTower.WarMachine.F12CascadeDiffArm DarkTower.WarMachine.F12DischargeArm
  DarkTower.WarMachine.Run4Preregistration`.
- `#print axioms` on all 30 new declarations, fixtures and bridge theorems:
  no `sorryAx`. Audit log: `/tmp/codex9-two-contracts-axioms.log`.
- `git diff --check` passed.
- Broader check of all 167 local modules transitively importing Holes completed
  with three failures. Two are explicitly expected-not-to-elaborate controls:
  `FoldCOrderNegative` and `FoldCFoldedNegative`. The third,
  `PreferenceDistributionPragmaticCostNegative`, fails at line 6 before its
  guarded negative test because its call uses the old C signature. Reproduced
  with Holes compiled from pre-change HEAD into an isolated `/tmp` module tree;
  no canonical build artifacts were overwritten for that check. This existing
  control needs a separate repair. Logs:
  `/tmp/codex9-contract-importers-build.log` and
  `/tmp/codex9-baseline-preference-negative.log`.
