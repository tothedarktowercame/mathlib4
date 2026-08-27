/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.WarMachine.GainChain
import DarkTower.WarMachine.CoverageReport
import DarkTower.WarMachine.CommitmentTemperature
import DarkTower.WarMachine.PolicyGrade
import Lean.Data.Json

/-!
# Executable contract emitter for the War Machine

The generated JSON names every War Machine requirement module.  The Clojure
consumer may validate this document and observations against it; it must not
maintain a separate family table.

Clause descriptions, predicate names, implementation paths and reserved-family
names are strings because `GainChain` does not represent source metadata as
data.

**No `holds` field is emitted, deliberately.**  A contract states what must be
true; whether it *was* true on a given run is a verdict, and verdicts about runs
belong to the trace checker, not to the contract document
(`p4ng/empirics-futon/NOTE-apm-lean-clojure-strategy.md`, direction 2).  An
earlier draft computed `holds` by applying each predicate to a counterexample
from `GainChain` — which is circular: `clockSplitOccurrence` is the two-clocks
witness and fails family 1 by construction, so the field would have reported a
property of the fixture rather than of the War Machine.  Current statuses live in
`M-formal-war-machine` §2.1b and in the qualification record.
-/

namespace DarkTower.WarMachine.ContractEmitter

open Lean
open DarkTower.WarMachine.GainChain

def stringArray (values : List String) : Json :=
  Json.arr (values.map Json.str).toArray

/-- A predicate name the **elaborator resolves**.  Written as a plain string, a
rename inside a module would drift silently past the contract and the build
would stay green; written as a checked constant, the build fails with an unknown
constant instead.  The emitted text is the final component, so the document's
shape is unchanged — only its authority is.

This is why the emitter imports every module it names.  Naming a module without
importing it is the same defect one level up: the contract asserts a declaration
exists and nothing checks that it does. -/
def predName (n : Name) : String := n.getString!

/-- Several families are carried by more than one predicate. -/
def predNames (ns : List Name) : String := String.intercalate " / " (ns.map predName)

def predArray (ns : List Name) : Json := stringArray (ns.map predName)

def familyJson (id : Nat) (name predicate : String) (clauses : List String)
    (clojureLocus : String) : Json :=
  Json.mkObj
    [("id", Json.num id),
     ("name", Json.str name),
     ("lean-predicate", Json.str predicate),
     ("clauses", stringArray clauses),
     ("clojure-locus", Json.str clojureLocus)]

def familiesJson : Json :=
  Json.arr #[
    familyJson 1 "identity-threading" (predName ``GainChain.threadedIdentity)
      ["the occurrence consumes an outcome",
       "selection and outcome share one tick",
       "occurrence and outcome share one tick",
       "selection and outcome share one mission",
       "selection and outcome share one producer"]
      "futon2/src/futon2/aif/fold_realized.clj; futon2/scripts/wm_scheduled_run.clj",
    familyJson 2 "non-empty-evidence-handle" (predName ``GainChain.inhabitedHandle)
      ["the fold occurrence contains a realized outcome"]
      "futon2/src/futon2/aif/fold_realized.clj",
    familyJson 4 "durability-before-fold"
      (predNames [``GainChain.durableBeforeFold, ``GainChain.loadYieldsOutcome,
                  ``GainChain.foldOf])
      ["every consumed outcome is durable",
       "corpus loading yields an outcome under its declared load policy",
       "the fold receives the outcome yielded by corpus loading"]
      "futon2/src/futon2/aif/enact.clj; futon2/src/futon2/aif/actuator_a3.clj; futon2/src/futon2/aif/fold_escrow.clj",
    familyJson 5 "provenance-containment"
      (predNames [``GainChain.declaredDomain, ``GainChain.typedAbsence,
                  ``GainChain.dischargedPrecondition, ``GainChain.domainNotNarrowed])
      ["the selected mission belongs to the producer's declared domain",
       "domain mismatch is distinct from missing data",
       "the selected producer's data precondition is discharged",
       "producer substitution does not narrow the declared domain"]
      "futon2/src/futon2/aif/fold_realized.clj; futon2/src/futon2/aif/actuator_a3.clj",
    familyJson 8 "temperature-governance"
      (predNames [``CommitmentTemperature.governs,
                  ``CommitmentTemperature.factorsThroughDiscard])
      ["a temperature-governed selector has one fixed ranking and two temperatures that select different actions",
       "a selector that factors through discarding temperature is not temperature-governed"]
      "futon2/src/futon2/aif/policy.clj"]

def chainPropertyJson : Json :=
  Json.mkObj
    [("name", Json.str (predName ``GainChain.gainChainSound)),
     ("conjuncts", predArray
       [``GainChain.threadedIdentity, ``GainChain.inhabitedHandle,
        ``GainChain.durableBeforeFold, ``GainChain.typedAbsence,
        ``GainChain.declaredDomain, ``GainChain.dischargedPrecondition,
        ``GainChain.gainAdvances])]

def compliancePropertyJson : Json :=
  Json.mkObj
    [("name", Json.str (predName ``GainChain.foldCompliant)),
     ("conjuncts", predArray
       [``GainChain.threadedIdentity, ``GainChain.inhabitedHandle,
        ``GainChain.durableBeforeFold, ``GainChain.typedAbsence,
        ``GainChain.dischargedPrecondition])]

/-- R5's executable clause.  Predicate names, clause descriptions, and the
Clojure source locus are literals because Lean declarations do not retain this
source metadata as runtime data.  The conjunct list follows the definition of
`CoverageReport.coverageReported`. -/
def coverageClauseJson : Json :=
  Json.mkObj
    [("id", Json.str "R5"),
     ("name", Json.str "coverage-reported"),
     ("lean-predicate", Json.str (predName ``CoverageReport.coverageReported)),
     ("conjuncts", predArray
       [``CoverageReport.declaresCoverage, ``CoverageReport.outsideIsTyped,
        ``GainChain.inhabitedHandle, ``GainChain.typedAbsence,
        ``GainChain.declaredDomain]),
     ("clojure-locus", Json.str "futon2/src/futon2/aif/coverage_check.clj")]

/-- Naming discipline for `G(π)`, separate from the numbered requirement
families.  The locus is an object carrying typed absence rather than a string:
a consumer cannot mistake an absent mirror for a present but blank path.

Two of `earnsPolicyGrade`'s three conjuncts are named declarations and one is an
equation with no name, and the first conjunct is a *negation* of the predicate it
names.  So `conjuncts` lists only the real declarations and `clauses` states all
three in words — listing `sustainedSingleAction` positively would misreport the
clause.  An earlier draft listed `scoreUnderObservedWiring` and
`notSustainedSingleAction`, neither of which is a declaration anywhere. -/
def policyGradeClauseJson : Json :=
  Json.mkObj
    [("id", Json.str "G-naming"),
     ("name", Json.str "policy-grade"),
     ("lean-predicate", Json.str (predName ``PolicyGrade.earnsPolicyGrade)),
     ("conjuncts", predArray
       [``PolicyGrade.sustainedSingleAction, ``PolicyGrade.wiringSensitive]),
     ("clauses", stringArray
       ["the scored family reproduces the run's recorded score at the observed wiring",
        "the trajectory is NOT a sustained single action",
        "some alternative wiring of the same components gives a different score"]),
     ("clojure-locus", Json.mkObj
       [("absent", Json.str "no-clojure-mirror-yet")])]

def reservedJson : Json :=
  Json.arr #[
    Json.mkObj [("id", Json.num 3), ("name", Json.str "self-contained-record")],
    Json.mkObj [("id", Json.num 6), ("name", Json.str "separated-powers")],
    Json.mkObj [("id", Json.num 7), ("name", Json.str "pinned-exit")],
    Json.mkObj [("id", Json.num 9), ("name", Json.str "candidate-space-membership")]]

def contractJson : Json :=
  Json.mkObj
    [("contract-version", Json.str "wm-contract-v2"),
     ("families", familiesJson),
     ("chain-property", chainPropertyJson),
     ("compliance-property", compliancePropertyJson),
     ("coverage-clause", coverageClauseJson),
     ("policy-grade-clause", policyGradeClauseJson),
     ("reserved", reservedJson)]

def emit : IO Unit := IO.println contractJson.compress

end DarkTower.WarMachine.ContractEmitter

def main : IO Unit := DarkTower.WarMachine.ContractEmitter.emit
