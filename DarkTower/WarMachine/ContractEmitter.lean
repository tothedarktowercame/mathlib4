/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.WarMachine.GainChain
import DarkTower.WarMachine.CoverageReport
import Lean.Data.Json

/-!
# Executable contract emitter for the War Machine gain chain

The generated JSON names the record-shaped requirement families stated by
`GainChain`.  The Clojure consumer may validate this document and observations
against it; it must not maintain a separate family table.

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
    familyJson 1 "identity-threading" "threadedIdentity"
      ["the occurrence consumes an outcome",
       "selection and outcome share one tick",
       "occurrence and outcome share one tick",
       "selection and outcome share one mission",
       "selection and outcome share one producer"]
      "futon2/src/futon2/aif/fold_realized.clj; futon2/scripts/wm_scheduled_run.clj",
    familyJson 2 "non-empty-evidence-handle" "inhabitedHandle"
      ["the fold occurrence contains a realized outcome"]
      "futon2/src/futon2/aif/fold_realized.clj",
    familyJson 4 "durability-before-fold" "durableBeforeFold / loadYieldsOutcome / foldOf"
      ["every consumed outcome is durable",
       "corpus loading yields an outcome under its declared load policy",
       "the fold receives the outcome yielded by corpus loading"]
      "futon2/src/futon2/aif/enact.clj; futon2/src/futon2/aif/actuator_a3.clj; futon2/src/futon2/aif/fold_escrow.clj",
    familyJson 5 "provenance-containment"
      "declaredDomain / typedAbsence / dischargedPrecondition / domainNotNarrowed"
      ["the selected mission belongs to the producer's declared domain",
       "domain mismatch is distinct from missing data",
       "the selected producer's data precondition is discharged",
       "producer substitution does not narrow the declared domain"]
      "futon2/src/futon2/aif/fold_realized.clj; futon2/src/futon2/aif/actuator_a3.clj"]

def chainPropertyJson : Json :=
  Json.mkObj
    [("name", Json.str "gainChainSound"),
     ("conjuncts", stringArray
       ["threadedIdentity", "inhabitedHandle", "durableBeforeFold",
        "typedAbsence", "declaredDomain", "dischargedPrecondition",
        "gainAdvances"])]

def compliancePropertyJson : Json :=
  Json.mkObj
    [("name", Json.str "foldCompliant"),
     ("conjuncts", stringArray
       ["threadedIdentity", "inhabitedHandle", "durableBeforeFold",
        "typedAbsence", "dischargedPrecondition"])]

/-- R5's executable clause.  Predicate names, clause descriptions, and the
Clojure source locus are literals because Lean declarations do not retain this
source metadata as runtime data.  The conjunct list follows the definition of
`CoverageReport.coverageReported`. -/
def coverageClauseJson : Json :=
  Json.mkObj
    [("id", Json.str "R5"),
     ("name", Json.str "coverage-reported"),
     ("lean-predicate", Json.str "coverageReported"),
     ("conjuncts", stringArray
       ["declaresCoverage", "outsideIsTyped", "inhabitedHandle",
        "typedAbsence", "declaredDomain"]),
     ("clojure-locus", Json.str "futon2/src/futon2/aif/coverage_check.clj")]

def reservedJson : Json :=
  Json.arr #[
    Json.mkObj [("id", Json.num 3), ("name", Json.str "self-contained-record")],
    Json.mkObj [("id", Json.num 6), ("name", Json.str "separated-powers")],
    Json.mkObj [("id", Json.num 7), ("name", Json.str "pinned-exit")]]

def contractJson : Json :=
  Json.mkObj
    [("contract-version", Json.str "wm-contract-v1"),
     ("families", familiesJson),
     ("chain-property", chainPropertyJson),
     ("compliance-property", compliancePropertyJson),
     ("coverage-clause", coverageClauseJson),
     ("reserved", reservedJson)]

def emit : IO Unit := IO.println contractJson.compress

end DarkTower.WarMachine.ContractEmitter

def main : IO Unit := DarkTower.WarMachine.ContractEmitter.emit
