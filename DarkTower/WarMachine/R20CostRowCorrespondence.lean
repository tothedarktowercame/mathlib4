import DarkTower.WarMachine.R20Certificate

/-!
# Retained cost-row correspondence

This module records the exact scoped correspondence between the retained
runtime cost projection and `R20Certificate.CostRow`.  The raw carrier is
already on the explicitly admitted nonnegative domain (`Nat`); it retains the
aggregate input and output reports that `CostRow` intentionally omits.

Projection never repairs arithmetic.  A present inconsistent raw row remains
present and can disagree.  Absence is represented separately by `Option`.
`throughSelection` is the result of the existing runtime phase classifier, not
a new chronology or phase taxonomy; the companion Clojure test checks that
classifier on the verbatim phases.

Runtime source: futon2 `apparatus-certificates/cost-row` and
`registered-run-telemetry/model-usage`, revision
`38c3f2b79a5d22a3737ebc6d7a7aa81c6d7961a2`.  Live instance: run
`2026-10-23-90ca5944-3d52-4bd6-940c-fe2f6c2c8c6b`, source SHA-256
`976d1bfc7983b3cc234dbc5a25ae848e0c73b018fa2076940b31bbfc5dcdc5b9`.
-/

namespace DarkTower.WarMachine.R20CostRowCorrespondence

open DarkTower.WarMachine.R20Certificate

/-- Present, nonnegative runtime inputs. Aggregate input/output are retained
because the runtime checker validates them although `CostRow` omits them. -/
structure RawCost where
  jobs : List JobCost
  msThroughSelection : Nat
  msAfterSelection : Nat
  reportedInputTokens : Nat
  reportedOutputTokens : Nat
  reportedTotalTokens : Nat
  reportedTokensThroughSelection : Nat
  reportedTokensAfterSelection : Nat

def sumInput (jobs : List JobCost) : Nat := (jobs.map (·.inputTokens)).sum
def sumOutput (jobs : List JobCost) : Nat := (jobs.map (·.outputTokens)).sum

/-- Drop only the aggregate input/output reports; do not repair any value. -/
def project (raw : RawCost) : CostRow :=
  { jobs := raw.jobs
    msThroughSelection := raw.msThroughSelection
    msAfterSelection := raw.msAfterSelection
    reportedTotalTokens := raw.reportedTotalTokens
    reportedTokensThroughSelection := raw.reportedTokensThroughSelection
    reportedTokensAfterSelection := raw.reportedTokensAfterSelection }

/-- Presence admission is independent of arithmetic validity. -/
def adapt : Option RawCost → Option CostRow
  | none => none
  | some raw => some (project raw)

/-- The checks performed by the runtime extractor on a present nonnegative row. -/
def RuntimeAgrees (raw : RawCost) : Prop :=
  (∀ j ∈ raw.jobs, j.totalTokens = j.inputTokens + j.outputTokens) ∧
  raw.reportedInputTokens = sumInput raw.jobs ∧
  raw.reportedOutputTokens = sumOutput raw.jobs ∧
  raw.reportedTotalTokens = totalTokens raw.jobs ∧
  raw.reportedTokensThroughSelection = tokensWhere true raw.jobs ∧
  raw.reportedTokensAfterSelection = tokensWhere false raw.jobs

/-- Exact scoped correspondence: Lean conformance plus the two aggregate checks
whose fields are not retained by `CostRow`. -/
theorem runtimeAgrees_iff (raw : RawCost) :
    RuntimeAgrees raw ↔
      CostConforms (project raw) ∧
      raw.reportedInputTokens = sumInput raw.jobs ∧
      raw.reportedOutputTokens = sumOutput raw.jobs := by
  simp only [RuntimeAgrees, CostConforms, project, sumInput, sumOutput]
  aesop

theorem runtimeAgrees_implies_conforms {raw : RawCost} (h : RuntimeAgrees raw) :
    CostConforms (project raw) :=
  (runtimeAgrees_iff raw).mp h |>.1

/-- The runtime and Lean case trees use the same strict comparisons and order,
including token ties, time tie-breaks, and the all-equal case. -/
def runtimeCase (raw : RawCost) : CostCase :=
  if raw.reportedTokensAfterSelection < raw.reportedTokensThroughSelection then .mostlyChoosing
  else if raw.reportedTokensThroughSelection < raw.reportedTokensAfterSelection then .mostlyActing
  else if raw.msAfterSelection < raw.msThroughSelection then .mostlyChoosing
  else if raw.msThroughSelection < raw.msAfterSelection then .mostlyActing
  else .even

theorem runtimeCase_eq_costCase (raw : RawCost) :
    runtimeCase raw = costCase (project raw) := rfl

def run90caJobs : List JobCost :=
  [{ throughSelection := false, inputTokens := 250597, outputTokens := 5727,
     totalTokens := 256324 },
   { throughSelection := false, inputTokens := 47928, outputTokens := 653,
     totalTokens := 48581 },
   { throughSelection := false, inputTokens := 1470752, outputTokens := 12554,
     totalTokens := 1483306 },
   { throughSelection := false, inputTokens := 355117, outputTokens := 2154,
     totalTokens := 357271 }]

def run90ca : RawCost :=
  { jobs := run90caJobs
    msThroughSelection := 247928
    msAfterSelection := 700366
    reportedInputTokens := 2124394
    reportedOutputTokens := 21088
    reportedTotalTokens := 2145482
    reportedTokensThroughSelection := 0
    reportedTokensAfterSelection := 2145482 }

theorem run90ca_agrees : RuntimeAgrees run90ca := by
  norm_num [RuntimeAgrees, run90ca, run90caJobs, sumInput, sumOutput, totalTokens, tokensWhere]
theorem run90ca_conforms : CostConforms (project run90ca) :=
  runtimeAgrees_implies_conforms run90ca_agrees
theorem run90ca_mostlyActing : costCase (project run90ca) = .mostlyActing := by
  norm_num [costCase, project, run90ca]

/-- Changing only omitted aggregate input leaves the projected Lean row exactly
unchanged and conforming, while the runtime predicate disagrees. -/
def wrongAggregateInput : RawCost := { run90ca with reportedInputTokens := 2124395 }

theorem wrongAggregateInput_projection_unchanged :
    project wrongAggregateInput = project run90ca := rfl
theorem wrongAggregateInput_still_conforms : CostConforms (project wrongAggregateInput) := by
  rw [wrongAggregateInput_projection_unchanged]
  exact run90ca_conforms
theorem wrongAggregateInput_runtime_disagrees : ¬ RuntimeAgrees wrongAggregateInput := by
  norm_num [RuntimeAgrees, wrongAggregateInput, run90ca, run90caJobs, sumInput]

def wrongJobTotal : RawCost :=
  { run90ca with jobs :=
      [{ throughSelection := false, inputTokens := 250597, outputTokens := 5727,
         totalTokens := 256325 }] ++ run90caJobs.drop 1 }

theorem wrongJobTotal_disagrees : ¬ RuntimeAgrees wrongJobTotal := by
  norm_num [RuntimeAgrees, wrongJobTotal, run90ca, run90caJobs]
theorem wrongJobTotal_not_conforms : ¬ CostConforms (project wrongJobTotal) := by
  norm_num [CostConforms, project, wrongJobTotal, run90ca, run90caJobs]

theorem missing_usage_is_absent : adapt none = none := rfl

/-- Move the first live job across the already-classified boundary and retain
the correspondingly derived side totals. -/
def phaseMoved : RawCost :=
  { run90ca with
    jobs := [{ throughSelection := true, inputTokens := 250597, outputTokens := 5727,
               totalTokens := 256324 }] ++ run90caJobs.drop 1
    reportedTokensThroughSelection := 256324
    reportedTokensAfterSelection := 1889158 }

theorem phaseMoved_agrees : RuntimeAgrees phaseMoved := by
  norm_num [RuntimeAgrees, phaseMoved, run90ca, run90caJobs, sumInput, sumOutput,
    totalTokens, tokensWhere]
theorem phaseMoved_split :
    (project phaseMoved).reportedTokensThroughSelection = 256324 ∧
    (project phaseMoved).reportedTokensAfterSelection = 1889158 := by decide

/-- Explicit controls for every tied-token branch of the common case tree. -/
theorem tokenTie_timeChoosing (raw : RawCost)
    (ht : raw.reportedTokensThroughSelection = raw.reportedTokensAfterSelection)
    (hm : raw.msAfterSelection < raw.msThroughSelection) :
    runtimeCase raw = .mostlyChoosing := by simp [runtimeCase, ht, hm]

theorem tokenTie_timeActing (raw : RawCost)
    (ht : raw.reportedTokensThroughSelection = raw.reportedTokensAfterSelection)
    (hm : raw.msThroughSelection < raw.msAfterSelection) :
    runtimeCase raw = .mostlyActing := by simp [runtimeCase, ht, hm, Nat.not_lt_of_ge (Nat.le_of_lt hm)]

theorem allTied_even (raw : RawCost)
    (ht : raw.reportedTokensThroughSelection = raw.reportedTokensAfterSelection)
    (hm : raw.msThroughSelection = raw.msAfterSelection) :
    runtimeCase raw = .even := by simp [runtimeCase, ht, hm]

#print axioms runtimeAgrees_iff
#print axioms runtimeAgrees_implies_conforms
#print axioms runtimeCase_eq_costCase
#print axioms run90ca_agrees
#print axioms run90ca_conforms
#print axioms run90ca_mostlyActing
#print axioms wrongAggregateInput_runtime_disagrees
#print axioms wrongJobTotal_not_conforms
#print axioms phaseMoved_agrees
#print axioms tokenTie_timeChoosing
#print axioms tokenTie_timeActing
#print axioms allTied_even

end DarkTower.WarMachine.R20CostRowCorrespondence
