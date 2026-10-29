import DarkTower.WarMachine.HistoricalMisclassificationCorrection

namespace DarkTower.WarMachine.OrdinaryAuthorRefusalCorrection

inductive TerminalClass where
  | authorResponseUnparseable | authorResponseInvalid | apparatusFailure | other
  deriving DecidableEq

def explicitNonInjury : TerminalClass → Bool
  | .authorResponseUnparseable | .authorResponseInvalid => true
  | _ => false

structure Evidence where
  recordPin : String
  observedRecordPin : String
  authorResponsePin : String
  observedAuthorResponsePin : String
  fixCommit : String
  observedFixCommit : String
  replayChecked : Bool
  replayResult : TerminalClass

def checked (e : Evidence) : Bool :=
  e.replayChecked && e.recordPin == e.observedRecordPin &&
  e.authorResponsePin == e.observedAuthorResponsePin &&
  e.fixCommit == e.observedFixCommit && explicitNonInjury e.replayResult

def append {α : Type} (history : List α) (correction : α) (e : Evidence) : List α :=
  if checked e then history ++ [correction] else history

theorem ordinaryAuthorRefusal_appends_iff_checked_nonInjury
    {α : Type} (history : List α) (correction : α) (e : Evidence) :
    append history correction e = history ++ [correction] ↔ checked e = true := by
  simp [append]

theorem ordinaryAuthorRefusal_apparatus_inert
    {α : Type} (history : List α) (correction : α) (e : Evidence)
    (h : e.replayResult = .apparatusFailure) :
    append history correction e = history := by
  simp [append, checked, h, explicitNonInjury]

theorem ordinaryAuthorRefusal_outsideSet_inert
    {α : Type} (history : List α) (correction : α) (e : Evidence)
    (h : explicitNonInjury e.replayResult = false) :
    append history correction e = history := by
  simp [append, checked, h]

theorem ordinaryAuthorRefusal_preservesHistory
    {α : Type} (history : List α) (correction : α) (e : Evidence) :
    history <+: append history correction e := by
  by_cases h : checked e = true
  · rw [append, if_pos h]
    exact List.prefix_append history [correction]
  · simp [append, h]

end DarkTower.WarMachine.OrdinaryAuthorRefusalCorrection
