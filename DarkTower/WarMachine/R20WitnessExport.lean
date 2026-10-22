import DarkTower.WarMachine.R20Witness

/-!
# EDN export of the R20 witness tables

The exporter derives every row from `R20Witness`; it owns no duplicate site,
quantity, carrier, or edge table.
-/

namespace DarkTower.WarMachine.R20WitnessExport
open DarkTower.WarMachine.R20Graph
open DarkTower.WarMachine.R20Witness

def edgeName : Edge → String
  | .habitToSelectionHabit => "habitToSelectionHabit"
  | .selectionToPrecisionHabit => "selectionToPrecisionHabit"
  | .selectionToPrecisionG => "selectionToPrecisionG"
  | .inferenceToPrecisionF => "inferenceToPrecisionF"
  | .strategicFocusToClassPreference => "strategicFocusToClassPreference"
  | .selectionToClassPreference => "selectionToClassPreference"
  | .classPreferenceToSelectionG => "classPreferenceToSelectionG"
  | .interoceptionToSelectionG => "interoceptionToSelectionG"

def escapeEdn : String → String := fun input =>
  input.foldl (fun output char =>
    output ++ match char with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | other => other.toString) ""

def ednString (value : String) : String := "\"" ++ escapeEdn value ++ "\""

def ednStrings (values : List String) : String :=
  "[" ++ String.intercalate " " (values.map ednString) ++ "]"

def edgeEdn (edge : Edge) : String :=
  "{:edge :" ++ edgeName edge ++
    " :quantity " ++ ednString (quantityTag edge.quantity) ++
    " :carriers " ++ ednStrings (carrierTags edge.quantity) ++
    " :source-sites " ++ ednStrings (endpointSites edge.source) ++
    " :target-sites " ++ ednStrings (endpointSites edge.target) ++ "}"

def edgesEdn : String :=
  "{:lean/module \"DarkTower.WarMachine.R20Witness\"\n :edges [" ++
    String.intercalate "\n         " (allEdges.map edgeEdn) ++ "]}"

/-- The exported F row retains its post-observation inference source site. -/
theorem inferenceToPrecisionF_export_source :
    (endpointSites Edge.inferenceToPrecisionF.source).contains
      (site carryClj "retrospective-f") = true := by decide

#eval IO.println edgesEdn

end DarkTower.WarMachine.R20WitnessExport
