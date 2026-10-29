/-! Selected mission wants are carried unchanged from their source to the
pre-author observation request. Observation authenticity remains governed by
MissionObservationAdmission.qualifiedRow; selection does not prove success. -/
namespace DarkTower.WarMachine.SelectedWantCarrier

structure Contract (Token Locator : Type) where
  wants : List Token
  locators : Token → Locator

def carry (source : Contract Token Locator) : Contract Token Locator := source

def authorAdmitted (mission : Bool) (contract : Contract Token Locator) : Prop :=
  mission = true → contract.wants ≠ []

theorem carry_preserves_wants (source : Contract Token Locator) :
    (carry source).wants = source.wants := rfl

theorem carry_preserves_locators (source : Contract Token Locator) :
    (carry source).locators = source.locators := rfl

theorem mission_empty_refused (contract : Contract Token Locator)
    (empty : contract.wants = []) : ¬ authorAdmitted true contract := by
  intro admitted
  exact admitted rfl empty

theorem nonmission_unchanged (contract : Contract Token Locator) :
    authorAdmitted false contract := by
  intro impossible
  cases impossible

end DarkTower.WarMachine.SelectedWantCarrier
