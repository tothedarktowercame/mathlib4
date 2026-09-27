import DarkTower.WarMachine.Proof2.ContainmentOrder
import DarkTower.WarMachine.Proof2.ObservedInterpretation

/-!
# Containment at the machine's received interpretation supply (W9-2)

The relation is C1's construction at ob.pat, not an independently supplied
order. No supply for a candidate's unit applications means no order on its
receipt. This is absence of the order, not a claim that order-use refuses
the whole scoring run: the code can record its list-kernel fallback.
-/

namespace DarkTower.WarMachine.Proof2.ContainmentOrderAtMachine

open DarkTower.WarMachine.CascadeTransition
open DarkTower.WarMachine.Proof2.ContainmentOrder
open DarkTower.WarMachine.Proof2.ObservedInterpretation

variable {ι V W : Type*} [Fintype V] [DecidableEq V]

def machineContainmentOrder (ob : ObservedInterpretation ι V) (a b : ι) : Prop :=
  containmentOrder ob.pat a b

theorem machineContainmentOrder_eq (ob : ObservedInterpretation ι V) (a b : ι) :
    machineContainmentOrder ob a b ↔ containmentOrder ob.pat a b := Iff.rfl

/-- The missing-order receipt retains the publication failure that caused it. -/
inductive OrderAbsence (W : Type*) where
  | noOrderOnReceipt (cause : InterpretationAbsence W)

def orderAtSupply
    (supply : Except (InterpretationAbsence W) (ObservedInterpretation ι V)) :
    Except (OrderAbsence W) (ι → ι → Prop) :=
  match observedInterpretation supply with
  | .ok ob => .ok (machineContainmentOrder ob)
  | .error reason => .error (.noOrderOnReceipt reason)

theorem orderAtSupply_published (ob : ObservedInterpretation ι V) :
    orderAtSupply (W := W) (.ok ob) = .ok (machineContainmentOrder ob) := rfl

theorem orderAtSupply_absent (reason : InterpretationAbsence W) :
    orderAtSupply (ι := ι) (V := V) (.error reason) =
      .error (.noOrderOnReceipt reason) := rfl

theorem absent_supply_has_no_order (reason : InterpretationAbsence W) (r : ι → ι → Prop) :
    orderAtSupply (V := V) (.error reason) ≠ .ok r := by
  simp [orderAtSupply, observedInterpretation]

/-- Same unit and token carriers, different published pattern supplies. -/
def cyclicSupply : ObservedInterpretation Bool (Fin 2) :=
  ⟨cyclePat, "fixture: published two-pattern reading"⟩

def constantSupply : ObservedInterpretation Bool (Fin 2) :=
  ⟨fun _ => upPattern, "fixture: published repeated up-pattern reading"⟩

/-- A supplied token dependency produces the edge. -/
theorem cyclicSupply_edge : machineContainmentOrder cyclicSupply true false :=
  cycle_edge_up

/-- The other supply has no such dependency on the very same indices. -/
theorem constantSupply_no_edge : ¬ machineContainmentOrder constantSupply true false := by
  simp [machineContainmentOrder, constantSupply, containmentOrder, upPattern]

/-- The bad case pins that the observed supply actually changes the order. -/
theorem different_supplies_different_orders :
    machineContainmentOrder cyclicSupply ≠ machineContainmentOrder constantSupply := by
  intro h
  have edge := cyclicSupply_edge
  rw [h] at edge
  exact constantSupply_no_edge edge

#print axioms machineContainmentOrder
#print axioms machineContainmentOrder_eq
#print axioms OrderAbsence
#print axioms orderAtSupply
#print axioms orderAtSupply_published
#print axioms orderAtSupply_absent
#print axioms absent_supply_has_no_order
#print axioms cyclicSupply
#print axioms constantSupply
#print axioms cyclicSupply_edge
#print axioms constantSupply_no_edge
#print axioms different_supplies_different_orders

end DarkTower.WarMachine.Proof2.ContainmentOrderAtMachine
