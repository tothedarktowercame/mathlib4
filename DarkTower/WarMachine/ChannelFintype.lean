import DarkTower.WarMachine.Holes

/-!
The fourteen declared channels (`Holes.Channel`) as a finite type, so that sums
over channels are `Finset.sum` over the whole type and coverage is by type.
Shared by the modules that sum over channels, so the instance is defined once.
-/

namespace DarkTower.WarMachine.Holes

theorem Channel.mem_all (c : Channel) : c ∈ Channel.all := by
  cases c <;> simp [Channel.all]

instance : Fintype Channel := Fintype.ofList Channel.all Channel.mem_all

end DarkTower.WarMachine.Holes
