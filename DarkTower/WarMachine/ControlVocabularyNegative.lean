import DarkTower.WarMachine.Holes
open DarkTower.WarMachine.Holes
inductive Control where | observe | act | outside deriving DecidableEq
def U : ControlVocabulary Control := ⟨{Control.observe, Control.act}⟩
/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
def bad : ControlPolicy U := ⟨[Control.outside], by simp [U]⟩
