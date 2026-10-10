import Holant.OneHot.StackProgram.GraphCodeMachine.Macros

/-! Exact postorder execution, reconstructed against the preserved byte grammar.
The recursion in these proofs follows the explicit pending-action machine. -/
namespace Holant.OneHot.StackProgram.GraphCodeMachine
open Turing Computability Holant.Complexity StackProtocol
variable {A : Type} [Fintype A] (e : Encoding A Bool) (C : ℕ) (entry : Action A)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

mutual
def treeTicks : Tree A → ℕ
  | .node a b ts => emitTicks e (nodeCode a b) + (forestTicks ts + 2 * (e.encode a).length + 2 * (e.encode b).length + 15)
def forestTicks : Forest A → ℕ
  | .nil => 10
  | .cons p t ts => emitTicks e (consCode p) + (forestTicks ts + (treeTicks t + 2 * (e.encode p).length + 13))
end

def closedTicks (a : A) (ts : Forest A) : ℕ :=
  emitTicks e (rootCode a) + (forestTicks e ts + 2 * (e.encode a).length + 12)

variable (hlabels : ∀ a, (e.encode a).length ≤ C)
include hlabels
mutual
theorem tree_exact (t : Tree A) (suffix : List Bool) (pending : List (Action A)) (output : List Bool) :
    RunsExactly (machine e C entry).computer.step
      (active e (TreeEncoding.treeEncode e t ++ suffix) (.tree :: pending) output)
      (active e suffix pending ((records (opEncoding e) (compileTree t)).reverse ++ output)) (treeTicks e t) := by
  cases t with
  | node a b ts =>
    have first := prepare_tree e C entry hlabels a b (TreeEncoding.forestEncode e ts ++ suffix) pending output
    have middle := forest_exact ts suffix ((nodeCode a b).map Action.emit ++ pending) output
    have last := emit_all e C entry hlabels (nodeCode a b) suffix pending
      ((records (opEncoding e) (compileForest ts)).reverse ++ output)
    have all := (first.trans (by simpa only [nodeTasks, List.cons_append] using middle)).trans last
    convert all using 1 <;> simp only [TreeEncoding.treeEncode, compileTree, records_append,
      List.reverse_append, List.append_assoc, treeTicks]
    omega

theorem forest_exact (ts : Forest A) (suffix : List Bool) (pending : List (Action A)) (output : List Bool) :
    RunsExactly (machine e C entry).computer.step
      (active e (TreeEncoding.forestEncode e ts ++ suffix) (.forest :: pending) output)
      (active e suffix pending ((records (opEncoding e) (compileForest ts)).reverse ++ output)) (forestTicks e ts) := by
  cases ts with
  | nil => exact prepare_nil e C entry hlabels suffix pending output
  | cons p t ts =>
    have first := prepare_cons e C entry hlabels p
      (TreeEncoding.treeEncode e t ++ TreeEncoding.forestEncode e ts ++ suffix) pending output
    have child := tree_exact t (TreeEncoding.forestEncode e ts ++ suffix)
      (.forest :: (consCode p).map Action.emit ++ pending) output
    have rest := forest_exact ts suffix ((consCode p).map Action.emit ++ pending)
      ((records (opEncoding e) (compileTree t)).reverse ++ output)
    have last := emit_all e C entry hlabels (consCode p) suffix pending
      ((records (opEncoding e) (compileForest ts)).reverse ++ ((records (opEncoding e) (compileTree t)).reverse ++ output))
    have all := ((first.trans (by simpa only [consTasks, List.cons_append, List.append_assoc] using child)).trans rest).trans
      (by simpa only [List.append_assoc] using last)
    convert all using 1 <;> simp only [TreeEncoding.forestEncode, List.cons_append, compileForest,
      records_append, List.reverse_append, List.append_assoc, forestTicks]
    omega
end

theorem closed_exact (a : A) (ts : Forest A) (suffix : List Bool) (pending : List (Action A)) (output : List Bool) :
    RunsExactly (machine e C entry).computer.step
      (active e (Holant.Algebraic.frame (e.encode a) ++ TreeEncoding.forestEncode e ts ++ suffix) (.closed :: pending) output)
      (active e suffix pending ((records (opEncoding e) (compileClosed a ts)).reverse ++ output)) (closedTicks e a ts) := by
  have first := prepare_closed e C entry hlabels a (TreeEncoding.forestEncode e ts ++ suffix) pending output
  have middle := forest_exact e C entry hlabels ts suffix ((rootCode a).map Action.emit ++ pending) output
  have last := emit_all e C entry hlabels (rootCode a) suffix pending
    ((records (opEncoding e) (compileForest ts)).reverse ++ output)
  have all := (first.trans (by simpa only [closedTasks, List.cons_append] using middle)).trans last
  convert all using 1 <;> simp only [compileClosed, records_append, List.reverse_append, List.append_assoc, closedTicks]
  omega

end Holant.OneHot.StackProgram.GraphCodeMachine
