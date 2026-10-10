import Holant.OneHot.StackProgram.GraphCodeMachine.Clean
import Mathlib.Tactic.Linarith

/-! Linear transition bounds in the actual prepared input length. -/
namespace Holant.OneHot.StackProgram.GraphCodeMachine
open Computability Holant.Complexity
variable {A : Type} (e : Encoding A Bool) (C : ℕ)
set_option maxHeartbeats 800000

def unitBudget (C : ℕ) : ℕ := 50 * (C + 20)
def rate (C : ℕ) : ℕ := unitBudget C + 19 * (2 * C + 14)
def overhead (C : ℕ) : ℕ := unitBudget C + 5 * (2 * C + 14) + 16

variable (hlabels : ∀ a, (e.encode a).length ≤ C)
include hlabels

theorem emitTicks_le (code : Code A) : emitTicks e code ≤ (2 * C + 21) * code.length := by
  induction code with
  | nil => simp [emitTicks]
  | cons op code ih =>
    have h := opEncode_length_le e C hlabels op
    simp only [emitTicks, List.map_cons, List.sum_cons, List.length_cons] at *
    nlinarith

mutual
theorem treeTicks_le (t : Tree A) : treeTicks e t ≤ unitBudget C * (t.vertices + t.edges) := by
  cases t with
  | node a b ts =>
    have hi := forestTicks_le ts
    have he := emitTicks_le e C hlabels (nodeCode a b)
    change emitTicks e (nodeCode a b) ≤ (2 * C + 21) * 11 at he
    have ha := hlabels a
    have hb := hlabels b
    simp only [treeTicks, Tree.vertices, Tree.edges]
    unfold unitBudget at *
    nlinarith

theorem forestTicks_le (ts : Forest A) : forestTicks e ts ≤ unitBudget C * (ts.vertices + ts.edges) + 10 := by
  cases ts with
  | nil => simp [forestTicks, Forest.vertices, Forest.edges]
  | cons p t ts =>
    have ht := treeTicks_le t
    have hs := forestTicks_le ts
    have he := emitTicks_le e C hlabels (consCode p)
    change emitTicks e (consCode p) ≤ (2 * C + 21) * 19 at he
    have hp := hlabels p
    simp only [forestTicks, Forest.vertices, Forest.edges]
    unfold unitBudget at *
    nlinarith
end

theorem closedTicks_le (a : A) (ts : Forest A) :
    closedTicks e a ts ≤ unitBudget C * (ts.vertices + ts.edges + 1) := by
  have hs := forestTicks_le e C hlabels ts
  have he := emitTicks_le e C hlabels (rootCode a)
  change emitTicks e (rootCode a) ≤ (2 * C + 21) * 3 at he
  have ha := hlabels a
  unfold closedTicks unitBudget at *
  nlinarith

omit hlabels in
mutual
theorem tree_size_le_input (t : Tree A) : t.vertices + t.edges ≤ (TreeEncoding.treeEncode e t).length := by
  cases t with
  | node a b ts =>
    have hs := forest_size_le_input ts
    simp only [TreeEncoding.treeEncode, Tree.vertices, Tree.edges, List.length_append, Holant.Algebraic.frame_length]
    omega

theorem forest_size_le_input (ts : Forest A) : ts.vertices + ts.edges + 1 ≤ (TreeEncoding.forestEncode e ts).length := by
  cases ts with
  | nil => rfl
  | cons p t ts =>
    have ht := tree_size_le_input t
    have hs := forest_size_le_input ts
    simp only [TreeEncoding.forestEncode, Forest.vertices, Forest.edges, List.length_append,
      List.length_cons, Holant.Algebraic.frame_length]
    omega
end

theorem tree_time_le (t : Tree A) :
    treeTicks e t + ((codeEncoding e).encode (compileTree t)).length + 5 ≤
      rate C * (TreeEncoding.treeEncode e t).length + overhead C := by
  have ht := treeTicks_le e C hlabels t
  have hc := codeEncoding_length_le e C hlabels (compileTree t)
  have hs := tree_size_le_input e t
  simp only [length_compileTree] at hc
  unfold rate overhead
  nlinarith

theorem forest_time_le (ts : Forest A) :
    forestTicks e ts + ((codeEncoding e).encode (compileForest ts)).length + 5 ≤
      rate C * (TreeEncoding.forestEncode e ts).length + overhead C := by
  have ht := forestTicks_le e C hlabels ts
  have hc := codeEncoding_length_le e C hlabels (compileForest ts)
  have hs := forest_size_le_input e ts
  simp only [length_compileForest] at hc
  unfold rate overhead
  nlinarith

theorem closed_time_le (a : A) (ts : Forest A) :
    closedTicks e a ts + ((codeEncoding e).encode (compileClosed a ts)).length + 5 ≤
      rate C * (Holant.Algebraic.frame (e.encode a) ++ TreeEncoding.forestEncode e ts).length + overhead C := by
  have ht := closedTicks_le e C hlabels a ts
  have hc := codeEncoding_length_le e C hlabels (compileClosed a ts)
  have hs := forest_size_le_input e ts
  simp only [length_compileClosed] at hc
  simp only [List.length_append, Holant.Algebraic.frame_length]
  unfold rate overhead
  nlinarith

end Holant.OneHot.StackProgram.GraphCodeMachine
