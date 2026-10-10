import Holant.Complexity.GraphPreprocessing.Traversal.Prepared
import Mathlib.Tactic.Linarith

/-! Actual input-bit bounds for source-counted pointer expansion. The grammar
relation is a specification of the emitted word; all transition witnesses are
for the finite machine in Prepared. -/
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
namespace Holant.Complexity.GraphPreprocessing.Traversal
open Turing Computability StackProtocol Holant.Algebraic

theorem row_length_le_table (pre tail : List (List Bool)) (row : List Bool) :
    row.length ≤ (tableBits (pre++row::tail)).length := by
  induction pre with
  | nil => simp only [List.nil_append,tableBits_cons,List.length_cons,List.length_append,frame_length]; omega
  | cons a pre ih => simp only [List.cons_append,tableBits_cons,List.length_cons,List.length_append]; omega

/-- Each output bit comes from the physical input task word or an actually read
row, and there are exactly count such reads. -/
theorem Expands.output_length {rows : List (List Bool)} {pending out : List Bool} {count : ℕ}
    (h : Expands rows pending out count) :
    2*out.length ≤ pending.length+count*(tableBits rows).length := by
  induction h with
  | nil => simp
  | literal b next ih =>
    simp only [Traversal.literal,List.length_cons,List.length_nil,List.length_append] at *
    omega
  | @reference pending out count pre tail row table next ih =>
    subst rows
    have hr := row_length_le_table pre tail row
    simp only [List.length_append,reference_length,Nat.add_mul,Nat.one_mul] at *
    omega

def inputTimeBound (n : ℕ) : ℕ := 8*n*n+18*n+10

theorem cleanBound_le_input {rows : List (List Bool)} {pending out : List Bool} {count : ℕ}
    (h : Expands rows pending out count) (bound : count ≤ rows.length) :
    cleanBound rows out count ≤ inputTimeBound (preparedInput rows pending).length := by
  have ho := h.output_length
  have hn := table_count_le rows
  let T := (tableBits rows).length
  let P := pending.length
  have hc : count ≤ T := le_trans bound hn
  have hout : out.length ≤ P+T*T := by
    have hm := Nat.mul_le_mul_right T hc
    change 2*out.length ≤ P+count*T at ho
    omega
  have hmul : count*(5*T+8) ≤ T*(5*T+8) := Nat.mul_le_mul_right _ hc
  have hinput : (preparedInput rows pending).length = 2*T+1+P := by
    simp only [preparedInput,List.length_append,frame_length,T,P]
  rw [hinput]
  unfold cleanBound inputTimeBound
  change 3*out.length+count*(5*T+8)+6*T+rows.length+10 ≤ _
  have hs : rows.length ≤ T := hn
  nlinarith [Nat.zero_le (P*P), Nat.zero_le (P*T), Nat.zero_le (T*T)]

/-- Polynomial bound in the genuine serialized prepared input, including the
budget-producing table scan, table copies, indexed reads, and final cleanup. -/
theorem clean_execute_input_bound {rows : List (List Bool)} {pending out : List Bool} {count : ℕ}
    (h : Expands rows pending out count) (bound : count ≤ rows.length) :
    ∃ time, time ≤ inputTimeBound (preparedInput rows pending).length ∧
      RunsExactly preparedMachine.computer.step
        (initList preparedMachine.computer (preparedInput rows pending))
        (haltList preparedMachine.computer out) time := by
  obtain ⟨time,ht,run⟩ := clean_execute_bounded h bound
  exact ⟨time,le_trans ht (cleanBound_le_input h bound),run⟩

end Holant.Complexity.GraphPreprocessing.Traversal
