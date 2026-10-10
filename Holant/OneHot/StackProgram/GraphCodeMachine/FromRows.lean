import Holant.OneHot.StackProgram.GraphCodeMachine.Interface
import Holant.Complexity.GraphPreprocessing.Traversal.Bounds
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

/-! Actual pointer-table expansion followed by the finite closed-tree compiler.
The only prepared boundary is the physical original-ID row table and initial
reference stream. No decoded tree is passed to a running transition. -/
namespace Holant.OneHot.StackProgram.GraphCodeMachine.FromRows
open Turing Computability Holant.Complexity StackProtocol
open Holant.Complexity.GraphPreprocessing
variable {A : Type} [Fintype A] (e : Encoding A Bool) (C : ℕ)
set_option backward.isDefEq.respectTransparency false

abbrev machine : BinaryCompose.Machine :=
  Traversal.preparedMachine.compose (GraphCodeMachine.machine e C .closed)

noncomputable def timePolynomial : Polynomial ℕ :=
  8 * Polynomial.X ^ 2 + 18 * Polynomial.X + 10 +
    Polynomial.C (rate C + 2) * (Polynomial.X + Polynomial.X ^ 2) + Polynomial.C (overhead C + 2)

/-- A derived bound on emitted data, obtained from the actual table grammar and
source-counted traversal budget rather than a separate size certificate. -/
theorem expanded_length_le {rows : List (List Bool)} {pending out : List Bool} {count : ℕ}
    (h : Traversal.Expands rows pending out count) (hc : count ≤ rows.length) :
    out.length ≤ (Traversal.preparedInput rows pending).length + (Traversal.preparedInput rows pending).length ^ 2 := by
  have hn := Traversal.table_count_le rows
  have ho := h.output_length
  have hm := Nat.mul_le_mul_right (Traversal.tableBits rows).length (le_trans hc hn)
  have hin : (Traversal.preparedInput rows pending).length = 2 * (Traversal.tableBits rows).length + 1 + pending.length := by
    simp only [Traversal.preparedInput, List.length_append, Holant.Algebraic.frame_length]
  rw [hin]
  nlinarith [Nat.zero_le (pending.length ^ 2), Nat.zero_le (pending.length * (Traversal.tableBits rows).length)]

/-- Complete physical table-to-bytecode execution, including table validation,
source-budget creation, all indexed reads, intermediate transfer and final halt. -/
theorem closed_exact (hlabels : ∀ a, (e.encode a).length ≤ C)
    (rows : List (List Bool)) (pending : List Bool) (a : A) (ts : Forest A) (count : ℕ)
    (h : Traversal.Expands rows pending ((closedEncoding e).encode (a, ts)) count) (hc : count ≤ rows.length) :
    ∃ time, time ≤ (timePolynomial C).eval (Traversal.preparedInput rows pending).length ∧
      RunsExactly (machine e C).computer.step
        (initList (machine e C).computer (Traversal.preparedInput rows pending))
        (haltList (machine e C).computer ((codeEncoding e).encode (compileClosed a ts))) time := by
  obtain ⟨first, hfirst, run⟩ := Traversal.clean_execute_input_bound h hc
  have last := compile_closed_exact e C hlabels a ts
  have all := BinaryCompose.Machine.compose_run Traversal.preparedMachine (GraphCodeMachine.machine e C .closed)
    _ _ _ _ _ run last
  have hout := expanded_length_le h hc
  have hlast := closed_time_le e C hlabels a ts
  change closedTicks e a ts + ((codeEncoding e).encode (compileClosed a ts)).length + 5 ≤
    rate C * ((closedEncoding e).encode (a, ts)).length + overhead C at hlast
  refine ⟨_, ?_, all⟩
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_C]
  unfold Traversal.inputTimeBound at hfirst
  have hm := Nat.mul_le_mul_left (rate C + 2) hout
  nlinarith

/-- The same assembled run includes a fixed finite primitive-instruction budget. -/
theorem closed_primitive (hlabels : ∀ a, (e.encode a).length ≤ C)
    (rows : List (List Bool)) (pending : List Bool) (a : A) (ts : Forest A) (count : ℕ)
    (h : Traversal.Expands rows pending ((closedEncoding e).encode (a, ts)) count) (hc : count ≤ rows.length) :
    ∃ time, time ≤ (timePolynomial C).eval (Traversal.preparedInput rows pending).length ∧
      RunsExactly (machine e C).computer.step
        (initList (machine e C).computer (Traversal.preparedInput rows pending))
        (haltList (machine e C).computer ((codeEncoding e).encode (compileClosed a ts))) time ∧
      FixedFieldMachines.primitiveCost (machine e C) time
        (some (initList (machine e C).computer (Traversal.preparedInput rows pending))) ≤
          (timePolynomial C).eval (Traversal.preparedInput rows pending).length * (machine e C).primitiveBudget := by
  obtain ⟨time, ht, run⟩ := closed_exact e C hlabels rows pending a ts count h hc
  exact ⟨time, ht, run, le_trans (FixedFieldMachines.primitiveCost_le _ _ _) (Nat.mul_le_mul_right _ ht)⟩

open Holant.OneHot.Decomposition Holant.OneHot.Computable.Evaluation
variable {n m : ℕ} {endpoint : Fin m → Bool → Fin n} {root : Fin n}

/-- Original-ID rows expand to the exact ordered original labelled tree, then
compile through the same physical intermediate word. Coefficients remain labels. -/
theorem original_closed (hlabels : ∀ a, (e.encode a).length ≤ C)
    (t : RootedSpanning endpoint root) (a b : Fin n → A)
    (port : {u : Fin n // u ≠ root} → A) (D : ℕ) (bound : ∀ u, t.depth u ≤ D) :
    let rows := Traversal.originalRows t e a b port true
    let children := Summary.ofList (fun u : Child t root => port ⟨u.1,u.2.1⟩)
      (fun u => build t a b port D u.1) (children t root)
    ∃ time, time ≤ (timePolynomial C).eval (Traversal.preparedInput rows (Traversal.reference root.val)).length ∧
      RunsExactly (machine e C).computer.step
        (initList (machine e C).computer (Traversal.preparedInput rows (Traversal.reference root.val)))
        (haltList (machine e C).computer ((codeEncoding e).encode (compileClosed (a root) children))) time := by
  have h := Traversal.expand_closed t e a b port D bound
  rw [Traversal.tree_vertices_original t a b port D bound] at h
  apply closed_exact e C hlabels _ _ _ _ n
  · exact h
  · simp

end Holant.OneHot.StackProgram.GraphCodeMachine.FromRows
