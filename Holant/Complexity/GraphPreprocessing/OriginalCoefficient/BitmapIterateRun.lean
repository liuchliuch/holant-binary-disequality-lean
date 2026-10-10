import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterateSpec

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false
local instance : DecidableEq roundMachine.K := roundMachine.decidableK
local instance : DecidableEq (Stack roundMachine) := (machine roundMachine).decidableK

/-- The actual provider's old and new bitmaps both have exactly V cells.
Thus every intermediate input width is the same original graph width. -/
theorem graph_step (g : Graph) (s : Finset g.Vertex) (index output : List Bool) :
    ∃ n, n≤roundPolynomial.eval (width g) ∧ RunsExactly (TM2.step (program roundMachine))
      (ready roundMachine (phase roundMachine 5) (NeighborPredicate.bitmap g s) [] (true::index) (edgeWord g) output [])
      (ready roundMachine (phase roundMachine 5) (NeighborPredicate.bitmap g (g.round s)) [] index (edgeWord g) output []) n := by
  let witness := BitmapRound.graph_timed g s
  let n := witness.steps
  have hs : (fun c => c.bind roundMachine.computer.step)^[n]
      (some (initList roundMachine.computer (Holant.Algebraic.frame (NeighborPredicate.bitmap g s)++edgeWord g))) =
        some (haltList roundMachine.computer (NeighborPredicate.bitmap g (g.round s))) := witness.evals_in_steps
  have run := round_exact roundMachine (NeighborPredicate.bitmap g s) index (edgeWord g) output
    (NeighborPredicate.bitmap g (g.round s)) n hs
  have htime : n≤BitmapRound.timePolynomial.eval (width g) := calc
    n ≤ BitmapRound.timePolynomial.eval (word g s).length := witness.steps_le_m
    _ = BitmapRound.timePolynomial.eval (width g) := by rw [word_length]
  refine ⟨n+2*(edgeWord g).length+7*g.vertices+11,?_,?_⟩
  · have hv := vertices_le_width g
    have he := edges_le_width g
    have h : n+2*(edgeWord g).length+7*g.vertices+11≤BitmapRound.timePolynomial.eval (width g)+9*width g+11 := by omega
    simpa [roundPolynomial] using h
  · have ht : n+2*(edgeWord g).length+7*g.vertices+11 = n+2*(edgeWord g).length+5*g.vertices+2*g.vertices+11 := by omega
    rw [ht]
    simpa only [NeighborPredicate.bitmap_length] using run

theorem loop_run (g : Graph) (s : Finset g.Vertex) (k : ℕ) (output : List Bool) :
    ∃ n, n≤k*roundPolynomial.eval (width g) ∧ RunsExactly (TM2.step (program roundMachine))
      (ready roundMachine (phase roundMachine 5) (NeighborPredicate.bitmap g s) [] (List.replicate k true) (edgeWord g) output [])
      (ready roundMachine (phase roundMachine 5) (NeighborPredicate.bitmap g ((g.round^[k]) s)) [] [] (edgeWord g) output []) n := by
  induction k generalizing s with
  | zero => exact ⟨0,by simp,rfl⟩
  | succ k ih =>
    obtain ⟨a,ha,first⟩ := graph_step g s (List.replicate k true) output
    obtain ⟨b,hb,rest⟩ := ih (g.round s)
    refine ⟨b+a,?_,?_⟩
    · nlinarith
    · simpa only [List.replicate_succ,Function.iterate_succ_apply] using first.trans rest

/-- The number of rounds is obtained from the physical initial bitmap scan.
All loader, replacement and final cleanup costs are part of this execution. -/
theorem whole_graph (g : Graph) (s : Finset g.Vertex) :
    ∃ n, n≤timePolynomial.eval (word g s).length ∧
      RunsExactly (machine roundMachine).computer.step (initList (machine roundMachine).computer (word g s))
        (haltList (machine roundMachine).computer (NeighborPredicate.bitmap g ((g.round^[g.vertices]) s))) n := by
  have prep := prepare roundMachine (NeighborPredicate.bitmap g s) (edgeWord g)
  simp only [NeighborPredicate.bitmap_length] at prep
  obtain ⟨n,hn,loop⟩ := loop_run g s g.vertices []
  have last := finish roundMachine (NeighborPredicate.bitmap g ((g.round^[g.vertices]) s)) (edgeWord g) []
  simp only [NeighborPredicate.bitmap_length,List.append_nil] at last
  have all := (prep.trans loop).trans last
  refine ⟨((edgeWord g).length+2*g.vertices+5)+(n+(5*g.vertices+2*(edgeWord g).length+8)),?_,?_⟩
  · have hv := vertices_le_width g
    have hm := Nat.mul_le_mul_right (roundPolynomial.eval (width g)) hv
    have hw : width g=2*g.vertices+1+(edgeWord g).length := rfl
    have bound : ((edgeWord g).length+2*g.vertices+5)+(n+(5*g.vertices+2*(edgeWord g).length+8)) ≤
        width g*roundPolynomial.eval (width g)+4*width g+13 := by omega
    simpa [timePolynomial,word_length] using bound
  · rw [initial]
    change RunsExactly (TM2.step (program roundMachine)) _ _ _
    exact all

theorem whole_run (x : Input) :
    ∃ n, n≤timePolynomial.eval (inputEncoding.encode x).length ∧
      RunsExactly (machine roundMachine).computer.step (initList (machine roundMachine).computer (inputEncoding.encode x))
        (haltList (machine roundMachine).computer (value x)) n := by
  simpa only [initial_word,value] using whole_graph (graph x) (initialSet x)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterate
