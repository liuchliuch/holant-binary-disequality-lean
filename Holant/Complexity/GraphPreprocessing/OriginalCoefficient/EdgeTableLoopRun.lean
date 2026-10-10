import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoopFinish
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeWordBounds
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CountsPackageInterface

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoop
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

noncomputable def roundBound (w : Computes (EdgeWord.inputEncoding s b arity) Frame.wordEncoding EdgeWord.word)
    (r : RawClosedNetwork) : ℕ :=
  w.time.eval (3*((RawClosedNetwork.encoding.encode r).length+1))+
    10*(RawClosedNetwork.encoding.encode r).length+10

/-- The provider's full actual run plus every surrounding physical operation
fits a bound derived from the original graph, uniformly over original indices. -/
theorem round_bound (w : Computes (EdgeWord.inputEncoding s b arity) Frame.wordEncoding EdgeWord.word)
    (r : RawClosedNetwork) (h : r.WellFormed s b arity) (e : Fin r.edges.length) :
    (w.outputs ⟨⟨r,h⟩,e⟩).steps+4*(RawClosedNetwork.encoding.encode r).length+2*e.val+
      2*(EdgeWord.word ⟨⟨r,h⟩,e⟩).length+10 ≤ roundBound w r := by
  have hi := EdgeWord.input_length_le_original (⟨⟨r,h⟩,e⟩ : EdgeWord.Input s b arity)
  have hm := natPolynomial_eval_mono w.time hi
  have hs := (w.outputs ⟨⟨r,h⟩,e⟩).steps_le_m
  have hw := EdgeWord.output_length (⟨⟨r,h⟩,e⟩ : EdgeWord.Input s b arity)
  change w.time.eval ((EdgeWord.inputEncoding s b arity).encode ⟨⟨r,h⟩,e⟩).length ≤
    w.time.eval (3*((RawClosedNetwork.encoding.encode r).length+1)) at hm
  change (EdgeWord.word ⟨⟨r,h⟩,e⟩).length ≤ 2*r.vertices.length at hw
  have hc := r.counts_le_encoded_length
  have he := e.isLt
  unfold roundBound
  omega

/-- Exact descending-loop simulation. No supplied counter/time certificate is
needed beyond the original index bound proved by actual record counting. -/
theorem loop_prefix (w : Computes (EdgeWord.inputEncoding s b arity) Frame.wordEncoding EdgeWord.word)
    (r : RawClosedNetwork) (h : r.WellFormed s b arity) (n : ℕ) (hn : n≤r.edges.length)
    (output vertices : List Bool) :
    ∃ steps, steps ≤ n*roundBound w r+1 ∧
      RunsExactly (TM2.step (program w.machine))
        (cleanConfig w.machine (.inr 6) (RawClosedNetwork.encoding.encode r) (List.replicate n true) output vertices [])
        (cleanConfig w.machine (.inr 18) (RawClosedNetwork.encoding.encode r) []
          (EdgeWord.prefixWord r h n ++ output) vertices []) steps := by
  induction n generalizing output with
  | zero =>
    refine ⟨1,by simp,?_⟩
    simpa only [List.replicate_zero,EdgeWord.prefix_zero,List.nil_append] using
      runsExactly_one (loop_nil w.machine (RawClosedNetwork.encoding.encode r) output vertices)
  | succ n ih =>
    have he : n<r.edges.length := by omega
    let e : Fin r.edges.length := ⟨n,he⟩
    let x : EdgeWord.Input s b arity := ⟨⟨r,h⟩,e⟩
    let run := w.outputs x
    have source : (fun c => c.bind w.machine.computer.step)^[run.steps]
        (some (initList w.machine.computer (Holant.Algebraic.frame (RawClosedNetwork.encoding.encode r) ++ List.replicate n true))) =
        some (haltList w.machine.computer (EdgeWord.word x)) := run.evals_in_steps
    have first := round_exact w.machine (RawClosedNetwork.encoding.encode r) (List.replicate n true)
      output vertices (EdgeWord.word x) run.steps source
    obtain ⟨steps,hs,last⟩ := ih (by omega) (EdgeWord.word x++output)
    refine ⟨steps+(run.steps+4*(RawClosedNetwork.encoding.encode r).length+2*(List.replicate n true).length+
      2*(EdgeWord.word x).length+10),?_,?_⟩
    · have hr := round_bound w r h e
      change run.steps+4*(RawClosedNetwork.encoding.encode r).length+2*n+2*(EdgeWord.word x).length+10 ≤ roundBound w r at hr
      simp only [List.length_replicate]
      nlinarith
    · have all := first.trans last
      simpa only [List.replicate_succ,EdgeWord.prefix_succ r h n he,List.append_assoc,x,e] using all

/-- A complete clean materialization from the actual raw-derived counter
package. The final word retains all original vertices and ordered edge ends. -/
theorem package_run (w : Computes (EdgeWord.inputEncoding s b arity) Frame.wordEncoding EdgeWord.word)
    (r : RawClosedNetwork) (h : r.WellFormed s b arity) :
    ∃ steps, steps ≤ r.edges.length*roundBound w r+3*(RawClosedNetwork.encoding.encode r).length+
        4*r.vertices.length+2*r.edges.length+12 ∧
      RunsExactly (machine w.machine).computer.step
        (initList (machine w.machine).computer (CountsPackage.word r))
        (haltList (machine w.machine).computer
          (Holant.Algebraic.frame (List.replicate r.vertices.length true) ++
            ReachRound.encode (ReachRound.graphEdges (r.graph h)))) steps := by
  have first := enter_loop w.machine (RawClosedNetwork.encoding.encode r)
    (List.replicate r.vertices.length true) (List.replicate r.edges.length true)
  obtain ⟨n,hn,loop⟩ := loop_prefix w r h r.edges.length (le_refl _) [] (List.replicate r.vertices.length true)
  simp only [List.append_nil,EdgeWord.prefix_full] at loop
  have last := finish_exact w.machine (RawClosedNetwork.encoding.encode r)
    (ReachRound.encode (ReachRound.graphEdges (r.graph h))) (List.replicate r.vertices.length true)
  have all := (first.trans loop).trans last
  refine ⟨(RawClosedNetwork.encoding.encode r).length+2*(List.replicate r.vertices.length true).length+5+
    (n+(2*(RawClosedNetwork.encoding.encode r).length+2*(List.replicate r.vertices.length true).length+
      2*(List.replicate r.edges.length true).length+6)),?_,?_⟩
  · simp only [List.length_replicate]
    omega
  · rw [initial]
    exact all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoop
