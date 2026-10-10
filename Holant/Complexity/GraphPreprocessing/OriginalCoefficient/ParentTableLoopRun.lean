import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentTableLoopSpec

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentTableLoop
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

theorem loop_prefix (w : Computes (RawParentRow.inputEncoding s b arity) ParentRowEncoding.row RawParentRow.value)
    (r : RawClosedNetwork) (h : r.WellFormed s b arity) (n : ℕ) (hn : n≤r.vertices.length) (output : List Bool) :
    ∃ steps, steps≤n*(roundPolynomial w).eval (RawClosedNetwork.encoding.encode r).length+1 ∧
      RunsExactly (TM2.step (program w.machine))
        (cleanConfig w.machine (.inr 6) (RawClosedNetwork.encoding.encode r) (List.replicate n true) output [] [])
        (cleanConfig w.machine (.inr 18) (RawClosedNetwork.encoding.encode r) []
          (prefixWord (r.graph h) n++output) [] []) steps := by
  induction n generalizing output with
  | zero =>
    refine ⟨1,by simp,?_⟩
    simpa only [List.replicate_zero,prefix_zero,List.nil_append] using
      runsExactly_one (loop_nil w.machine (RawClosedNetwork.encoding.encode r) output [])
  | succ n ih =>
    have hv : n<r.vertices.length := by omega
    let v : Fin r.vertices.length := ⟨n,hv⟩
    let x : RawParentRow.Input s b arity := ⟨⟨r,h⟩,v⟩
    let result := ParentRowEncoding.row.encode (RawParentRow.value x)
    let run := w.outputs x
    have source : (fun c => c.bind w.machine.computer.step)^[run.steps]
        (some (initList w.machine.computer (Holant.Algebraic.frame (RawClosedNetwork.encoding.encode r)++List.replicate n true))) =
      some (haltList w.machine.computer result) := run.evals_in_steps
    have first := round_exact w.machine (RawClosedNetwork.encoding.encode r) (List.replicate n true)
      output [] result run.steps source
    obtain ⟨steps,hs,last⟩ := ih (by omega) (entry result++output)
    refine ⟨steps+(run.steps+4*(RawClosedNetwork.encoding.encode r).length+2*(List.replicate n true).length+2*result.length+12),?_,?_⟩
    · have hb := round_bound w r h v
      change run.steps+4*(RawClosedNetwork.encoding.encode r).length+2*n+2*result.length+12≤_
        at hb
      simp only [List.length_replicate]
      nlinarith
    · have all := first.trans last
      simpa only [List.replicate_succ,prefix_succ (r.graph h) n hv,List.append_assoc,result,RawParentRow.value,x,v] using all

theorem package_run (w : Computes (RawParentRow.inputEncoding s b arity) ParentRowEncoding.row RawParentRow.value)
    (r : RawClosedNetwork) (h : r.WellFormed s b arity) :
    ∃ steps, steps≤(timePolynomial w).eval (RawClosedNetwork.encoding.encode r).length ∧
      RunsExactly (machine w.machine).computer.step
        (initList (machine w.machine).computer (CountsPackage.word r))
        (haltList (machine w.machine).computer (ParentRowEncoding.table.encode (r.graph h).parentTable)) steps := by
  have first := enter_loop w.machine (RawClosedNetwork.encoding.encode r)
    (List.replicate r.vertices.length true) (List.replicate r.edges.length true)
  obtain ⟨n,hn,loop⟩ := loop_prefix w r h r.vertices.length (le_refl _) [false]
  have hp : prefixWord (r.graph h) r.vertices.length++[false]=ParentRowEncoding.table.encode (r.graph h).parentTable := prefix_full (r.graph h)
  rw [hp] at loop
  have last := finish_exact w.machine (RawClosedNetwork.encoding.encode r) (ParentRowEncoding.table.encode (r.graph h).parentTable)
  have all := (first.trans loop).trans last
  refine ⟨((RawClosedNetwork.encoding.encode r).length+2)+
    (n+(2*(RawClosedNetwork.encoding.encode r).length+2*(List.replicate r.vertices.length true).length+
      (List.replicate r.edges.length true).length+6)),?_,?_⟩
  · have hc := r.counts_le_encoded_length
    have hv : r.vertices.length≤(RawClosedNetwork.encoding.encode r).length := by omega
    have hm := Nat.mul_le_mul_right ((roundPolynomial w).eval (RawClosedNetwork.encoding.encode r).length) hv
    simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,List.length_replicate]
    omega
  · rw [initial]
    exact all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentTableLoop
