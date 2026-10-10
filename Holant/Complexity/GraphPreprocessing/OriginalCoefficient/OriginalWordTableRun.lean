import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OriginalWordTable

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OriginalWordTable
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines ParentTableLoop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ} {f : RawRootReach.Input s b arity → List Bool}

theorem loop_prefix (w : Computes (RawRootReach.inputEncoding s b arity) Frame.wordEncoding f)
    (r : RawClosedNetwork) (h : r.WellFormed s b arity) (n : ℕ) (hn : n≤r.vertices.length) (out : List Bool) :
    ∃ steps, steps≤n*(roundPolynomial w).eval (RawClosedNetwork.encoding.encode r).length+1 ∧
      RunsExactly (TM2.step (program w.machine))
        (cleanConfig w.machine (.inr 6) (RawClosedNetwork.encoding.encode r) (List.replicate n true) out [] [])
        (cleanConfig w.machine (.inr 18) (RawClosedNetwork.encoding.encode r) [] (prefixWord f r h n++out) [] []) steps := by
  induction n generalizing out with
  | zero =>
    refine ⟨1,by simp,?_⟩
    simpa only [List.replicate_zero,prefix_zero,List.nil_append] using runsExactly_one (loop_nil w.machine (RawClosedNetwork.encoding.encode r) out [])
  | succ n ih =>
    have hv : n<r.vertices.length := by omega
    let v : Fin r.vertices.length := ⟨n,hv⟩
    let x : RawRootReach.Input s b arity := ⟨⟨r,h⟩,v⟩
    let result := f x
    let run := w.outputs x
    have source : (fun c => c.bind w.machine.computer.step)^[run.steps]
        (some (initList w.machine.computer (Holant.Algebraic.frame (RawClosedNetwork.encoding.encode r)++List.replicate n true)))=
      some (haltList w.machine.computer result) := run.evals_in_steps
    have first := round_exact w.machine (RawClosedNetwork.encoding.encode r) (List.replicate n true) out [] result run.steps source
    obtain ⟨steps,hs,last⟩ := ih (by omega) (entry result++out)
    refine ⟨steps+(run.steps+4*(RawClosedNetwork.encoding.encode r).length+2*(List.replicate n true).length+2*result.length+12),?_,?_⟩
    · have hb := round_bound w r h v
      change run.steps+4*(RawClosedNetwork.encoding.encode r).length+2*n+2*result.length+12≤_ at hb
      simp only [List.length_replicate]
      nlinarith
    · have all := first.trans last
      simpa only [List.replicate_succ,prefix_succ f r h n hv,List.append_assoc,result,x,v] using all

theorem package_run (w : Computes (RawRootReach.inputEncoding s b arity) Frame.wordEncoding f)
    (r : RawClosedNetwork) (h : r.WellFormed s b arity) :
    ∃ steps, steps≤(timePolynomial w).eval (RawClosedNetwork.encoding.encode r).length ∧
      RunsExactly (machine w.machine).computer.step
        (initList (machine w.machine).computer (CountsPackage.word r))
        (haltList (machine w.machine).computer (framedListEncode Frame.wordEncoding (rows f r h))) steps := by
  have first := enter_loop w.machine (RawClosedNetwork.encoding.encode r) (List.replicate r.vertices.length true) (List.replicate r.edges.length true)
  obtain ⟨n,hn,loop⟩ := loop_prefix w r h r.vertices.length (le_refl _) [false]
  rw [prefix_full] at loop
  have last := finish_exact w.machine (RawClosedNetwork.encoding.encode r) (framedListEncode Frame.wordEncoding (rows f r h))
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

noncomputable def packageComputes (w : Computes (RawRootReach.inputEncoding s b arity) Frame.wordEncoding f) :
    Computes (EdgeTableLoop.packageEncoding s b arity) (framedListEncoding Frame.wordEncoding) (fun x => rows f x.val x.property) where
  machine := machine w.machine
  time := timePolynomial w
  outputs x := {
    steps := Classical.choose (package_run w x.val x.property)
    evals_in_steps := (Classical.choose_spec (package_run w x.val x.property)).2
    steps_le_m := le_trans (Classical.choose_spec (package_run w x.val x.property)).1
      (natPolynomial_eval_mono (timePolynomial w) (EdgeTableLoop.raw_length_le_package x)) }
noncomputable def computes (w : Computes (RawRootReach.inputEncoding s b arity) Frame.wordEncoding f) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) (framedListEncoding Frame.wordEncoding) (fun x => rows f x.val x.property) :=
  (RawEdgeTable.countsComputes s b arity).andThen (packageComputes w)
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OriginalWordTable
