import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextWordTable

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextWordTable
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines ParentTableLoop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false
variable {A : Type} {ea : Encoding A Bool} {size : A → ℕ}
  {f : (Σ x : A, Fin (size x)) → List Bool}

theorem loop_prefix (hsize : ∀x,size x≤(ea.encode x).length) (w : Computes (queryEncoding ea size) Frame.wordEncoding f)
    (x : A) (n : ℕ) (hn : n≤size x) (out : List Bool) :
    ∃ steps, steps≤n*(roundPolynomial w).eval (ea.encode x).length+1 ∧
      RunsExactly (TM2.step (program w.machine))
        (cleanConfig w.machine (.inr 6) (ea.encode x) (List.replicate n true) out [] [])
        (cleanConfig w.machine (.inr 18) (ea.encode x) [] (prefixWord size f x n++out) [] []) steps := by
  induction n generalizing out with
  | zero =>
    refine ⟨1,by simp,?_⟩
    simpa only [List.replicate_zero,prefix_zero,List.nil_append] using runsExactly_one (loop_nil w.machine (ea.encode x) out [])
  | succ n ih =>
    have hv : n<size x := by omega
    let v : Fin (size x) := ⟨n,hv⟩
    let query : (Σ x : A, Fin (size x)) := ⟨x,v⟩
    let result := f query
    let run := w.outputs query
    have source : (fun c => c.bind w.machine.computer.step)^[run.steps]
        (some (initList w.machine.computer (Holant.Algebraic.frame (ea.encode x)++List.replicate n true)))=
      some (haltList w.machine.computer result) := run.evals_in_steps
    have first := round_exact w.machine (ea.encode x) (List.replicate n true) out [] result run.steps source
    obtain ⟨steps,hs,last⟩ := ih (by omega) (entry result++out)
    refine ⟨steps+(run.steps+4*(ea.encode x).length+2*(List.replicate n true).length+2*result.length+12),?_,?_⟩
    · have hb := round_bound hsize w x v
      change run.steps+4*(ea.encode x).length+2*n+2*result.length+12≤_ at hb
      simp only [List.length_replicate]
      nlinarith
    · have all := first.trans last
      simpa only [List.replicate_succ,prefix_succ size f x n hv,List.append_assoc,result,query,v] using all

theorem package_run (hsize : ∀x,size x≤(ea.encode x).length) (w : Computes (queryEncoding ea size) Frame.wordEncoding f)
    (x : A) :
    ∃ steps, steps≤(timePolynomial w).eval (ea.encode x).length ∧
      RunsExactly (machine w.machine).computer.step
        (initList (machine w.machine).computer ((packageEncoding ea size).encode x))
        (haltList (machine w.machine).computer (framedListEncode Frame.wordEncoding (rows size f x))) steps := by
  have first := enter_loop w.machine (ea.encode x) (List.replicate (size x) true) (List.replicate 0 true)
  obtain ⟨n,hn,loop⟩ := loop_prefix hsize w x (size x) (le_refl _) [false]
  rw [prefix_full] at loop
  have last := finish_exact w.machine (ea.encode x) (framedListEncode Frame.wordEncoding (rows size f x))
  have all := (first.trans loop).trans last
  refine ⟨((ea.encode x).length+2)+
    (n+(2*(ea.encode x).length+2*(List.replicate (size x) true).length+
      (List.replicate 0 true).length+6)),?_,?_⟩
  · have hc := hsize x
    have hv : size x≤(ea.encode x).length := by omega
    have hm := Nat.mul_le_mul_right ((roundPolynomial w).eval (ea.encode x).length) hv
    simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,List.length_replicate]
    omega
  · rw [initial]
    exact all

noncomputable def packageComputes (hsize : ∀x,size x≤(ea.encode x).length) (w : Computes (queryEncoding ea size) Frame.wordEncoding f) :
    Computes (packageEncoding ea size) (framedListEncoding Frame.wordEncoding) (rows size f) where
  machine := machine w.machine
  time := timePolynomial w
  outputs x := {
    steps := Classical.choose (package_run hsize w x)
    evals_in_steps := (Classical.choose_spec (package_run hsize w x)).2
    steps_le_m := le_trans (Classical.choose_spec (package_run hsize w x)).1
      (natPolynomial_eval_mono (timePolynomial w) (raw_length_le_package ea size x)) }
noncomputable def countPackageComputes (count : Computes ea UnaryBinary.unaryEncoding size) :
    Computes ea (packageEncoding ea size) id :=
  recode (pairComputes (identityComputes ea) (pairComputes count (constantComputes ea Frame.wordEncoding [])))
    id (fun _ => rfl) (fun _ => rfl)
noncomputable def computes (hsize : ∀x,size x≤(ea.encode x).length)
    (count : Computes ea UnaryBinary.unaryEncoding size)
    (w : Computes (queryEncoding ea size) Frame.wordEncoding f) :
    Computes ea (framedListEncoding Frame.wordEncoding) (rows size f) :=
  (countPackageComputes count).andThen (packageComputes hsize w)
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextWordTable
