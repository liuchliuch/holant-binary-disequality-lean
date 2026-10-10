import Holant.Complexity.FixedFieldMachines.MachineSyntax
import Holant.Proofs.LinearProgramming.Support.MachineCombinators.ParentTableLoopFinish
import Holant.Complexity.GraphPreprocessing.UnaryBinary
import Holant.Complexity.FixedFieldMachines.Constant

/-! A real finite descending-counter loop emits every unary index below an
executed count. Its frames are prepended, hence the output is increasing. -/
open Holant.Complexity Holant.Complexity.GraphPreprocessing
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.UnaryRange
open Holant.Complexity Holant.Complexity.GraphPreprocessing
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines ParentTableLoop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false
def bits (n : ℕ) := (List.range n).flatMap (fun i => entry (List.replicate i true))
@[simp] theorem bits_zero : bits 0=[] := rfl
theorem bits_succ (n : ℕ) : bits (n+1)=bits n++entry (List.replicate n true) := by
  simp [bits,List.range_succ]
theorem bits_encode (n : ℕ) : bits n++[false]=framedListEncode UnaryBinary.unaryEncoding (List.range n) := by
  have general (xs : List ℕ) : xs.flatMap (fun i => entry (List.replicate i true))++[false]=
      framedListEncode UnaryBinary.unaryEncoding xs := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      simpa only [List.flatMap_cons,List.append_assoc,framedListEncode,entry,UnaryBinary.unaryEncoding,List.cons_append] using
        (congrArg (fun tail => entry (List.replicate a true)++tail) ih)
  exact general _
noncomputable def provider := Wiring.secondComputes Frame.wordEncoding UnaryBinary.unaryEncoding
noncomputable def roundPolynomial : Polynomial ℕ := provider.time.comp (Polynomial.X+1)+4*Polynomial.X+12
noncomputable def packagePolynomial : Polynomial ℕ := Polynomial.X*roundPolynomial+2*Polynomial.X+9
abbrev loopMachine : Machine := ParentTableLoop.machine secondMachine
theorem loop (N n : ℕ) (hn : n≤N) (out : List Bool) :
    ∃ steps, steps≤n*roundPolynomial.eval N+1 ∧
      RunsExactly (TM2.step (program secondMachine))
        (cleanConfig secondMachine (.inr 6) [] (List.replicate n true) out [] [])
        (cleanConfig secondMachine (.inr 18) [] [] (bits n++out) [] []) steps := by
  induction n generalizing out with
  | zero =>
    exact ⟨1,by simp,by simpa using runsExactly_one (loop_nil secondMachine [] out [])⟩
  | succ n ih =>
    let run := provider.outputs ([],n)
    have source : (fun c => c.bind secondMachine.computer.step)^[run.steps]
        (some (initList secondMachine.computer (Holant.Algebraic.frame []++List.replicate n true)))=
      some (haltList secondMachine.computer (List.replicate n true)) := run.evals_in_steps
    have first := round_exact secondMachine [] (List.replicate n true) out [] (List.replicate n true) run.steps source
    obtain ⟨steps,hs,last⟩ := ih (by omega) (entry (List.replicate n true)++out)
    refine ⟨steps+(run.steps+4*0+2*(List.replicate n true).length+2*(List.replicate n true).length+12),?_,?_⟩
    · have hb := run.steps_le_m
      have hp := natPolynomial_eval_mono provider.time (show n+1≤N+1 by omega)
      simp only [pairEncoding_length,Frame.wordEncoding,id_eq,UnaryBinary.unaryEncoding,List.length_nil,List.length_replicate,
        Nat.mul_zero,Nat.zero_add] at hb
      rw [Nat.add_comm 1 n] at hb
      simp only [List.length_nil,List.length_replicate] at hb ⊢
      have hr : run.steps+4*n+12≤roundPolynomial.eval N := by
        simp only [roundPolynomial,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_X,Polynomial.eval_one,
          Polynomial.eval_mul,Polynomial.eval_ofNat]
        omega
      nlinarith
    · simpa only [List.replicate_succ,bits_succ,List.append_assoc,List.length_nil] using first.trans last
def packageEncoding : Encoding ℕ Bool where
  encode n := Holant.Algebraic.frame []++Holant.Algebraic.frame (List.replicate n true)
  decode word := do
    let (a,tail) ← Holant.Algebraic.unframe word
    let (b,rest) ← Holant.Algebraic.unframe tail
    if a=[] ∧ rest=[] then UnaryBinary.unaryEncoding.decode b else none
  decode_encode n := by
    have h := Holant.Algebraic.unframe_frame_append (List.replicate n true) []
    simp only [List.append_nil] at h
    simp [Holant.Algebraic.unframe_frame_append,h,UnaryBinary.unaryEncoding]
theorem package_run (n : ℕ) :
    ∃ steps, steps≤packagePolynomial.eval n ∧ RunsExactly loopMachine.computer.step
      (initList loopMachine.computer (packageEncoding.encode n))
      (haltList loopMachine.computer (framedListEncode UnaryBinary.unaryEncoding (List.range n))) steps := by
  have first := enter_loop secondMachine [] (List.replicate n true) []
  obtain ⟨steps,hs,middle⟩ := loop n n (le_refl _) [false]
  rw [bits_encode] at middle
  have last := finish_exact secondMachine [] (framedListEncode UnaryBinary.unaryEncoding (List.range n))
  have all := (first.trans middle).trans last
  refine ⟨2+(steps+(2*0+2*(List.replicate n true).length+0+6)),?_,?_⟩
  · simp only [List.length_nil,List.length_replicate,packagePolynomial,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]
    omega
  · rw [ParentTableLoop.initial]
    change RunsExactly (TM2.step (program secondMachine)) _ _ _
    simpa only [packageEncoding,List.append_nil,List.length_nil,Nat.zero_add] using all
noncomputable def packageComputes : Computes packageEncoding (framedListEncoding UnaryBinary.unaryEncoding) List.range where
  machine := loopMachine
  time := packagePolynomial
  outputs n := {
    steps := Classical.choose (package_run n)
    evals_in_steps := (Classical.choose_spec (package_run n)).2
    steps_le_m := le_trans (Classical.choose_spec (package_run n)).1
      (natPolynomial_eval_mono packagePolynomial (by simp [packageEncoding,Holant.Algebraic.frame_length]; omega)) }
noncomputable def prepareComputes : Computes UnaryBinary.unaryEncoding packageEncoding id :=
  recode (pairComputes (constantComputes UnaryBinary.unaryEncoding Frame.wordEncoding [])
    (pairComputes (identityComputes UnaryBinary.unaryEncoding)
      (constantComputes UnaryBinary.unaryEncoding Frame.wordEncoding []))) id (fun _ => rfl)
    (fun _ => by simp [pairEncoding_encode,Frame.wordEncoding,packageEncoding,UnaryBinary.unaryEncoding])
noncomputable def computes : Computes UnaryBinary.unaryEncoding (framedListEncoding UnaryBinary.unaryEncoding) List.range :=
  prepareComputes.andThen packageComputes
abbrev prepareMachine : Machine := pairMachine (Constant.machine []) (pairMachine identityMachine (Constant.machine []))
abbrev machine : Machine := prepareMachine.compose loopMachine
@[simp] theorem computes_machine : computes.machine=machine := rfl
theorem inFP : InFP UnaryBinary.unaryEncoding (framedListEncoding UnaryBinary.unaryEncoding) List.range := computes.inFP
end Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.UnaryRange
