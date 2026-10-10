import Holant.OneHot.StackProgram.Machine.DynamicFetch
import Holant.OneHot.StackProgram.Machine.Certificates

/-! Timed simulation of arbitrarily long serialized programs by one finite TM2.
The bound depends on executed instructions and certified word/stack sizes. -/
namespace Holant.OneHot.StackProgram.Machine.Interpreter
open Turing Computability Holant.Complexity StackProtocol Family
variable {A V : Type} [Fintype A] [DecidableEq A] [CommSemiring V]
variable (labels : Encoding A Bool) (C : ℕ) (e : Encoding V Bool) (coeff : A → V)
variable (lits : Kernels.Literals e coeff) (providers : Operator.Providers e)

abbrev machine : BinaryCompose.Machine := Dynamic.machine (Kernels.machine lits providers) labels C

/-- Whole encoded stack transfers and opcode parsing are charged each time. -/
def instructionBound (W H : ℕ) : ℕ :=
  Kernels.timeBound providers W + 2 * (C + 6) + 4 * ((2 * W + 2) * H + 1) + 9

omit [Fintype A] [DecidableEq A] [CommSemiring V] in
private theorem stack_nonempty (s : List V) : (stackEncoding e).encode s ≠ [] := by
  cases s <;> simp [stackEncoding, framedListEncoding, framedListEncode]

/-- All actual instruction fetches, framed copies, arithmetic programs, and
cleanups simulate a certified execution, preserving the exact fieldword codec. -/
theorem execute (hlabels : ∀ a, (labels.encode a).length ≤ C)
    {W H : ℕ} {code : Code A} {s out trace : List V}
    (h : Certified e coeff W H code s out trace) :
    ∃ time, time ≤ code.length * instructionBound C e providers W H ∧
      RunsExactly (machine labels C e coeff lits providers).computer.step
        (cfg (.inl 1) (initial (Kernels.machine lits providers))
          (tapes (Kernels.machine lits providers) ((codeEncoding labels).encode code)
            ((stackEncoding e).encode s) [] []))
        (cfg (.inl 1) (initial (Kernels.machine lits providers))
          (tapes (Kernels.machine lits providers) [false] ((stackEncoding e).encode out) [] [])) time := by
  induction h with
  | nil s width height => exact ⟨0, by simp, rfl⟩
  | cons op code s mid out event trace exec width height next ih =>
    obtain ⟨after, ha, run_after⟩ := ih
    obtain ⟨ticks, hticks, kernel⟩ := Kernels.run_exact e coeff lits providers op s mid event exec W
      width next.input_width
    have first := Dynamic.instruction_exact (Kernels.machine lits providers) labels C hlabels op
      ((codeEncoding labels).encode code) ((stackEncoding e).encode s) ((stackEncoding e).encode mid)
      ticks kernel (stack_nonempty e mid)
    have hstart := stack_bits_le e s W width
    have hend := stack_bits_le e mid W next.input_width
    have hheight := next.input_height
    have hl := opEncode_length_le labels C hlabels op
    have hstart' : ((stackEncoding e).encode s).length ≤ (2 * W + 2) * H + 1 :=
      le_trans hstart (Nat.add_le_add_right (Nat.mul_le_mul_left _ height) _)
    have hend' : ((stackEncoding e).encode mid).length ≤ (2 * W + 2) * H + 1 :=
      le_trans hend (Nat.add_le_add_right (Nat.mul_le_mul_left _ hheight) _)
    have htime : ticks + 2 * (opEncode labels op).length +
        2 * ((stackEncoding e).encode s).length + 2 * ((stackEncoding e).encode mid).length + 9 ≤
        instructionBound C e providers W H := by
      dsimp [instructionBound]
      omega
    refine ⟨after + (ticks + 2 * (opEncode labels op).length +
      2 * ((stackEncoding e).encode s).length + 2 * ((stackEncoding e).encode mid).length + 9), ?_, ?_⟩
    · simp only [List.length_cons]
      nlinarith
    · simpa only [codeEncoding, framedListEncoding, framedListEncode, opEncoding,
        List.cons_append] using first.trans run_after

/-- Clean closed entry point: start_exact the empty data stack and remove the
final code terminator, with all worker tapes and finite registers reset. -/
theorem closed_exact (hlabels : ∀ a, (labels.encode a).length ≤ C)
    {W H : ℕ} {code : Code A} {out trace : List V}
    (h : Certified e coeff W H code [] out trace) :
    ∃ time, time ≤ code.length * instructionBound C e providers W H + 3 ∧
      Kernels.Executes (machine labels C e coeff lits providers)
        ((codeEncoding labels).encode code) ((stackEncoding e).encode out) time := by
  obtain ⟨time, ht, hr⟩ := execute labels C e coeff lits providers hlabels h
  have first := runsExactly_one (Dynamic.start_exact (Kernels.machine lits providers) labels C
    ((codeEncoding labels).encode code))
  have last := Dynamic.finish (Kernels.machine lits providers) labels C ((stackEncoding e).encode out)
  have all := (first.trans hr).trans last
  refine ⟨2 + (time + 1), by omega, all⟩

/-- Trace bounds instantiate the runtime theorem only after fixed literal words
and the initial stack have also been bounded. No code-length-only FP claim. -/
theorem closed_of_run (hlabels : ∀ a, (labels.encode a).length ≤ C)
    (W : ℕ) (hc : ∀ a, (e.encode (coeff a)).length ≤ W)
    (hzero : (e.encode 0).length ≤ W) (hone : (e.encode 1).length ≤ W)
    (code : Code A) (out trace : List V)
    (hr : run coeff code [] = some (out, trace))
    (ht : ∀ x ∈ trace, (e.encode x).length ≤ W) :
    ∃ time, time ≤ code.length * instructionBound C e providers W code.length + 3 ∧
      Kernels.Executes (machine labels C e coeff lits providers)
        ((codeEncoding labels).encode code) ((stackEncoding e).encode out) time := by
  apply closed_exact labels C e coeff lits providers hlabels
  exact certified_of_run e coeff W code.length hc hzero hone code [] out trace hr
    (by simp) ht (by simp)

end Holant.OneHot.StackProgram.Machine.Interpreter
