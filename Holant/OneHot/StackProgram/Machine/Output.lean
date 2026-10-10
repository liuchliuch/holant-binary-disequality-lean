import Holant.OneHot.StackProgram.Machine.Interpreter
import Holant.OneHot.StackProgram.Machine.Unbox
import Holant.Complexity.BinaryCompose.Composition

/-! The closed-program interface emits the original raw value codec, after
actual singleton extraction and clean bitwise transfer. -/
namespace Holant.OneHot.StackProgram.Machine.Interpreter
open Turing Computability Holant.Complexity
variable {A V : Type} [Fintype A] [DecidableEq A] [CommSemiring V]
variable (labels : Encoding A Bool) (C : ℕ) (e : Encoding V Bool) (coeff : A → V)
variable (lits : Kernels.Literals e coeff) (providers : Operator.Providers e)

abbrev valueMachine : BinaryCompose.Machine :=
  (machine labels C e coeff lits providers).compose Unbox.machine

/-- Exact fieldword output; every transfer, list check and final halt is charged. -/
theorem value_exact (hlabels : ∀ a, (labels.encode a).length ≤ C)
    {W H : ℕ} {code : Code A} {value : V} {trace : List V}
    (h : Certified e coeff W H code [] [value] trace) :
    ∃ time, time ≤ code.length * instructionBound C e providers W H + 6 * W + 16 ∧
      Kernels.Executes (valueMachine labels C e coeff lits providers)
        ((codeEncoding labels).encode code) (e.encode value) time := by
  obtain ⟨time, ht, hr⟩ := closed_exact labels C e coeff lits providers hlabels h
  have unbox := Unbox.encoded e value
  have all := BinaryCompose.Machine.compose_run (machine labels C e coeff lits providers) Unbox.machine
    ((codeEncoding labels).encode code) ((stackEncoding e).encode [value]) (e.encode value)
    time (2 * (e.encode value).length + 5) hr unbox
  have hw := h.output_width value (by simp)
  have hm : ((stackEncoding e).encode [value]).length = 2 * (e.encode value).length + 3 := by
    simp [stackEncoding, framedListEncoding, framedListEncode, Holant.Algebraic.frame_length]
  refine ⟨_, ?_, all⟩
  rw [hm]
  omega

/-- Direct operational consequence of a compiled-program run with exact trace. -/
theorem value_of_run (hlabels : ∀ a, (labels.encode a).length ≤ C)
    (W : ℕ) (hc : ∀ a, (e.encode (coeff a)).length ≤ W)
    (hzero : (e.encode 0).length ≤ W) (hone : (e.encode 1).length ≤ W)
    (code : Code A) (value : V) (trace : List V)
    (hr : run coeff code [] = some ([value], trace))
    (ht : ∀ x ∈ trace, (e.encode x).length ≤ W) :
    ∃ time, time ≤ code.length * instructionBound C e providers W code.length + 6 * W + 16 ∧
      Kernels.Executes (valueMachine labels C e coeff lits providers)
        ((codeEncoding labels).encode code) (e.encode value) time := by
  apply value_exact labels C e coeff lits providers hlabels
  exact certified_of_run e coeff W code.length hc hzero hone code [] [value] trace hr
    (by simp) ht (by simp)

end Holant.OneHot.StackProgram.Machine.Interpreter
