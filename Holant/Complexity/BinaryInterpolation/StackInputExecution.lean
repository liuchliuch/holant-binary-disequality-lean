import Holant.Complexity.BinaryInterpolation.StackInputInterpreter

namespace Holant.Complexity.BinaryInterpolation.StackInputInterpreter
open Turing Computability BinaryCompose StackProtocol
open Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
open Family
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A V : Type} [Fintype A] [DecidableEq A] [CommSemiring V]
variable (labels : Encoding A Bool) (C : ℕ) (e : Encoding V Bool) (coeff : A→V)
variable (lits : Kernels.Literals e coeff) (providers : Operator.Providers e)

private theorem mapped_halt (workers : Op A→BinaryCompose.Machine) (out : List Bool) :
    mapped workers (haltList (Dynamic.machine workers labels C).computer out)=
      haltList (machine workers labels C).computer out := by
  rw [BinaryCompose.Machine.halt_eq,BinaryCompose.Machine.halt_eq]
  rfl

/-- An arbitrary encoded initial value stack is physically loaded, executed,
and cleaned up. Width and height assumptions describe the verified trace only;
they are never read as input data or treated as unit-cost arithmetic. -/
theorem execute (hlabels : ∀a,(labels.encode a).length≤C)
    {W H : ℕ} {code : Code A} {s out trace : List V}
    (h : Certified e coeff W H code s out trace) :
    ∃time,time≤2*((codeEncoding labels).encode code).length+
        2*((stackEncoding e).encode s).length+6+
        code.length*Interpreter.instructionBound C e providers W H ∧
      Kernels.Executes (machine (Kernels.machine lits providers) labels C)
        (Holant.Algebraic.frame ((codeEncoding labels).encode code)++(stackEncoding e).encode s)
        ((stackEncoding e).encode out) time := by
  let workers := Kernels.machine lits providers
  obtain ⟨time,ht,hr⟩ := Interpreter.execute labels C e coeff lits providers hlabels h
  have last := Dynamic.finish workers labels C ((stackEncoding e).encode out)
  have middle := lift_run workers labels C _ _ _ (hr.trans last)
  have first := start workers labels C ((codeEncoding labels).encode code) ((stackEncoding e).encode s)
  have all := first.trans middle
  rw [mapped_halt] at all
  refine ⟨_,?_,all⟩
  omega

end
end Holant.Complexity.BinaryInterpolation.StackInputInterpreter
