import Holant.OneHot.StackProgram.GraphCodeMachine.Join
import Holant.OneHot.StackProgram.GraphCode

/-! Clean linear-time code joining for original graph residual addition and
component multiplication. The exact serialized labels are copied unchanged. -/
namespace Holant.OneHot.StackProgram.GraphCodeMachine.Join
open Turing Computability Holant.Complexity StackProtocol
variable {A : Type} (e : Encoding A Bool)
set_option backward.isDefEq.respectTransparency false

def inputEncoding : Encoding (Code A × Code A) Bool :=
  FixedFieldMachines.pairEncoding (codeEncoding e) (codeEncoding e)

theorem run_codes (suffix p q : Code A) :
    RunsExactly (machine ((codeEncoding e).encode suffix)).computer.step
      (initList (machine ((codeEncoding e).encode suffix)).computer ((inputEncoding e).encode (p, q)))
      (haltList (machine ((codeEncoding e).encode suffix)).computer
        ((codeEncoding e).encode (p ++ q ++ suffix)))
      (2 * ((inputEncoding e).encode (p, q)).length + 6) := by
  have h := run_exact ((codeEncoding e).encode suffix) (records (opEncoding e) p) (records (opEncoding e) q)
  convert h using 1 <;>
    simp [inputEncoding, FixedFieldMachines.pairEncoding, code_records, records_append,
      List.append_assoc, Holant.Algebraic.frame_length] <;> omega

noncomputable def computes (suffix : Code A) :
    BinaryCompose.Computes (inputEncoding e) (codeEncoding e) (fun p => p.1 ++ p.2 ++ suffix) where
  machine := machine ((codeEncoding e).encode suffix)
  time := 2 * Polynomial.X + 6
  outputs p := {
    steps := 2 * ((inputEncoding e).encode p).length + 6
    evals_in_steps := run_codes e suffix p.1 p.2
    steps_le_m := by simp }

noncomputable def outputBound (suffix : Code A) :
    PolynomialOutputBound (inputEncoding e) (codeEncoding e) (fun p => p.1 ++ p.2 ++ suffix) where
  bound := Polynomial.X + Polynomial.C ((codeEncoding e).encode suffix).length
  length_le p := by
    simp [inputEncoding, FixedFieldMachines.pairEncoding, code_records, records_append,
      List.append_assoc, Holant.Algebraic.frame_length]
    omega

noncomputable def addComputes :
    BinaryCompose.Computes (inputEncoding e) (codeEncoding e) (fun p => addCode p.1 p.2) :=
  computes e [.swap, .add]

noncomputable def mulComputes :
    BinaryCompose.Computes (inputEncoding e) (codeEncoding e) (fun p => mulCode p.1 p.2) :=
  computes e [.swap, .mul]

noncomputable def constantComputes {X : Type} (input : Encoding X Bool) (code : Code A) :
    BinaryCompose.Computes input (codeEncoding e) (fun _ => code) :=
  FixedFieldMachines.constantComputes input (codeEncoding e) code

end Holant.OneHot.StackProgram.GraphCodeMachine.Join
