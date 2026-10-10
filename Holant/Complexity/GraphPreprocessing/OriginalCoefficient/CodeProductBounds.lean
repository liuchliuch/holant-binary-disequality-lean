import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CodeProductRun
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CodeProduct
open Turing Computability Holant.OneHot Holant.OneHot.StackProgram
open BinaryCompose StackProtocol FixedFieldMachines
open Holant.OneHot.StackProgram.GraphCodeMachine
variable {A : Type} (e : Encoding A Bool)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option Elab.async false

def payload (ps : List (Code A)) := (ps.map (fun p => (chunk e p).length)).sum
theorem entry_length (p : Code A) : (entry e p).length=2*(chunk e p).length+5 := by
  simp [entry,code_records,Holant.Algebraic.frame_length,chunk]
  omega
theorem entry_ticks (p : Code A) : entryTicks e p=7*(chunk e p).length+23 := by
  simp only [entryTicks,entry_length,bodyTicks,code_records,chunk,List.length_append,List.length_singleton]
  omega
theorem input_length (ps : List (Code A)) : ((inputEncoding e).encode ps).length=4*payload e ps+12*ps.length+1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change (true::(Holant.Algebraic.frame (entry e p)++(inputEncoding e).encode ps)).length=4*payload e (p::ps)+12*(ps.length+1)+1
    simp only [List.length_cons,List.length_append,Holant.Algebraic.frame_length]
    rw [entry_length,ih]
    simp only [payload,List.map_cons,List.sum_cons]
    omega
theorem list_ticks (ps : List (Code A)) : listTicks e ps=7*payload e ps+23*ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change entryTicks e p+listTicks e ps=7*payload e (p::ps)+23*(ps.length+1)
    rw [entry_ticks,ih]
    simp only [payload,List.map_cons,List.sum_cons]
    omega
theorem chunk_flatten_length (ps : List (Code A)) : (chunk e ps.flatten).length=payload e ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatten_cons,chunk,records_append,List.length_append,payload,List.map_cons,List.sum_cons]
    exact congrArg (fun n => (chunk e p).length+n) ih

theorem output_length (ps : List (Code A)) :
    ((codeEncoding e).encode (product ps)).length=
      payload e ps+(chunk e [.one]).length+ps.length*(chunk e [.swap,.mul]).length+1 := by
  have h := congrArg List.length (output_eq e ps)
  simpa [List.length_flatten,chunk_flatten_length,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.symm

noncomputable def timePolynomial : Polynomial ℕ :=
  Polynomial.C ((chunk e [.swap,.mul]).length+3)*Polynomial.X+Polynomial.C ((chunk e [.one]).length+7)
theorem time_bound (ps : List (Code A)) :
    listTicks e ps+ps.length+((codeEncoding e).encode (product ps)).length+6≤
      (timePolynomial e).eval ((inputEncoding e).encode ps).length := by
  rw [list_ticks,output_length]
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,input_length]
  nlinarith [Nat.zero_le (payload e ps*(chunk e [.swap,.mul]).length)]
noncomputable def computes : Computes (inputEncoding e) (codeEncoding e) product where
  machine := driver e
  time := timePolynomial e
  outputs ps := {
    steps := listTicks e ps+ps.length+((codeEncoding e).encode (product ps)).length+6
    evals_in_steps := run_exact e ps
    steps_le_m := time_bound e ps }
theorem inFP : InFP (inputEncoding e) (codeEncoding e) product := (computes e).inFP
noncomputable def primitivePolynomial : Polynomial ℕ := timePolynomial e*Polynomial.C (driver e).primitiveBudget
theorem primitive_bound (ps : List (Code A)) :
    primitiveCost (driver e) ((computes e).outputs ps).steps
      (some (initList (driver e).computer ((inputEncoding e).encode ps)))≤
      (primitivePolynomial e).eval ((inputEncoding e).encode ps).length := by
  have h := Nat.mul_le_mul_right (driver e).primitiveBudget ((computes e).outputs ps).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C,computes] using le_trans (primitiveCost_le _ _ _) h
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CodeProduct
