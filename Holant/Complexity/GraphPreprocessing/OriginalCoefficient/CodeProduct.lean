import Holant.OneHot.StackProgram.GraphCodeMachine.Components.Run
import Holant.Complexity.BinaryCompose.Identity

/-! A physical product compiler for already compiled component code chunks.
The payload type is Code, not Tree. The generic frozen component controller
uses its single-chunk route with an actual one-transition identity subroutine;
all frame extraction, result terminator stripping, counting and final reversal
remain executed Boolean-stack operations. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CodeProduct
open Turing Computability Holant.OneHot Holant.OneHot.StackProgram
open Holant.OneHot.StackProgram.GraphCodeMachine
open BinaryCompose StackProtocol
variable {A : Type} (e : Encoding A Bool)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option Elab.async false

def entry (p : Code A) := [false,true]++Holant.Algebraic.frame ((codeEncoding e).encode p)
def entryDecode : List Bool → Option (Code A)
  | false::true::rest => do
      let (word,tail) ← Holant.Algebraic.unframe rest
      if tail=[] then (codeEncoding e).decode word else none
  | _ => none
def entryEncoding : Encoding (Code A) Bool where
  encode := entry e
  decode := entryDecode e
  decode_encode p := by
    have hf (word : List Bool) : Holant.Algebraic.unframe (Holant.Algebraic.frame word)=some (word,[]) := by
      simpa using Holant.Algebraic.unframe_frame_append word []
    simp [entry,entryDecode,hf]
def inputEncoding := framedListEncoding (entryEncoding e)
def product : List (Code A) → Code A
  | [] => [.one]
  | p::ps => mulCode p (product ps)
theorem product_ofFn {n : ℕ} (f : Fin n → Code A) : product (List.ofFn f)=finiteProductCode f := by
  induction n with
  | zero => simp [product,finiteProductCode]
  | succ n ih => rw [List.ofFn_succ,product,finiteProductCode,ih]
theorem product_stream (ps : List (Code A)) :
    product ps=ps.flatten++[.one]++(List.replicate ps.length [.swap,.mul]).flatten := by
  induction ps with
  | nil => simp [product]
  | cons p ps ih =>
    simp [product,mulCode,ih,List.replicate_succ,List.append_assoc]
    have commute (n : ℕ) : (List.replicate n ([.swap,.mul] : Code A)).flatten++[.swap,.mul]=
        [.swap,.mul]++(List.replicate n ([.swap,.mul] : Code A)).flatten := by
      induction n with
      | zero => rfl
      | succ n hn => simpa [List.replicate_succ,List.append_assoc] using congrArg (fun w => ([.swap,.mul] : Code A)++w) hn
    exact commute ps.length
abbrev chunk (p : Code A) := records (opEncoding e) p
abbrev driver := Components.machine identityMachine
  (chunk e [.zero]).reverse (chunk e [.one]).reverse
  (chunk e [.swap,.add]).reverse (chunk e [.swap,.mul]).reverse

def bodyTicks (p : Code A) := 2*((codeEncoding e).encode p).length+(chunk e p).length+8
def entryTicks (p : Code A) := 2*(entry e p).length+3+bodyTicks e p

theorem body_exact (p : Code A) (input output count : List Bool) :
    RunsExactly (driver e).computer.step
      (Components.active identityMachine 3 input (entry e p) output count)
      (Components.active identityMachine 0 input [] ((chunk e p).reverse++output) (true::count)) (bodyTicks e p) := by
  let z := (chunk e [.zero]).reverse
  let o := (chunk e [.one]).reverse
  let a := (chunk e [.swap,.add]).reverse
  let m := (chunk e [.swap,.mul]).reverse
  let word := (codeEncoding e).encode p
  have tag := Components.tag_exact identityMachine z o a m false true input (Holant.Algebraic.frame word) output count
  have call := Components.call_exact identityMachine z o a m 0 input [] output count word (chunk e p) 1 (by
    change (fun c => c.bind identityMachine.computer.step)^[1] (some (initList identityMachine.computer word))=
      some (haltList identityMachine.computer (chunk e p++[false]))
    change identityMachine.computer.step (initList identityMachine.computer word)=
      some (haltList identityMachine.computer (chunk e p++[false]))
    simpa only [word,code_records] using identity_step (chunk e p++[false]))
  have done := Components.finish_descriptor identityMachine z o a m input ((chunk e p).reverse++output) count
  have all := ((runsExactly_one tag).trans (by simpa [word,Components.startPhase,Components.afterPhase,List.append_nil] using call)).trans
    (runsExactly_one done)
  convert all using 1 <;> simp [bodyTicks,entry,word,driver,z,o,a,m]; omega

theorem entry_exact (p : Code A) (suffix output count : List Bool) :
    RunsExactly (driver e).computer.step
      (Components.active identityMachine 0 (true::Holant.Algebraic.frame (entry e p)++suffix) [] output count)
      (Components.active identityMachine 0 suffix [] ((chunk e p).reverse++output) (true::count)) (entryTicks e p) := by
  have first := Components.fetch_exact identityMachine (chunk e [.zero]).reverse (chunk e [.one]).reverse
    (chunk e [.swap,.add]).reverse (chunk e [.swap,.mul]).reverse (entry e p) suffix output count
  convert first.trans (body_exact e p suffix output count) using 1
  simp [entryTicks,Nat.add_comm]
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CodeProduct
