import Holant.Proofs.Tractability.ProductMachine.ExpressionEncoding
import Holant.Proofs.Tractability.ProductMachine.Rewrite
import Holant.Complexity.FixedFieldMachines.Reverse


namespace Holant.LocalDrafts.Tractability.ProductMachine.Bytecode

open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open Holant.OneHot.StackProgram
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable {A B : Type}

def chunk (labels : Encoding B Bool) (e : Expr B) : List Bool :=
  entries (opEncoding labels) e.code

abbrev Emits (ea : Encoding A Bool) (labels : Encoding B Bool) (f : A → Expr B) :=
  Computes ea Frame.wordEncoding (fun a => chunk labels (f a))

noncomputable def reverseWord : Computes Frame.wordEncoding Frame.wordEncoding List.reverse :=
  recode (reverseComputes Frame.wordEncoding) id (fun _ => rfl) (fun _ => rfl)

noncomputable def constant (ea : Encoding A Bool) (labels : Encoding B Bool) (e : Expr B) :
    Emits ea labels (fun _ => e) := constantComputes ea Frame.wordEncoding (chunk labels e)

noncomputable def literal (labels : Encoding B Bool) : Emits labels labels Expr.literal := by
  let opcode := joinComputes (constantComputes labels Frame.wordEncoding [false, false, false])
    (encodeComputes labels)
  let framed := opcode.andThen frameComputes
  exact congrComputes (joinComputes (constantComputes labels Frame.wordEncoding [true]) framed)
    (fun _ => by simp [chunk, Expr.code, entries, entry, opEncoding, opEncode])

noncomputable def binary (ea : Encoding A Bool) (labels : Encoding B Bool)
    (mul : Bool) (f g : A → Expr B) (wf : Emits ea labels f) (wg : Emits ea labels g) :
    Emits ea labels (fun a => if mul then .mul (f a) (g a) else .add (f a) (g a)) :=
  congrComputes (joinComputes (joinComputes wg wf)
    (constantComputes ea Frame.wordEncoding
      (entries (opEncoding labels) [if mul then .mul else .add])))
    (fun a => by cases mul <;> simp [chunk, Expr.code, entries, List.append_assoc])

noncomputable def finish {ea : Encoding A Bool} {labels : Encoding B Bool} {f : A → Expr B}
    (w : Emits ea labels f) : Computes ea (Expr.encoding labels) f :=
  recode (joinComputes w (constantComputes ea Frame.wordEncoding [false])) id (fun _ => rfl)
    (fun a => by
      simpa only [chunk, Expr.encoding, codeEncoding, framedListEncoding, framedListEncode, Frame.wordEncoding, id_eq, List.append_nil] using
        entries_append_encode (opEncoding labels) (f a).code [])

noncomputable def unfinish (labels : Encoding B Bool) : Emits (Expr.encoding labels) labels id :=
  recode (entriesComputes (opEncoding labels)) Expr.code (fun _ => rfl) (fun _ => rfl)

noncomputable def flatMap (ea : Encoding A Bool) (f : A → List Bool)
    (w : Computes ea Frame.wordEncoding f) :
    Computes (framedListEncoding ea) Frame.wordEncoding (fun xs => xs.flatMap f) := by
  let prepare : Computes (framedListEncoding ea)
      (ContextFlatMap.inputEncoding Frame.wordEncoding (fun _ => ea))
      (fun xs => (⟨[], xs⟩ : Σ _ : List Bool, List A)) :=
    recode (pairComputes (constantComputes (framedListEncoding ea) Frame.wordEncoding [])
      (identityComputes (framedListEncoding ea))) id (fun _ => rfl) (fun _ => rfl)
  let worker : Computes (sigmaEncoding Frame.wordEncoding (fun _ => ea)) Frame.wordEncoding
      (fun x => f x.2) :=
    recode ((Wiring.secondComputes Frame.wordEncoding ea).andThen w)
      (fun x => (x.1, x.2)) (fun _ => rfl) (fun _ => rfl)
  exact prepare.andThen (ContextFlatMap.computes Frame.wordEncoding (fun _ => ea) _ worker)

theorem product_chunk (labels : Encoding B Bool) (xs : List (Expr B)) :
    chunk labels (Expr.product xs) = chunk labels .one ++
      xs.reverse.flatMap (fun e => chunk labels e ++ entries (opEncoding labels) [.mul]) := by
  induction xs with
  | nil => simp [Expr.product, chunk, Expr.code, entries]
  | cons e es ih =>
    simp only [Expr.product, chunk, Expr.code, entries, List.flatMap_append] at *
    rw [List.reverse_cons, List.flatMap_append]
    simpa [List.append_assoc] using congrArg
      (fun tail => tail ++ e.code.flatMap (entry (opEncoding labels)) ++
        [Op.mul].flatMap (entry (opEncoding labels))) ih

/-- The unbounded factor stream is processed by ContextFlatMap, not a fixed
number of compositions depending on the runtime list. -/
noncomputable def product (ea : Encoding A Bool) (labels : Encoding B Bool)
    (f : A → Expr B) (w : Emits ea labels f) :
    Emits (framedListEncoding ea) labels (fun xs => Expr.product (xs.map f)) := by
  let each := joinComputes w (constantComputes ea Frame.wordEncoding
    (entries (opEncoding labels) [.mul]))
  let body := (flatMap ea _ (each.andThen reverseWord)).andThen reverseWord
  refine congrComputes (joinComputes (constant (framedListEncoding ea) labels .one) body) ?_
  intro xs
  simp only [List.reverse_flatMap, List.reverse_reverse, Function.comp_def]
  rw [product_chunk]
  simp only [←List.map_reverse,List.flatMap_map,Function.comp_def]

end Holant.LocalDrafts.Tractability.ProductMachine.Bytecode
