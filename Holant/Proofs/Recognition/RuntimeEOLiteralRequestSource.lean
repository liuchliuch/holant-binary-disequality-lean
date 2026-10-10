import Holant.Proofs.Recognition.RuntimeEOLiteralRequest
import Holant.Proofs.Recognition.RuntimeEOLiteralSystems
import Holant.Proofs.Algorithms.TransformRecognition.ProductAllocationSource
import Holant.Proofs.Recognition.UniformKPolynomial

/-! Source normalization of the actual runtime literal A/P requests. The
pairing is reconstructed from generated accepted metadata. Width, free scalar
and unary slots, original RootCode bindings and the entire combined body match
the physical compiler exactly. Root search terminates only on this represented
source domain, and its returned candidate remains the serialized witness. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOLiteralRequestSource
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm (Parameter)
open UniformTensorWitnessBranch (Metadata)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def parameters (product : Bool) (count : ℕ) : ℕ := if product then 1+2*count else 1

def parameterIndex {count : ℕ} : Parameter count → Fin (1+2*count)
  | none => 0
  | some (j,b) => ⟨1+2*j.val+(if b then 1 else 0),by cases b <;> simp only [Bool.false_eq_true,ite_true,ite_false] <;> omega⟩

theorem parameterIndex_injective {count : ℕ} : Function.Injective (parameterIndex (count:=count)) := by
  intro a b h
  have he := congrArg Fin.val h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => rcases b with ⟨j,b⟩; cases b <;> simp only [parameterIndex,Fin.val_mk,Fin.val_zero,Bool.false_eq_true,ite_true,ite_false] at he <;> omega
  | some a =>
    rcases a with ⟨i,a⟩
    cases b with
    | none => cases a <;> simp only [parameterIndex,Fin.val_mk,Fin.val_zero,Bool.false_eq_true,ite_true,ite_false] at he <;> omega
    | some b =>
      rcases b with ⟨j,b⟩
      cases a <;> cases b <;> simp only [parameterIndex,Fin.val_mk,Bool.false_eq_true,ite_true,ite_false] at he
      all_goals first | omega | (have hij : i=j := Fin.ext (by omega); subst j; rfl)

variable {s : ℕ} (arity : Fin s → ℕ)
abbrev Entries := OriginalAffineSystem.Entries arity
abbrev Width (product : Bool) (count : ℕ) := OriginalVariableLayout.Width (Entries arity) (parameters product count)
abbrev Extra (product : Bool) (count : ℕ) := OriginalVariableLayout.Extra (Entries arity) (parameters product count)
def imaginary (product : Bool) (count : ℕ) : Fin (Width arity product count) :=
  OriginalVariableLayout.special (Entries arity) (parameters product count) 0
def sqrt (product : Bool) (count : ℕ) : Fin (Width arity product count) :=
  OriginalVariableLayout.special (Entries arity) (parameters product count) 1
def address (product : Bool) (count : ℕ) (i : Fin s) (x : Fin (arity i) → Bool) : Fin (Width arity product count) :=
  OriginalTensorRows.entryVariable arity (parameters product count) (.inl i) x
def bindings (product : Bool) (count : ℕ) : Fin (Entries arity+2) → Fin (Width arity product count) :=
  OriginalVariableLayout.binding (Entries arity) (parameters product count)
def scale (count : ℕ) : Fin (Width arity false count) := OriginalVariableLayout.parameter (Entries arity) 1 0
def parameter {count : ℕ} (t : Parameter count) : Fin (Width arity true count) :=
  OriginalVariableLayout.parameter (Entries arity) (1+2*count) (parameterIndex t)

variable (input : OriginalFamilyInput.Input arity) (i : Fin s) (complete : Bool) (k : ℕ) (m : Metadata)

def encode : RuntimeEOLiteralRequest.Input := ((OriginalFamilyPackingSource.fromSource arity input false,i.val,complete,k),m)

theorem source_exact : RuntimeEOLiteralRequest.source (encode arity input i complete k m)=
    OriginalFamilyPackingSource.fromSource arity input false := rfl

theorem width_exact (product : Bool) : RuntimeEOLiteralRequest.width product (encode arity input i complete k m)=
    Width arity product m.1.length := OriginalAllocatedPackingMachine.width_source arity input false _

theorem arity_exact : RuntimeEOLiteralRequest.arity (encode arity input i complete k m)=arity i := by
  change (((List.finRange s).map (fun j => (arity j,(SparseTransform.allWords (arity j)).map (input j)))).getD i.val (0,[])).1=arity i
  rw [←List.ofFn_eq_map,PositiveCertificateMachine.getD_ofFn]

theorem imaginary_exact (product : Bool) : RuntimeEOLiteralRequest.imaginary product (encode arity input i complete k m)=
    (imaginary arity product m.1.length).val := by
  change 5+parameters product m.1.length+(OriginalFamilyPackingMachine.original (OriginalFamilyPackingSource.fromSource arity input false)).length=_
  rw [OriginalFamilyPackingSource.original_length]
  simp only [imaginary,Entries,OriginalVariableLayout.special,Fin.val_natAdd]
  omega

theorem base_exact (product : Bool) : RuntimeEOLiteralRequest.base product (encode arity input i complete k m)=
    RuntimeEOLiteralRows.sourceBase (imaginary arity product m.1.length) (sqrt arity product m.1.length)
      (address arity product m.1.length i) complete k m := by
  unfold RuntimeEOLiteralRequest.base
  rw [width_exact,imaginary_exact,arity_exact]
  have ht := ProductAllocationSource.entry_table_source arity input (parameters product m.1.length) (.inl i)
  change OriginalAddressTablesMachine.table (OriginalCatalogueSource.family arity input,parameters product m.1.length,i.val)=_ at ht
  change ((Width arity product m.1.length,(imaginary arity product m.1.length).val,
    (imaginary arity product m.1.length).val+1),(arity i,complete,k),m,
    OriginalAddressTablesMachine.table (OriginalCatalogueSource.family arity input,parameters product m.1.length,i.val))=_
  rw [ht]
  unfold RuntimeEOLiteralRows.sourceBase
  congr 2

theorem unary_exact : RuntimeEOLiteralRequest.unary (encode arity input i complete k m)=
    List.ofFn (fun j : Fin m.1.length => ((parameter arity (some (j,false))).val,(parameter arity (some (j,true))).val)) := by
  unfold RuntimeEOLiteralRequest.unary
  change (List.range m.1.length).map _=_
  rw [RuntimeTensorRowsSoundness.map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext j
  simp only [parameter,parameterIndex,OriginalVariableLayout.parameter,Fin.val_natAdd,Fin.val_castAdd,Bool.false_eq_true,ite_false,ite_true]
  congr 1 <;> omega

variable (hg : m∈RuntimeTensorCatalogue.catalogue (RuntimeEOView.arity (arity i,complete,k)))
    (hv : RuntimeEOPairings.valid (RuntimeEOView.arity (arity i,complete,k)) m=true)
local notation "p" => RuntimeEOPairings.pairing m hg hv

def typedBody (product : Bool) : List (Sparse.Poly (Width arity product m.1.length) 1) :=
  match product with
  | false => SparseTransform.guard RationalCompiler.data (Extra arity false m.1.length)::
      FiniteSystemDisjunction.combine (RuntimeEOLiteralSystems.affineBranches
        (imaginary arity false m.1.length) (sqrt arity false m.1.length) (address arity false m.1.length i)
        complete k m hg hv (scale arity m.1.length))
  | true => SparseTransform.guard RationalCompiler.data (Extra arity true m.1.length)::
      FiniteSystemDisjunction.combine (RuntimeEOLiteralSystems.productBranches
        (imaginary arity true m.1.length) (sqrt arity true m.1.length) (address arity true m.1.length i)
        complete k m hg hv (parameter arity))

theorem body_wire (product : Bool) : RuntimeEOLiteralRequest.body product (encode arity input i complete k m)=
    RationalInputMachine.bodyWire (typedBody arity i complete k m hg hv product) := by
  unfold RuntimeEOLiteralRequest.body
  rw [width_exact,RationalMatrixMachine.guard_wire]
  cases product
  · simp only [Bool.false_eq_true,ite_false,RuntimeEOLiteralRequest.affineBranches]
    rw [base_exact]
    change RationalInputMachine.rowWire _::RationalDisjunctionMachine.combine _
      ((RawAffineEnumeration.templates (p).count).map (fun c => RuntimeEOLiteralRows.affineRows
        (RuntimeEOLiteralRows.sourceBase _ _ _ complete k m,(scale arity m.1.length).val,c)))=_
    rw [RuntimeEOLiteralSystems.affineBranches_wire _ _ _ complete k m hg hv,RationalDisjunctionMachine.combine_wire]
    rfl
  · simp only [ite_true,RuntimeEOLiteralRequest.productBranches]
    rw [base_exact,unary_exact]
    change RationalInputMachine.rowWire _::RationalDisjunctionMachine.combine _
      ((RawProductEnumeration.templates (p).count).map (fun c => RuntimeEOLiteralRows.productRows
        (RuntimeEOLiteralRows.sourceBase _ _ _ complete k m,c,(parameter arity (none : Parameter (p).count)).val,
          List.ofFn (fun j => ((parameter arity (some (j,false))).val,(parameter arity (some (j,true))).val)))))=_
    erw [RuntimeEOLiteralSystems.productBranches_wire (imaginary arity true m.1.length)
      (sqrt arity true m.1.length) (address arity true m.1.length i) complete k m hg hv
      (parameter arity (count:=(p).count)),RationalDisjunctionMachine.combine_wire]
    rfl

theorem request_exact (product : Bool) : RuntimeEOLiteralRequest.request product (encode arity input i complete k m)=
    RationalInputMachine.fromSource (UniformKPolynomial.descriptors arity input)
      (typedBody arity i complete k m hg hv product) (bindings arity product m.1.length) := by
  unfold RuntimeEOLiteralRequest.request RationalInputMachine.fromSource
  congr 1
  · exact width_exact arity input i complete k m product
  · exact OriginalFamilyPackingSource.roots_exact arity input false
  · exact body_wire arity input i complete k m hg hv product
  · exact OriginalAllocatedPackingMachine.addresses_source arity input false _

theorem guard_mem (product : Bool) : SparseTransform.guard RationalCompiler.data (Extra arity product m.1.length) ∈
    typedBody arity i complete k m hg hv product := by cases product <;> exact List.mem_cons_self ..

variable (G : (j : Fin s) → Signature AlgebraicComplex (arity j))
    (represented : ∀j x,(input j x).Represents (G j x : ℂ))

def output (product : Bool) : Option WitnessOutput.Output :=
  WitnessOutput.originalOutput (UniformKPolynomial.descriptors arity input)
    (UniformKPolynomial.valid arity G input represented)
    (typedBody arity i complete k m hg hv product) (bindings arity product m.1.length)

theorem source_outputs (product : Bool) : ∃ticks,Nonempty (TM2OutputsInTime (RuntimeEOLiteralRequest.machine product).computer
    (RuntimeEOLiteralRequest.encoding.encode (encode arity input i complete k m))
    (some (WitnessOutput.resultEncoding.encode (output arity input i complete k m hg hv G represented product))) ticks) := by
  obtain ⟨ticks,⟨right⟩⟩ := WitnessOutput.original_outputs
    (UniformKPolynomial.descriptors arity input) (UniformKPolynomial.valid arity G input represented)
    (typedBody arity i complete k m hg hv product) (bindings arity product m.1.length)
  have left := (RuntimeEOLiteralRequest.executes product).outputs (encode arity input i complete k m)
  rw [request_exact arity input i complete k m hg hv product] at left
  exact ⟨_,⟨Machine.compose_correct _ _ _ _ _ _ _ left right⟩⟩

theorem output_isSome_iff (product : Bool) :
    (output arity input i complete k m hg hv G represented product).isSome=true ↔
      ∃z : Fin (Width arity product m.1.length) → ℂ,
        (∀j,z (bindings arity product m.1.length j)=(UniformKPolynomial.values arity G j : ℂ)) ∧
        ∀e∈typedBody arity i complete k m hg hv product,
          SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z e=0 := by
  rw [output,WitnessOutput.originalOutput_correct _ _ (UniformKPolynomial.values arity G)
    (UniformKPolynomial.descriptors_represents arity G input represented) _ _ (guard_mem arity i complete k m hg hv product)]
  exact exists_congr fun z => RationalInputSystem.system_zero_iff
    (fun j => (UniformKPolynomial.values arity G j : ℂ))
    (typedBody arity i complete k m hg hv product) (bindings arity product m.1.length) z

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOLiteralRequestSource
