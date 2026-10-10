import Holant.Proofs.Recognition.RuntimeTensorRequestSource
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeTensorRequest
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeTensorBasisSemantics
import Holant.Proofs.Algorithms.TransformRecognition.ProductAllocationSource

/-!
# Promised-domain source normalization for the runtime tensor request

The semantic family layout indexes correctness only. The physical request is
built from its runtime raw family, selected label, flags and candidate. A zero
branch needs no manufactured partition; only a nonzero candidate must belong
to the actual runtime catalogue. Invalid nonzero metadata becomes a literal
constant-one contradiction. No halting statement for malformed RootCodes is
assumed by this normalization layer.
-/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open UniformTensorWitnessBranch (Metadata)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {s : ℕ} (arity : Fin s → ℕ)
abbrev Entries := OriginalAffineSystem.Entries arity
abbrev Extra := OriginalVariableLayout.Extra (Entries arity) 1
abbrev Width := OriginalVariableLayout.Width (Entries arity) 1

def address (i : Fin s) (x : Fin (arity i) → Bool) : Fin (Width arity) :=
  OriginalTensorRows.entryVariable arity 1 (.inl i) x

def imaginary : Fin (Width arity) := OriginalVariableLayout.special (Entries arity) 1 0
def sqrt : Fin (Width arity) := OriginalVariableLayout.special (Entries arity) 1 1
def bindings : Fin (Entries arity+2) → Fin (Width arity) := OriginalVariableLayout.binding (Entries arity) 1

variable (input : OriginalFamilyInput.Input arity) (native opposite : Bool) (i : Fin s)
  (c : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.Candidate)

def encode : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.Input :=
  ((OriginalFamilyPackingSource.fromSource arity input false,(native,opposite),i.val),c)

def Legal : Prop := c.1=true ∨ c.2 ∈ RuntimeTensorCatalogue.catalogue (arity i)

theorem source_exact : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.source (encode arity input native opposite i c)=
    OriginalFamilyPackingSource.fromSource arity input false := rfl

theorem width_exact : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.width (encode arity input native opposite i c)=Width arity :=
  OriginalAllocatedPackingMachine.width_source arity input false 1

theorem arity_exact : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.arity (encode arity input native opposite i c)=arity i := by
  change (((List.finRange s).map (fun k => (arity k,(SparseTransform.allWords (arity k)).map (input k)))).getD
    i.val (0,[])).1=arity i
  rw [←List.ofFn_eq_map,PositiveCertificateMachine.getD_ofFn]

theorem imaginary_exact : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.imaginary (encode arity input native opposite i c)=
    (imaginary arity).val := by
  change 6+(OriginalFamilyPackingMachine.original (OriginalFamilyPackingSource.fromSource arity input false)).length = _
  rw [OriginalFamilyPackingSource.original_length]
  simp only [imaginary,Entries,OriginalVariableLayout.special,Fin.val_natAdd]
  omega

theorem basisInput_exact : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.basisInput (encode arity input native opposite i c)=
    ((native,opposite),(Width arity,(imaginary arity).val,(sqrt arity).val)) := by
  unfold _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.basisInput
  rw [width_exact,imaginary_exact]
  change ((native,opposite),(Width arity,(imaginary arity).val,(imaginary arity).val+1)) = _
  simp only [imaginary,sqrt,OriginalVariableLayout.special,Fin.val_natAdd]
  congr 2

theorem rowInput_exact : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.rowInput (encode arity input native opposite i c)=
    RuntimeTensorRowsSoundness.request c.2 (address arity i) := by
  unfold _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.rowInput
  rw [width_exact,arity_exact]
  change (Width arity,arity i,c.2,OriginalAddressTablesMachine.table
    (OriginalCatalogueSource.family arity input,1,i.val)) = _
  have ht := ProductAllocationSource.entry_table_source arity input 1 (.inl i)
  change OriginalAddressTablesMachine.table (OriginalCatalogueSource.family arity input,1,i.val)=_ at ht
  rw [ht]
  rfl

theorem valid_exact : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.candidateValid (encode arity input native opposite i c)=
    RuntimeTensorValidation.valid (native,arity i,c.2) := by
  unfold _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.candidateValid
  rw [arity_exact]
  rfl

def typedBasis : List (Sparse.Poly (Width arity) 1) :=
  _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasis.typedRows native opposite (imaginary arity) (sqrt arity)

variable (legal : Legal arity i c)

def typedExtra : List (Sparse.Poly (Width arity) 1) :=
  if hz : c.1=true then (SparseTransform.allWords (arity i)).map
    (RuntimeTensorRowsSoundness.entries (address arity i))
  else if hv : RuntimeTensorValidation.valid (native,arity i,c.2)=true then
    RuntimeTensorRowsSoundness.typedRows c.2 (legal.resolve_left hz) native hv (address arity i)
  else [Sparse.one RationalCompiler.data]

def typedBody : List (Sparse.Poly (Width arity) 1) :=
  typedBasis arity native opposite ++ typedExtra arity native i c legal

theorem extraRows_wire : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.extraRows (encode arity input native opposite i c)=
    RationalInputMachine.bodyWire (typedExtra arity native i c legal) := by
  unfold _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.extraRows
  rw [rowInput_exact,valid_exact,width_exact]
  change (if c.1 then RuntimeTensorRows.zeroRows (RuntimeTensorRowsSoundness.request c.2 (address arity i))
    else if RuntimeTensorValidation.valid (native,arity i,c.2) then
      RuntimeTensorRows.rows native (RuntimeTensorRowsSoundness.request c.2 (address arity i))
    else [RationalSparseMachine.one (Width arity)]) = _
  unfold typedExtra
  by_cases hz : c.1=true
  · simp only [hz,ite_true,dif_pos,RuntimeTensorRowsSoundness.zeroRows_wire]
  · simp only [hz,Bool.false_eq_true,ite_false,dif_neg]
    by_cases hv : RuntimeTensorValidation.valid (native,arity i,c.2)=true
    · simp only [hv,ite_true,dif_pos]
      exact RuntimeTensorRowsSoundness.rows_wire c.2 (legal.resolve_left hz) native hv (address arity i)
    · simp only [hv,Bool.false_eq_true,ite_false,dite_false,RationalInputMachine.bodyWire,List.map_cons,List.map_nil,
        RationalSparseMachine.one_wire]

theorem body_wire : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.body (encode arity input native opposite i c)=
    RationalInputMachine.bodyWire (typedBody arity native opposite i c legal) := by
  unfold _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.body
  rw [basisInput_exact,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasis.rows_wire,extraRows_wire arity input native opposite i c legal]
  simp only [typedBody,typedBasis,RationalInputMachine.bodyWire,List.map_append]

theorem request_exact : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.request (encode arity input native opposite i c)=
    RationalInputMachine.fromSource (UniformKPolynomial.descriptors arity input)
      (typedBody arity native opposite i c legal) (bindings arity) := by
  unfold _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.request RationalInputMachine.fromSource
  congr 1
  · exact width_exact arity input native opposite i c
  · exact OriginalFamilyPackingSource.roots_exact arity input false
  · exact body_wire arity input native opposite i c legal
  · exact OriginalAllocatedPackingMachine.addresses_source arity input false 1

theorem guard_mem : SparseTransform.guard RationalCompiler.data (Extra arity) ∈
    typedBody arity native opposite i c legal := by
  simp [typedBody,typedBasis,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasis.typedRows]

variable (G : (j : Fin s) → Signature AlgebraicComplex (arity j))
  (represented : ∀j x,(input j x).Represents (G j x : ℂ))

/-- The actual witness output of the one fixed RootCode search programme. -/
def output : Option WitnessOutput.Output :=
  WitnessOutput.originalOutput (UniformKPolynomial.descriptors arity input)
    (UniformKPolynomial.valid arity G input represented)
    (typedBody arity native opposite i c legal) (bindings arity)

/-- Termination is restricted to genuine original-root representations and
the runtime generated-candidate domain. No total Executes wrapper is used. -/
theorem source_outputs : ∃ticks,Nonempty (TM2OutputsInTime _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.machine.computer
    (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.encoding.encode (encode arity input native opposite i c))
    (some (WitnessOutput.resultEncoding.encode (output arity input native opposite i c legal G represented))) ticks) := by
  obtain ⟨ticks,⟨right⟩⟩ := WitnessOutput.original_outputs
    (UniformKPolynomial.descriptors arity input) (UniformKPolynomial.valid arity G input represented)
    (typedBody arity native opposite i c legal) (bindings arity)
  have left := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.executes.outputs (encode arity input native opposite i c)
  rw [request_exact arity input native opposite i c legal] at left
  exact ⟨_,⟨Machine.compose_correct _ _ _ _ _ _ _ left right⟩⟩

/-- Original bindings and sparse body constraints characterize the answer of
that same emitted witness search. -/
theorem output_isSome_iff :
    (output arity input native opposite i c legal G represented).isSome=true ↔
      ∃z : Fin (Width arity) → ℂ,
        (∀j,z (bindings arity j)=(UniformKPolynomial.values arity G j : ℂ)) ∧
        ∀p∈typedBody arity native opposite i c legal,
          SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0 := by
  rw [output,WitnessOutput.originalOutput_correct _ _ (UniformKPolynomial.values arity G)
    (UniformKPolynomial.descriptors_represents arity G input represented) _ _
      (guard_mem arity native opposite i c legal)]
  apply exists_congr
  intro z
  exact RationalInputSystem.system_zero_iff (fun j => (UniformKPolynomial.values arity G j : ℂ))
    (typedBody arity native opposite i c legal) (bindings arity) z

section Meaning

def Bound (z : Fin (Width arity) → ℂ) : Prop :=
  ∀j,z (bindings arity j)=(UniformKPolynomial.values arity G j : ℂ)

def transformed : Signature AlgebraicComplex (arity i) :=
  (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.basis native opposite).symm.action (G i)

theorem values_coe : (fun j => (UniformKPolynomial.values arity G j : ℂ)) =
    OriginalVariableLayout.boundValues (fun j => (OriginalFamilyInput.values arity G false j : ℂ)) := by
  funext j
  induction j using Fin.addCases with
  | left j => simp [UniformKPolynomial.values,OriginalVariableLayout.boundValues]
  | right j => fin_cases j <;> simp [UniformKPolynomial.values,OriginalVariableLayout.boundValues,StandardRootCodes.values]

theorem bound_old (z : Fin (Width arity) → ℂ) (hb : Bound arity G z) :
    OriginalTensorRows.Bound arity 1 (OriginalFamilyInput.values arity G false) z := by
  intro j
  exact (hb j).trans (congrFun (values_coe arity G) j)

theorem bound_imaginary (z : Fin (Width arity) → ℂ) (hb : Bound arity G z) :
    z (imaginary arity)=(imaginaryUnit : ℂ) :=
  OriginalVariableLayout.binding_imaginary z _ (bound_old arity G z hb)

theorem bound_sqrt (z : Fin (Width arity) → ℂ) (hb : Bound arity G z) :
    z (sqrt arity)=(sqrtTwo : ℂ) :=
  OriginalVariableLayout.binding_sqrt z _ (bound_old arity G z hb)

theorem bound_entry (z : Fin (Width arity) → ℂ) (hb : Bound arity G z) (x : Fin (arity i) → Bool) :
    z (address arity i x)=(G i x : ℂ) := by
  have h := OriginalTensorRows.bound_entry arity 1 (OriginalFamilyInput.values arity G false) z
    (bound_old arity G z hb) (.inl i) x
  change z (address arity i x)=(OriginalAffineSystem.sourceVertex arity
    (OriginalFamilyInput.values arity G false) i x : ℂ) at h
  rw [OriginalFamilyInput.sourceVertex_values] at h
  exact h

theorem entries_exact (z : Fin (Width arity) → ℂ) (hb : Bound arity G z)
    (hB : ∀p∈typedBasis arity native opposite,
      SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0)
    (x : Fin (arity i) → Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
      (RuntimeTensorRowsSoundness.entries (address arity i) x)=(transformed arity native opposite i G x : ℂ) :=
  _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.entries_source (algebraMap AlgebraicComplex ℂ) z native opposite
    (imaginary arity) (sqrt arity) (bound_imaginary arity G z hb) (bound_sqrt arity G z hb) hB
    (address arity i) (G i) (bound_entry arity i G z hb) x

def mappedMatrix : Kernel ℂ := fun a b => ((_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.basis native opposite).matrix a b : ℂ)
def mappedInverse : Kernel ℂ := fun a b => ((_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.basis native opposite).inverse a b : ℂ)

theorem mapped_inverse_identity : Kernel.mul (mappedMatrix native opposite) (mappedInverse native opposite)=
    Signature.equality := by
  change Kernel.mul (fun a b => (algebraMap AlgebraicComplex ℂ) ((_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.basis native opposite).matrix a b))
    (fun a b => (algebraMap AlgebraicComplex ℂ) ((_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.basis native opposite).inverse a b)) = _
  rw [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.kernel_map_mul,
    (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.basis native opposite).matrix_inverse,
    _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.kernel_map_equality]

def matrixValues : Fin 5 → ℂ :=
  ![mappedMatrix native opposite false false,mappedMatrix native opposite false true,
    mappedMatrix native opposite true false,mappedMatrix native opposite true true,
    (SymbolicTransform.determinant (mappedMatrix native opposite))⁻¹]

def fill (u : ℂ) : Fin (Width arity) → ℂ :=
  OriginalVariableLayout.fill (matrixValues native opposite) (fun _ : Fin 1 => u)
    (fun j => (OriginalFamilyInput.values arity G false j : ℂ)) OriginalVariableLayout.constants

theorem fill_bound (u : ℂ) : Bound arity G (fill arity native opposite G u) := by
  intro j
  exact (OriginalVariableLayout.fill_binding (matrixValues native opposite) (fun _ : Fin 1 => u)
    (fun j => (OriginalFamilyInput.values arity G false j : ℂ)) j).trans (congrFun (values_coe arity G) j).symm

theorem fill_parameter (u : ℂ) :
    fill arity native opposite G u (Fin.natAdd 5 (0 : Fin (1+(Entries arity+3))))=u :=
  OriginalVariableLayout.fill_parameter (matrixValues native opposite) (fun _ : Fin 1 => u)
    (fun j => (OriginalFamilyInput.values arity G false j : ℂ)) OriginalVariableLayout.constants 0

theorem fill_matrix (u : ℂ) : SymbolicTransform.matrix (SparseTransform.point (fill arity native opposite G u))=
    mappedMatrix native opposite := by
  funext a b
  cases a <;> cases b <;>
    simp [SymbolicTransform.matrix,SparseTransform.point,fill,OriginalVariableLayout.fill,
      SymbolicTransform.index,matrixValues]

theorem fill_guard (u : ℂ) : SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ)
    (fill arity native opposite G u) (SparseTransform.guard RationalCompiler.data (Extra arity))=0 := by
  rw [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.compilerData,SparseEvaluation.guard_eval,fill_matrix]
  change (SymbolicTransform.determinant (mappedMatrix native opposite))⁻¹*
    SymbolicTransform.determinant (mappedMatrix native opposite)-1=0
  rw [inv_mul_cancel₀ (SymbolicTransform.determinant_nonzero_of_inverse _ _ (mapped_inverse_identity native opposite)),sub_self]

theorem fill_basis (u : ℂ) : ∀p∈typedBasis arity native opposite,
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) (fill arity native opposite G u) p=0 := by
  apply (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.rows_zero_iff_map (algebraMap AlgebraicComplex ℂ)
    (fill arity native opposite G u) native opposite (imaginary arity) (sqrt arity)
    (bound_imaginary arity G _ (fill_bound arity native opposite G u))
    (bound_sqrt arity G _ (fill_bound arity native opposite G u))).mpr
  exact ⟨fill_guard arity native opposite G u,fill_matrix arity native opposite G u⟩

/-- The selected runtime candidate's exact source condition. The zero branch
is independent of metadata; nonzero branches require actual validator acceptance. -/
def CandidateTest (f : Signature AlgebraicComplex (arity i)) : Prop :=
  if hz : c.1=true then ∀x,f x=0
  else ∃hv : RuntimeTensorValidation.valid (native,arity i,c.2)=true,
    RuntimeTensorRowsSoundness.shapeBranchTest native f
      (RuntimeTensorRowsSoundness.reifiedShape c.2 (legal.resolve_left hz) native hv)

theorem body_solutions_iff :
    (∃z : Fin (Width arity) → ℂ,Bound arity G z ∧
      ∀p∈typedBody arity native opposite i c legal,
        SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0) ↔
    CandidateTest arity native i c legal (transformed arity native opposite i G) := by
  constructor
  · rintro ⟨z,hb,hbody⟩
    obtain ⟨hB,he⟩ := (List.forall_mem_append.mp hbody)
    by_cases hz : c.1=true
    · rw [CandidateTest,dif_pos hz]
      intro x
      have hx := he (RuntimeTensorRowsSoundness.entries (address arity i) x)
        (by simp [typedExtra,hz,SparseTransform.mem_allWords])
      rw [entries_exact arity native opposite i G z hb hB x] at hx
      exact Subtype.ext hx
    · rw [CandidateTest,dif_neg hz]
      by_cases hv : RuntimeTensorValidation.valid (native,arity i,c.2)=true
      · let gen := legal.resolve_left hz
        have hr := (RuntimeTensorRowsSoundness.rows_eval_iff c.2 gen native hv
          (algebraMap ℚ ℂ) z (address arity i)).mp
            (by simpa only [typedExtra,dif_neg hz,dif_pos hv] using he)
        simp_rw [entries_exact arity native opposite i G z hb hB] at hr
        have hbranch : UniformTensorDecisionSyntax.BranchTest native
            (fun x => (transformed arity native opposite i G x : ℂ))
            (RuntimeTensorReification.count c.2) (RuntimeTensorReification.arity c.2)
            (RuntimeTensorReification.blockPorts c.2 gen native hv) (RuntimeTensorReification.pivot c.2 gen) :=
          ⟨left_ne_zero_of_mul_eq_one hr.1,hr.2⟩
        refine ⟨hv,?_⟩
        exact (UniformTensorDecisionSyntax.branchTest_map_iff (algebraMap AlgebraicComplex ℂ)
          (algebraMap AlgebraicComplex ℂ).injective native (transformed arity native opposite i G)
          _ _ _ _).mp hbranch
      · have hone := he (Sparse.one RationalCompiler.data) (by simp [typedExtra,hz,hv])
        rw [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.compilerData,SparseEvaluation.one_eval] at hone
        exact (one_ne_zero hone).elim
  · intro hc
    by_cases hz : c.1=true
    · rw [CandidateTest,dif_pos hz] at hc
      let z := fill arity native opposite G 0
      have hb : Bound arity G z := fill_bound arity native opposite G 0
      have hB : ∀p∈typedBasis arity native opposite,
          SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0 := fill_basis arity native opposite G 0
      refine ⟨z,hb,List.forall_mem_append.mpr ⟨hB,?_⟩⟩
      intro p hp
      simp only [typedExtra,dif_pos hz,List.mem_map] at hp
      obtain ⟨x,_,rfl⟩ := hp
      rw [entries_exact arity native opposite i G z hb hB x,hc x]
      rfl
    · rw [CandidateTest,dif_neg hz] at hc
      obtain ⟨hv,hbranch⟩ := hc
      let gen := legal.resolve_left hz
      let pvt := RuntimeTensorReification.pivot c.2 gen
      let u : ℂ := (transformed arity native opposite i G pvt : ℂ)⁻¹
      let z := fill arity native opposite G u
      have hb : Bound arity G z := fill_bound arity native opposite G u
      have hB : ∀p∈typedBasis arity native opposite,
          SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0 := fill_basis arity native opposite G u
      have hcomplex : UniformTensorDecisionSyntax.BranchTest native
          (fun x => (transformed arity native opposite i G x : ℂ))
          (RuntimeTensorReification.count c.2) (RuntimeTensorReification.arity c.2)
          (RuntimeTensorReification.blockPorts c.2 gen native hv) pvt :=
        (UniformTensorDecisionSyntax.branchTest_map_iff (algebraMap AlgebraicComplex ℂ)
          (algebraMap AlgebraicComplex ℂ).injective native (transformed arity native opposite i G)
          _ _ _ _).mpr hbranch
      refine ⟨z,hb,List.forall_mem_append.mpr ⟨hB,?_⟩⟩
      simp only [typedExtra,dif_neg hz,dif_pos hv]
      apply (RuntimeTensorRowsSoundness.rows_eval_iff c.2 gen native hv (algebraMap ℚ ℂ) z (address arity i)).mpr
      simp_rw [entries_exact arity native opposite i G z hb hB]
      rw [show z (Fin.natAdd 5 (0 : Fin (1+(Entries arity+3))))=u from fill_parameter arity native opposite G u]
      exact ⟨mul_inv_cancel₀ hcomplex.1,hcomplex.2⟩

/-- Exact meaning of the actual retained candidate-search output. -/
theorem output_correct :
    (output arity input native opposite i c legal G represented).isSome=true ↔
      CandidateTest arity native i c legal (transformed arity native opposite i G) :=
  (output_isSome_iff arity input native opposite i c legal G represented).trans
    (body_solutions_iff arity native opposite i c legal G)

end Meaning

/-- The returned bytes are the actual root-search candidate's serialization,
not a separately chosen algebraic solution. -/
theorem returned_packet (o : WitnessOutput.Output)
    (ho : output arity input native opposite i c legal G represented=some o) :
    ∃a : OriginalSystemWitness.Candidate (m:=Entries arity+2) (typedBody arity native opposite i c legal),
      OriginalSystemWitness.candidate (UniformKPolynomial.descriptors arity input)
        (UniformKPolynomial.valid arity G input represented) (typedBody arity native opposite i c legal)
        (bindings arity)=some a ∧ o=WitnessOutput.ofCandidate a := by
  obtain ⟨a,ha,ho⟩ := Option.map_eq_some_iff.mp ho
  exact ⟨a,ha,ho.symm⟩

def cost : ℕ := Classical.choose (source_outputs arity input native opposite i c legal G represented)

def execution : TM2OutputsInTime _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.machine.computer
    (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.encoding.encode (encode arity input native opposite i c))
    (some (WitnessOutput.resultEncoding.encode (output arity input native opposite i c legal G represented)))
    (cost arity input native opposite i c legal G represented) :=
  Classical.choice (Classical.choose_spec (source_outputs arity input native opposite i c legal G represented))

/-- Primitive operations and every stack prefix of the same complete
request-compilation plus RootCode-search programme. -/
theorem resources :
    primitiveCost _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.machine (execution arity input native opposite i c legal G represented).steps
      (some (initList _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.machine.computer
        (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.encoding.encode (encode arity input native opposite i c)))) ≤
      cost arity input native opposite i c legal G represented*_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.machine.primitiveBudget ∧
    ∀k,k≤(execution arity input native opposite i c legal G represented).steps →
      ∀cfg : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.machine.Config,
      (fun st => st.bind _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.machine.computer.step)^[k]
        (some (initList _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.machine.computer
          (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.encoding.encode (encode arity input native opposite i c))))=some cfg →
      stackSize cfg.stk ≤ (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.encoding.encode (encode arity input native opposite i c)).length +
        cost arity input native opposite i c legal G represented*_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.machine.primitiveBudget := by
  constructor
  · exact (primitiveCost_le _ _ _).trans (Nat.mul_le_mul_right _
      (execution arity input native opposite i c legal G represented).steps_le_m)
  · intro k hk cfg hc
    have h := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.machine.run_size_le
      (initList _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.machine.computer
        (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.encoding.encode (encode arity input native opposite i c))) cfg k hc
    rw [Machine.size_init] at h
    exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _
      (hk.trans (execution arity input native opposite i c legal G represented).steps_le_m)) _)

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource
