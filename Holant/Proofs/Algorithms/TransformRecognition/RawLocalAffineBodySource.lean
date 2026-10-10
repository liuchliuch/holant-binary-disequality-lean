import Holant.Proofs.Algorithms.TransformRecognition.RawLocalAffineBranchMachine
import Holant.Proofs.Algorithms.TransformRecognition.LocalAffineAllocationSource


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawLocalAffineBodySource
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open OriginalLocalAffineSystem
open ProductVariableLayout (Slot slotArity)
variable {s : ℕ} (arity : Fin s → ℕ)
variable (input : OriginalFamilyInput.Input arity) (disequality : Bool)
variable (c : RawLocalAffineFamilyEnumeration.Candidate)

abbrev sourceInput := OriginalFamilyPackingSource.fromSource arity input disequality
abbrev request : RawLocalAffineBranchMachine.Input := (sourceInput arity input disequality,c)
def edgeFlag : Slot s → Bool
  | .inl _ => false
  | .inr _ => true

def original (j : Slot s) : RationalSlotTableMachine.Input :=
  (edgeFlag j,Width arity,slotArity arity j,
    (SparseTransform.allWords (slotArity arity j)).map
      (fun x => RationalTensorMachine.wireRow (x,OriginalTensorRows.entryVariable arity (Count arity) j x)))

theorem count_exact : LocalAffineAllocationMachine.count (sourceInput arity input disequality).1=Count arity :=
  LocalAffineAllocationSource.count_source arity input

theorem width_exact : OriginalAllocatedPackingMachine.width
    (RawLocalAffineBranchMachine.allocated (request arity input disequality c))=Width arity := by
  unfold RawLocalAffineBranchMachine.allocated
  rw [count_exact]
  exact OriginalAllocatedPackingMachine.width_source arity input disequality (Count arity)

theorem imaginary_exact : RawLocalAffineBranchMachine.imaginary (request arity input disequality c)=
    (imaginaryVariable arity).val := by
  simp only [RawLocalAffineBranchMachine.imaginary,RawLocalAffineBranchMachine.allocated,
    OriginalAllocatedPackingMachine.base,request,count_exact,sourceInput,
    OriginalFamilyPackingSource.original_length,imaginaryVariable,OriginalVariableLayout.special,
    Fin.val_natAdd,Fin.val_castAdd]
  simp only [Entries]
  omega

theorem sqrt_exact : RawLocalAffineBranchMachine.imaginary (request arity input disequality c)+1=
    (sqrtVariable arity).val := by
  rw [imaginary_exact]
  simp only [imaginaryVariable,sqrtVariable,OriginalVariableLayout.special,Fin.val_natAdd,Fin.val_castAdd]
  omega

theorem eighth_exact : RawLocalAffineBranchMachine.imaginary (request arity input disequality c)+2=
    (eighthVariable arity).val := by
  rw [imaginary_exact]
  simp only [imaginaryVariable,eighthVariable,OriginalVariableLayout.special,Fin.val_natAdd,Fin.val_castAdd]
  omega

theorem slot_header (j : Slot s) :
    (RawLocalAffineBranchMachine.slot (request arity input disequality c)
      (OriginalCatalogueSource.slotNumber j)).1 =
      (original arity j,(imaginaryVariable arity).val,(eighthVariable arity).val) := by
  unfold RawLocalAffineBranchMachine.slot
  rw [width_exact,eighth_exact,imaginary_exact]
  have hc := LocalAffineAllocationSource.count_source arity input
  have hf : (OriginalFamilyPackingSource.fromSource arity input disequality).1 =
      OriginalCatalogueSource.family arity input := rfl
  have ha := OriginalCatalogueSource.selected_arity arity input j
  have ht := ProductAllocationSource.entry_table_source arity input (Count arity) j
  simp only [RawLocalAffineBranchMachine.arityAt,request,sourceInput,
    OriginalFamilyPackingSource.family_length,hf,hc,ha,ht,original,OriginalCatalogueSource.family_length]
  cases j with
  | inl i => simp [OriginalCatalogueSource.slotNumber,edgeFlag,Nat.ne_of_lt i.isLt]
  | inr u => simp [OriginalCatalogueSource.slotNumber,edgeFlag]

theorem original_polynomial (j : Slot s) (x : Fin (slotArity arity j) → Bool) :
    RationalSlotTableMachine.polynomial (original arity j) (List.ofFn x)=
      RationalInputMachine.rowWire (OriginalTensorRows.compiled arity (Count arity) j x) := by
  cases j with
  | inl i =>
    exact RationalSlotTableMachine.vertex_polynomial
      (OriginalTensorRows.entryVariable arity (Count arity) (.inl i)) x
  | inr u =>
    cases u
    have h0 := Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.getD_ofFn x (0 : Fin 2) false
    have h1 := Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.getD_ofFn x (1 : Fin 2) false
    unfold RationalSlotTableMachine.polynomial original edgeFlag
    simp only [ite_true,h0,h1]
    apply RationalEdgeMachine.edge_wire
    intro a b
    cases a <;> cases b <;> rfl

theorem rows_from_records (B : LocalAffineBranch.Branch arity) (j : Slot s)
    (code : (Fin (slotArity arity j) → Bool) → Holant.LocalDrafts.Tractability.AffineMachine.EncodedTable.Data)
    (hcode : ∀ a x, RationalAffineTemplateMachine.value
        (Width arity,(imaginaryVariable arity).val,code a,List.ofFn x)=
      RationalInputMachine.rowWire
        (SymbolicPhaseCoefficients.affineCoefficient (imaginaryVariable arity) ((B j).2 a) x))
    (hrecords : LocalAffineAllocationMachine.records (OriginalCatalogueSource.family arity input,
        OriginalCatalogueSource.slotNumber j,RawLocalAffineCandidateSource.slotCode c j)=
      RawLocalAffineRowsSource.sourceRecords (B j) (fun a => scaleVariable arity ⟨j,a⟩)
        (fun a => inverseVariable arity ⟨j,a⟩) code) :
    RationalLocalAffineRowsMachine.rows (RawLocalAffineBranchMachine.slot
      (request arity input disequality c) (OriginalCatalogueSource.slotNumber j))=
      (slotRows arity B j).map RationalInputMachine.rowWire := by
  let r := RawLocalAffineBranchMachine.slot (request arity input disequality c) (OriginalCatalogueSource.slotNumber j)
  have hh : r.1=(original arity j,(imaginaryVariable arity).val,(eighthVariable arity).val) :=
    slot_header arity input disequality c j
  apply RawLocalAffineRowsSource.rows_source r
    (by rw [hh]; rfl) (by rw [hh]; rfl)
    (OriginalTensorRows.compiled arity (Count arity) j)
    (fun x => by rw [hh]; exact original_polynomial arity j x)
    (B j) (imaginaryVariable arity) (eighthVariable arity)
    (by rw [hh]) (by rw [hh]) _ _ code hcode
  exact hrecords

theorem normalized_rows (hc : c ∈ RawLocalAffineCandidateSource.generated arity input) (j : Slot s) :
    RationalLocalAffineRowsMachine.rows (RawLocalAffineBranchMachine.slot
      (request arity input disequality c) (OriginalCatalogueSource.slotNumber j))=
      (slotRows arity (RawLocalAffineCandidateSource.normalizedFamily arity input c hc) j).map
        RationalInputMachine.rowWire := by
  apply rows_from_records arity input disequality c
    (RawLocalAffineCandidateSource.normalizedFamily arity input c hc) j
    (fun a => (RawLocalAffineCandidateSource.atWord _ (RawLocalAffineCandidateSource.slotCode c j) a).2)
  · exact RawLocalAffineCandidateSource.normalized_coefficient (imaginaryVariable arity) _ _
      (RawLocalAffineCandidateSource.slot_generated arity input c hc j)
  · exact LocalAffineAllocationSource.records_normalized arity input j _
      (RawLocalAffineCandidateSource.slot_generated arity input c hc j)

theorem canonical_rows (B : LocalAffineBranch.Branch arity) (j : Slot s) :
    RationalLocalAffineRowsMachine.rows (RawLocalAffineBranchMachine.slot
      (request arity input disequality (RawLocalAffineCandidateSource.sourceFamily arity B))
      (OriginalCatalogueSource.slotNumber j))=
      (slotRows arity B j).map RationalInputMachine.rowWire := by
  apply rows_from_records arity input disequality _ B j
    (fun a => RationalAffineTemplateSource.sourceCode ((B j).2 a))
  · intro a x
    exact RationalAffineTemplateSource.value_fromCode _ _ _
  · rw [RawLocalAffineCandidateSource.sourceFamily_slot]
    exact LocalAffineAllocationSource.records_of_map arity input j _

theorem body_from_rows (B : LocalAffineBranch.Branch arity)
    (hrows : ∀ j, RationalLocalAffineRowsMachine.rows (RawLocalAffineBranchMachine.slot
      (request arity input disequality c) (OriginalCatalogueSource.slotNumber j))=
        (slotRows arity B j).map RationalInputMachine.rowWire) :
    RawLocalAffineBranchMachine.body (request arity input disequality c)=
      RationalInputMachine.bodyWire (body arity B) := by
  unfold RawLocalAffineBranchMachine.body
  rw [width_exact,eighth_exact,sqrt_exact,imaginary_exact]
  simp only [request,sourceInput,OriginalFamilyPackingSource.family_length]
  rw [←OriginalCatalogueSource.slots_numbers]
  simp only [List.flatMap_map,Function.comp_def,hrows,RationalMatrixMachine.guard_wire,
    RationalAffineBodyMachine.eighth_wire,body,eighthRow,RationalInputMachine.bodyWire,
    List.map_cons,List.map_flatMap]

theorem normalized_body (hc : c ∈ RawLocalAffineCandidateSource.generated arity input) :
    RawLocalAffineBranchMachine.body (request arity input disequality c)=
      RationalInputMachine.bodyWire (body arity (RawLocalAffineCandidateSource.normalizedFamily arity input c hc)) :=
  body_from_rows arity input disequality c _ (normalized_rows arity input disequality c hc)

theorem canonical_body (B : LocalAffineBranch.Branch arity) :
    RawLocalAffineBranchMachine.body (request arity input disequality (RawLocalAffineCandidateSource.sourceFamily arity B))=
      RationalInputMachine.bodyWire (body arity B) :=
  body_from_rows arity input disequality _ B (canonical_rows arity input disequality B)

end
end Holant.LocalDrafts.MainChain.TransformRecognition.RawLocalAffineBodySource
