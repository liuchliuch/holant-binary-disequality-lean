import Holant.Proofs.Algorithms.TransformRecognition.RawProductCandidateSource


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawProductBodyNormalization
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open OriginalProductSystem
open ProductVariableLayout (Slot slotArity)
variable {s : ℕ} (arity : Fin s → ℕ)
variable (input : OriginalFamilyInput.Input arity) (disequality : Bool)
variable (c : RawProductFamilyEnumeration.Candidate)

abbrev sourceInput := OriginalFamilyPackingSource.fromSource arity input disequality
abbrev request : RawProductBranchMachine.Input := (sourceInput arity input disequality,c)
def edgeFlag : Slot s → Bool
  | .inl _ => false
  | .inr _ => true

def typedSlot (j : Slot s) : RationalProductRowsMachine.Input :=
  ((edgeFlag j,Width arity,slotArity arity j,
    (SparseTransform.allWords (slotArity arity j)).map
      (fun x => RationalTensorMachine.wireRow (x,OriginalTensorRows.entryVariable arity (Count arity) j x))),
    RawProductCandidateSource.slotCode c j,(parameterVariable arity ⟨j,none⟩).val,
    List.ofFn (fun k => ((parameterVariable arity ⟨j,some (k,false)⟩).val,
      (parameterVariable arity ⟨j,some (k,true)⟩).val)))

theorem family_exact : (sourceInput arity input disequality).1 = OriginalCatalogueSource.family arity input := rfl

theorem arity_exact (j : Slot s) :
    RawProductBranchMachine.arityAt (request arity input disequality c)
      (OriginalCatalogueSource.slotNumber j) = slotArity arity j :=
  OriginalCatalogueSource.selected_arity arity input j

theorem unaries_exact (j : Slot s) :
    RawProductBranchMachine.unaryAddresses
      (request arity input disequality c,OriginalCatalogueSource.slotNumber j) =
      List.ofFn (fun k => ((parameterVariable arity ⟨j,some (k,false)⟩).val,
        (parameterVariable arity ⟨j,some (k,true)⟩).val)) := by
  unfold RawProductBranchMachine.unaryAddresses
  rw [arity_exact]
  change CommonFieldMachine.Coordinates.tab (slotArity arity j)
    (fun k => ProductAllocationMachine.unaryPair
      (ProductAllocationMachine.scalarAddress (OriginalCatalogueSource.family arity input,
        OriginalCatalogueSource.slotNumber j),k)) = _
  rw [CommonFieldMachine.Coordinates.tab_ofFn]
  congr 1
  funext k
  exact ProductAllocationSource.unary_source arity input j k

theorem slot_exact (j : Slot s) :
    RawProductBranchMachine.slot (request arity input disequality c)
      (OriginalCatalogueSource.slotNumber j) = typedSlot arity c j := by
  have hcount : ProductAllocationMachine.count (OriginalCatalogueSource.family arity input) = Count arity :=
    ProductAllocationSource.count_source arity input false
  unfold RawProductBranchMachine.slot
  rw [arity_exact,unaries_exact]
  simp only [RawProductBranchMachine.allocated,request,sourceInput,
    ProductAllocationSource.width_source,ProductAllocationSource.count_source,
    OriginalFamilyPackingSource.family_length,family_exact,
    ProductAllocationSource.entry_table_source,ProductAllocationSource.scalar_source,typedSlot,
    OriginalCatalogueSource.family_length,hcount,OriginalAllocatedPackingMachine.width_source]
  cases j with
  | inl i => simp [OriginalCatalogueSource.slotNumber,edgeFlag,RawProductCandidateSource.slotCode,
      Nat.ne_of_lt i.isLt]
  | inr u => simp [OriginalCatalogueSource.slotNumber,edgeFlag,RawProductCandidateSource.slotCode]

theorem original_polynomial (j : Slot s) (x : Fin (slotArity arity j) → Bool) :
    RationalSlotTableMachine.polynomial (typedSlot arity c j).1 (List.ofFn x) =
      RationalInputMachine.rowWire (OriginalTensorRows.compiled arity (Count arity) j x) := by
  cases j with
  | inl i =>
    exact RationalSlotTableMachine.vertex_polynomial
      (OriginalTensorRows.entryVariable arity (Count arity) (.inl i)) x
  | inr u =>
    cases u
    have h0 := Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.getD_ofFn x (0 : Fin 2) false
    have h1 := Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.getD_ofFn x (1 : Fin 2) false
    unfold RationalSlotTableMachine.polynomial typedSlot edgeFlag
    simp only [ite_true,h0,h1]
    apply RationalEdgeMachine.edge_wire
    intro a b
    cases a <;> cases b <;> rfl

variable (hc : c ∈ RawProductCandidateSource.generated arity input)
abbrev branch := RawProductCandidateSource.normalized arity input c hc

theorem row_exact (j : Slot s) (x : Fin (slotArity arity j) → Bool) :
    RationalProductRowsMachine.row
      (RawProductBranchMachine.slot (request arity input disequality c)
        (OriginalCatalogueSource.slotNumber j)) (List.ofFn x) =
      RationalInputMachine.rowWire (row arity (branch arity input c hc) j x) := by
  rw [slot_exact]
  unfold RationalProductRowsMachine.row
  rw [original_polynomial]
  have hv := RawProductCandidateSource.value_exact arity input c hc j
    (fun p => parameterVariable arity ⟨j,p⟩) x
  change RationalSparseMachine.sub _
    (RationalProductTemplateMachine.value (Width arity,RawProductCandidateSource.slotCode c j,
      (parameterVariable arity ⟨j,none⟩).val,
      List.ofFn (fun k => ((parameterVariable arity ⟨j,some (k,false)⟩).val,
        (parameterVariable arity ⟨j,some (k,true)⟩).val)),List.ofFn x)) = _
  rw [hv,RationalSparseMachine.sub_wire]
  rfl

theorem rows_exact (j : Slot s) :
    RationalProductRowsMachine.rows
      (RawProductBranchMachine.slot (request arity input disequality c)
        (OriginalCatalogueSource.slotNumber j)) =
      ((SparseTransform.allWords (slotArity arity j)).map
        (row arity (branch arity input c hc) j)).map RationalInputMachine.rowWire := by
  have hs := slot_exact arity input disequality c j
  simp only [RationalProductRowsMachine.rows,hs,typedSlot,RationalTableMachine.words_eq,
    List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro x _
  simpa only [hs,typedSlot] using row_exact arity input disequality c hc j x

theorem body_exact :
    RawProductBranchMachine.body (request arity input disequality c) =
      RationalInputMachine.bodyWire (body arity (branch arity input c hc)) := by
  unfold RawProductBranchMachine.body
  simp only [RawProductBranchMachine.allocated,request,sourceInput,
    ProductAllocationSource.width_source,OriginalFamilyPackingSource.family_length]
  rw [←OriginalCatalogueSource.slots_numbers]
  simp only [List.flatMap_map,Function.comp_def,rows_exact arity input disequality c hc,
    RationalMatrixMachine.guard_wire,body,RationalInputMachine.bodyWire,List.map_cons,List.map_flatMap]

end
end Holant.LocalDrafts.MainChain.TransformRecognition.RawProductBodyNormalization
