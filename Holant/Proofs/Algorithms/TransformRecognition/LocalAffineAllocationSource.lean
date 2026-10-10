import Holant.Proofs.Algorithms.TransformRecognition.RawLocalAffineCandidateSource
import Holant.Proofs.Algorithms.TransformRecognition.RawLocalAffineRowsSource
import Holant.Proofs.Algorithms.TransformRecognition.ProductAllocationSource
import Holant.Proofs.Algorithms.TransformRecognition.OriginalLocalAffineSystem


namespace Holant.LocalDrafts.MainChain.TransformRecognition.LocalAffineAllocationSource
set_option backward.isDefEq.respectTransparency false
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open LocalAffineAllocationMachine
open OriginalLocalAffineSystem
open ProductVariableLayout (Slot slotArity)
variable {s : ℕ} (arity : Fin s → ℕ)

 theorem entries_source (input : OriginalFamilyInput.Input arity) :
    entries (OriginalCatalogueSource.family arity input)=Entries arity := by
  simp only [entries,OriginalCatalogueSource.catalogue_exact,List.length_map]

theorem count_source (input : OriginalFamilyInput.Input arity) :
    count (OriginalCatalogueSource.family arity input)=Count arity := by
  rw [count,entries_source]

theorem family_exact (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    (OriginalFamilyPackingSource.fromSource arity input disequality).1=OriginalCatalogueSource.family arity input := rfl

theorem count_raw (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    count (OriginalFamilyPackingSource.fromSource arity input disequality).1=Count arity :=
  count_source arity input

theorem width_source (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    OriginalAllocatedPackingMachine.width
      (OriginalFamilyPackingSource.fromSource arity input disequality,
        count (OriginalFamilyPackingSource.fromSource arity input disequality).1)=Width arity := by
  have hc : count (OriginalFamilyPackingSource.fromSource arity input disequality).1=Count arity :=
    count_source arity input
  rw [hc,OriginalAllocatedPackingMachine.width_source]

theorem scalar_source (input : OriginalFamilyInput.Input arity)
    (p : LocalAffineVariableLayout.Parameters arity) :
    OriginalCatalogueMachine.address (0,OriginalCatalogueMachine.catalogue
      (OriginalCatalogueSource.family arity input),OriginalCatalogueSource.key arity p) =
      (scaleVariable arity p).val := by
  rw [OriginalCatalogueSource.catalogue_exact]
  change 5+0+(List.map (OriginalCatalogueSource.key arity)
    (LocalAffineVariableLayout.catalogue arity)).idxOf (OriginalCatalogueSource.key arity p) = _
  rw [OriginalCatalogueSource.idxOf_map_injective _ (OriginalCatalogueSource.key_injective arity)]
  simp only [scaleVariable,scaleIndex,OriginalVariableLayout.parameter,LocalAffineVariableLayout.address,
    Fin.val_natAdd,Fin.val_castAdd,Nat.add_zero]

theorem inverse_source (input : OriginalFamilyInput.Input arity)
    (p : LocalAffineVariableLayout.Parameters arity) :
    OriginalCatalogueMachine.address (entries (OriginalCatalogueSource.family arity input),
      OriginalCatalogueMachine.catalogue (OriginalCatalogueSource.family arity input),
      OriginalCatalogueSource.key arity p) = (inverseVariable arity p).val := by
  rw [entries_source,OriginalCatalogueSource.catalogue_exact]
  change 5+Entries arity+(List.map (OriginalCatalogueSource.key arity)
    (LocalAffineVariableLayout.catalogue arity)).idxOf (OriginalCatalogueSource.key arity p) = _
  rw [OriginalCatalogueSource.idxOf_map_injective _ (OriginalCatalogueSource.key_injective arity)]
  simp only [inverseVariable,OriginalVariableLayout.parameter,LocalAffineVariableLayout.address,
    Fin.val_natAdd,Fin.val_castAdd]
  omega

theorem records_of_map (input : OriginalFamilyInput.Input arity) (j : Slot s)
    (choice : (Fin (slotArity arity j) → Bool) → RawLocalAffineEnumeration.Choice) :
    records (OriginalCatalogueSource.family arity input,OriginalCatalogueSource.slotNumber j,
      (SparseTransform.allWords (slotArity arity j)).map choice) =
      (SparseTransform.allWords (slotArity arity j)).map (fun a =>
        (List.ofFn a,(choice a).1,(scaleVariable arity ⟨j,a⟩).val,
          (inverseVariable arity ⟨j,a⟩).val,(choice a).2)) := by
  let ws := SparseTransform.allWords (slotArity arity j)
  have hk := OriginalCatalogueSource.atVertex_exact arity input j
  unfold records
  rw [hk,List.length_map]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range]
  · intro k hk1 hk2
    have hkw : k<ws.length := by simpa only [List.length_map] using hk2
    simp only [List.getElem_map,List.getElem_range]
    have hkey : key (OriginalCatalogueSource.family arity input,OriginalCatalogueSource.slotNumber j,
        ws.map choice) k = OriginalCatalogueSource.key arity ⟨j,ws[k]⟩ := by
      unfold key
      rw [hk]
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hkw)]
      rw [List.getElem_map,List.getElem_map]
    have hchoice : (ws.map choice).getD k emptyChoice=choice ws[k] := by
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hkw),List.getElem_map]
    change (record (OriginalCatalogueSource.family arity input,OriginalCatalogueSource.slotNumber j,ws.map choice) k) = _
    unfold record
    rw [hkey,hchoice]
    dsimp only
    rw [scalar_source arity input ⟨j,ws[k]⟩,inverse_source arity input ⟨j,ws[k]⟩]
    rfl

theorem records_normalized (input : OriginalFamilyInput.Input arity) (j : Slot s)
    (c : RawLocalAffineEnumeration.Candidate)
    (hc : c ∈ RawLocalAffineEnumeration.candidates (slotArity arity j)) :
    records (OriginalCatalogueSource.family arity input,OriginalCatalogueSource.slotNumber j,c) =
      RawLocalAffineRowsSource.sourceRecords
        (RawLocalAffineCandidateSource.normalized _ c hc)
        (fun a => scaleVariable arity ⟨j,a⟩) (fun a => inverseVariable arity ⟨j,a⟩)
        (fun a => (RawLocalAffineCandidateSource.atWord _ c a).2) := by
  conv_lhs => rw [←RawLocalAffineCandidateSource.reconstruct _ c hc]
  rw [records_of_map]
  unfold RawLocalAffineRowsSource.sourceRecords
  apply List.map_congr_left
  intro a ha
  simp only [RawLocalAffineRowsSource.recordSource,RawLocalAffineCandidateSource.normalized_mask]

end Holant.LocalDrafts.MainChain.TransformRecognition.LocalAffineAllocationSource
