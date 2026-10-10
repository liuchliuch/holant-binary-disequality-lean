import Holant.Proofs.Algorithms.TransformRecognition.RawAffineCandidateSource
import Holant.Proofs.Algorithms.TransformRecognition.RawAffineRecognitionMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineBodyNormalization
set_option backward.isDefEq.respectTransparency false
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open OriginalAffineSystem
variable {s : ℕ} (arity : Fin s → ℕ)
variable (input : OriginalFamilyInput.Input arity) (disequality : Bool)
variable (c : RawAffineBranchMachine.Templates) (hc : c ∈ RawAffineCandidateSource.generated arity input)

abbrev sourceInput : OriginalFamilyPackingMachine.Input :=
  OriginalFamilyPackingSource.fromSource arity input disequality
abbrev request : RawAffineBranchMachine.Input := (sourceInput arity input disequality,c)
abbrev branch : AffineBranch.Branch arity := RawAffineCandidateSource.normalized arity input c hc

theorem width_exact : OriginalFamilyPackingMachine.width (sourceInput arity input disequality)=Width arity :=
  OriginalFamilyPackingSource.width_exact arity input disequality

theorem imaginary_exact : RawAffineBranchMachine.imaginary (request arity input disequality c) =
    (imaginaryVariable arity).val := by
  simp only [RawAffineBranchMachine.imaginary,request,sourceInput,OriginalFamilyPackingMachine.base,
    OriginalFamilyPackingMachine.parameterCount,OriginalFamilyPackingSource.family_length,
    OriginalFamilyPackingSource.original_length,imaginaryVariable,OriginalVariableLayout.special,Fin.val_natAdd]
  omega

theorem vertex_input (i : Fin s) :
    RawAffineBranchMachine.vertexBlock (request arity input disequality c) i.val =
      ((scaleVariable arity (.inl i)).val,RawAffineCandidateSource.vertex c i,
        (SparseTransform.allWords (arity i)).map
          (fun y => RationalTensorMachine.wireRow (y,entryVariable arity (.inl i) y))) := by
  simp only [RawAffineBranchMachine.vertexBlock,request,sourceInput,
    OriginalFamilyPackingMachine.parameterCount,OriginalFamilyPackingSource.family_length,
    RawAffineBranchSource.family_exact,OriginalCatalogueSource.family_length]
  rw [show i.val=OriginalCatalogueSource.slotNumber (.inl i) from rfl,OriginalCatalogueSource.table_exact]
  rfl

theorem vertex_row (i : Fin s) (x : Fin (arity i) → Bool) :
    RationalAffineRowsMachine.row
      (Width arity,(imaginaryVariable arity).val,RawAffineBranchMachine.vertexBlock
        (request arity input disequality c) i.val) (List.ofFn x) =
      RationalInputMachine.rowWire (row arity (branch arity input c hc) (.inl i) x) := by
  rw [vertex_input]
  unfold RationalAffineRowsMachine.row
  dsimp only
  erw [RationalTensorMachine.dense_vertex_wire (q := Extra arity) x
      (entryVariable arity (.inl i)),RationalSparseMachine.variable_wire,
    RawAffineCandidateSource.vertex_coefficient arity (imaginaryVariable arity) input c hc i x,
    RationalSparseMachine.mul_wire,RationalSparseMachine.sub_wire]
  rfl

theorem vertex_rows (i : Fin s) :
    RationalAffineRowsMachine.rows
      (Width arity,(imaginaryVariable arity).val,RawAffineBranchMachine.vertexBlock
        (request arity input disequality c) i.val) =
      ((SparseTransform.allWords (arity i)).map
        (row arity (branch arity input c hc) (.inl i))).map RationalInputMachine.rowWire := by
  have hd := (RawAffineCandidateSource.vertex_regular arity input c hc i).1
  have hi := vertex_input arity input disequality c i
  simp only [RationalAffineRowsMachine.rows,hi,hd,RationalTableMachine.words_eq,
    List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro x _
  simpa only [hi] using vertex_row arity input disequality c hc i x

theorem edge_input :
    RawAffineBranchMachine.edgeBlock (request arity input disequality c) =
      ((scaleVariable arity (.inr ())).val,c.2,OriginalAffineBodySource.edgeAddresses arity) := by
  simp only [RawAffineBranchMachine.edgeBlock,request,sourceInput,
    OriginalFamilyPackingMachine.parameterCount,OriginalFamilyPackingSource.family_length,
    RawAffineBranchSource.family_exact,OriginalCatalogueSource.family_length]
  have ht := OriginalCatalogueSource.table_exact arity input (.inr ())
  simp only [OriginalCatalogueSource.slotNumber] at ht
  rw [ht]
  rfl

theorem edge_row (x : Fin 2 → Bool) :
    RationalAffineEdgeRowsMachine.row
      (Width arity,(imaginaryVariable arity).val,RawAffineBranchMachine.edgeBlock
        (request arity input disequality c)) (List.ofFn x) =
      RationalInputMachine.rowWire (row arity (branch arity input c hc) (.inr ()) x) := by
  rw [edge_input]
  have h0 : (List.ofFn x).getD 0 false=x 0 :=
    Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.getD_ofFn x (0 : Fin 2) false
  have h1 : (List.ofFn x).getD 1 false=x 1 :=
    Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.getD_ofFn x (1 : Fin 2) false
  unfold RationalAffineEdgeRowsMachine.row
  rw [h0,h1,RationalEdgeMachine.edge_wire _ _ _ _ (OriginalAffineBodySource.edgeAddresses_exact arity),
    RationalSparseMachine.variable_wire,RawAffineCandidateSource.edge_coefficient arity (imaginaryVariable arity) input c hc x,
    RationalSparseMachine.mul_wire,RationalSparseMachine.sub_wire]
  rfl

theorem edge_rows :
    RationalAffineEdgeRowsMachine.rows
      (Width arity,(imaginaryVariable arity).val,RawAffineBranchMachine.edgeBlock
        (request arity input disequality c)) =
      ((SparseTransform.allWords 2).map (row arity (branch arity input c hc) (.inr ()))).map
        RationalInputMachine.rowWire := by
  simp only [RationalAffineEdgeRowsMachine.rows,RationalTableMachine.words_eq,List.map_map,
    Function.comp_def,edge_row arity input disequality c hc]
  rfl

theorem body_exact :
    RationalAffineBodyMachine.body (RawAffineBranchMachine.bodyInput (request arity input disequality c)) =
      RationalInputMachine.bodyWire (body arity (branch arity input c hc)) := by
  have hi := imaginary_exact arity input disequality c
  have hs : (imaginaryVariable arity).val+1=(sqrtVariable arity).val := by
    simp [imaginaryVariable,sqrtVariable,OriginalVariableLayout.special]; omega
  have he : (imaginaryVariable arity).val+2=(eighthVariable arity).val := by
    simp [imaginaryVariable,eighthVariable,OriginalVariableLayout.special]; omega
  have hv : (List.range s).flatMap (fun i => RationalAffineRowsMachine.rows
      (Width arity,(imaginaryVariable arity).val,RawAffineBranchMachine.vertexBlock
        (request arity input disequality c) i)) =
      (List.finRange s).flatMap (fun i => ((SparseTransform.allWords (arity i)).map
        (row arity (branch arity input c hc) (.inl i))).map RationalInputMachine.rowWire) := by
    rw [List.flatMap_def]
    change (CommonFieldMachine.Coordinates.tab s _).flatten = _
    rw [CommonFieldMachine.Coordinates.tab_ofFn,List.ofFn_eq_map,←List.flatMap_def]
    congr 1
    funext i
    exact vertex_rows arity input disequality c hc i
  simp only [RationalAffineBodyMachine.body,RawAffineBranchMachine.bodyInput,
    width_exact,imaginary_exact,hs,he,request,sourceInput,OriginalFamilyPackingSource.family_length,
    List.flatMap_map,Function.comp_def,hv,edge_rows arity input disequality c hc,
    RationalMatrixMachine.guard_wire,RationalAffineBodyMachine.eighth_wire,body,
    eighthRow,ProductVariableLayout.slots,RationalInputMachine.bodyWire,List.map_cons,
    List.map_flatMap,List.map_append,List.flatMap_append,List.flatMap_map,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,Function.comp_def]
  rfl

end Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineBodyNormalization
