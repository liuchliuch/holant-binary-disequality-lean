import Holant.Proofs.Algorithms.TransformRecognition.RationalAffineBodyMachine
import Holant.Proofs.Algorithms.TransformRecognition.OriginalAffineSystem


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalAffineBodySource
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open OriginalAffineSystem
variable {s : ℕ} (arity : Fin s → ℕ)

noncomputable def vertexBlock (B : AffineBranch.Branch arity) (i : Fin s) : RationalAffineRowsMachine.Block :=
  ((scaleVariable arity (.inl i)).val,RationalAffineTemplateSource.sourceCode (B.1 i),
    (SparseTransform.allWords (arity i)).map
      (fun y => RationalTensorMachine.wireRow (y,entryVariable arity (.inl i) y)))

def edgeAddresses : List ℕ :=
  [(entryVariable arity (.inr ()) ![false,false]).val,
   (entryVariable arity (.inr ()) ![false,true]).val,
   (entryVariable arity (.inr ()) ![true,false]).val,
   (entryVariable arity (.inr ()) ![true,true]).val]

theorem edgeAddresses_exact (a b : Bool) :
    (edgeAddresses arity).getD (SymbolicTransform.index a b).val 0 =
      (entryVariable arity (.inr ()) ![a,b]).val := by
  cases a <;> cases b <;> rfl

noncomputable def edgeBlock (B : AffineBranch.Branch arity) : RationalAffineEdgeRowsMachine.Block :=
  ((scaleVariable arity (.inr ())).val,RationalAffineTemplateSource.sourceCode B.2,edgeAddresses arity)

noncomputable def encode (B : AffineBranch.Branch arity) : RationalAffineBodyMachine.Input :=
  (Width arity,(imaginaryVariable arity).val,(sqrtVariable arity).val,(eighthVariable arity).val,
    (List.finRange s).map (vertexBlock arity B),edgeBlock arity B)

theorem vertex_rows (B : AffineBranch.Branch arity) (i : Fin s) :
    RationalAffineRowsMachine.rows (Width arity,(imaginaryVariable arity).val,vertexBlock arity B i) =
      ((SparseTransform.allWords (arity i)).map (row arity B (.inl i))).map RationalInputMachine.rowWire := by
  have h := RationalAffineRowsMachine.rows_fromSource
    (imaginaryVariable arity) (scaleVariable arity (.inl i)) (B.1 i)
    (entryVariable arity (.inl i))
  have hr : RationalAffineRowsMachine.sourceRow
      (imaginaryVariable arity) (scaleVariable arity (.inl i)) (B.1 i)
      (entryVariable arity (.inl i)) = row arity B (.inl i) := by
    funext x
    rfl
  rw [hr] at h
  exact h

theorem edge_row (B : AffineBranch.Branch arity) (x : Fin 2 → Bool) :
    RationalAffineEdgeRowsMachine.row
      (Width arity,(imaginaryVariable arity).val,edgeBlock arity B) (List.ofFn x) =
      RationalInputMachine.rowWire (row arity B (.inr ()) x) := by
  have h := RationalAffineEdgeRowsMachine.row_fromSource
    (imaginaryVariable arity) (scaleVariable arity (.inr ())) B.2 (edgeAddresses arity)
    (fun a b => entryVariable arity (.inr ()) ![a,b]) (edgeAddresses_exact arity) x
  simpa only [edgeBlock,RationalAffineEdgeRowsMachine.sourceRow,row,compiled,codeAt,Extra,Width,OriginalVariableLayout.Width] using h

theorem edge_rows (B : AffineBranch.Branch arity) :
    RationalAffineEdgeRowsMachine.rows (Width arity,(imaginaryVariable arity).val,edgeBlock arity B) =
      ((SparseTransform.allWords 2).map (row arity B (.inr ()))).map RationalInputMachine.rowWire := by
  simp only [RationalAffineEdgeRowsMachine.rows,RationalTableMachine.words_eq,List.map_map,
    Function.comp_def,edge_row]
  rfl

theorem body_exact (B : AffineBranch.Branch arity) :
    RationalAffineBodyMachine.body (encode arity B) = RationalInputMachine.bodyWire (body arity B) := by
  simp only [RationalAffineBodyMachine.body,encode,List.flatMap_map,Function.comp_def,
    vertex_rows,edge_rows,RationalMatrixMachine.guard_wire,RationalAffineBodyMachine.eighth_wire,
    body,eighthRow,ProductVariableLayout.slots,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,RationalInputMachine.bodyWire,List.map_cons,List.map_append,List.map_flatMap]
  rfl

noncomputable def outputs (B : AffineBranch.Branch arity) :
    TM2OutputsInTime RationalAffineBodyMachine.executes.machine.computer
      (RationalAffineBodyMachine.encoding.encode (encode arity B))
      (some (RationalSparseMachine.familyEncoding.encode (RationalInputMachine.bodyWire (body arity B))))
      (RationalAffineBodyMachine.executes.cost (encode arity B)) := by
  have h := RationalAffineBodyMachine.executes.outputs (encode arity B)
  rw [body_exact] at h
  exact h

end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalAffineBodySource
