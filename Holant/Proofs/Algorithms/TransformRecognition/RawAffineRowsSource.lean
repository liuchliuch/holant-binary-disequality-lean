import Holant.Proofs.Algorithms.TransformRecognition.RawAffineEnumerationValidity
import Holant.Proofs.Algorithms.TransformRecognition.RationalAffineEdgeRowsMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineRowsSource
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition

theorem vertex_row {q : ℕ} (imaginary scale : Fin (5+q))
    (d : EncodedTable.Data) (hd : EncodedTable.Regular d)
    (address : (Fin d.1 → Bool) → Fin (5+q)) (x : Fin d.1 → Bool) :
    RationalAffineRowsMachine.row (5+q,imaginary.val,scale.val,d,
      (SparseTransform.allWords d.1).map (fun y => RationalTensorMachine.wireRow (y,address y)))
      (List.ofFn x) = RationalInputMachine.rowWire
        (RationalAffineRowsMachine.sourceRow imaginary scale
          (RawAffineTemplateNormalization.normalize d) address x) := by
  unfold RationalAffineRowsMachine.row
  rw [RationalTensorMachine.dense_vertex_wire,RationalSparseMachine.variable_wire,
    RawAffineTemplateNormalization.coefficient_exact imaginary d hd,
    RationalSparseMachine.mul_wire,RationalSparseMachine.sub_wire]
  rfl

theorem vertex_rows {q : ℕ} (imaginary scale : Fin (5+q))
    (d : EncodedTable.Data) (hd : EncodedTable.Regular d)
    (address : (Fin d.1 → Bool) → Fin (5+q)) :
    RationalAffineRowsMachine.rows (5+q,imaginary.val,scale.val,d,
      (SparseTransform.allWords d.1).map (fun y => RationalTensorMachine.wireRow (y,address y))) =
      ((SparseTransform.allWords d.1).map
        (RationalAffineRowsMachine.sourceRow imaginary scale
          (RawAffineTemplateNormalization.normalize d) address)).map RationalInputMachine.rowWire := by
  simp only [RationalAffineRowsMachine.rows,RationalTableMachine.words_eq,List.map_map,
    Function.comp_def,vertex_row imaginary scale d hd]

theorem edge_row {q : ℕ} (imaginary scale : Fin (5+q))
    (payload : List EncodedTable.Row × EncodedTable.Phase)
    (hd : EncodedTable.Regular (2,payload)) (addresses : List ℕ)
    (E : Bool → Bool → Fin (5+q))
    (haddr : ∀ a b, addresses.getD (SymbolicTransform.index a b).val 0 = (E a b).val)
    (x : Fin 2 → Bool) :
    RationalAffineEdgeRowsMachine.row (5+q,imaginary.val,scale.val,(2,payload),addresses) (List.ofFn x) =
      RationalInputMachine.rowWire (RationalAffineEdgeRowsMachine.sourceRow imaginary scale
        (RawAffineTemplateNormalization.normalize (2,payload)) E x) := by
  have h0 : (List.ofFn x).getD 0 false=x 0 :=
    Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.getD_ofFn x (0 : Fin 2) false
  have h1 : (List.ofFn x).getD 1 false=x 1 :=
    Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.getD_ofFn x (1 : Fin 2) false
  unfold RationalAffineEdgeRowsMachine.row
  rw [h0,h1,RationalEdgeMachine.edge_wire _ _ addresses E haddr,
    RationalSparseMachine.variable_wire,RawAffineTemplateNormalization.coefficient_exact imaginary (2,payload) hd,
    RationalSparseMachine.mul_wire,RationalSparseMachine.sub_wire]
  rfl

/-- Normalization may reorder support rows, but it changes no emitted entry.
The equality is for an arbitrary assignment in the stored arity. -/
theorem coefficient_canonical {v : ℕ} (imaginary : Fin v)
    (d : EncodedTable.Data) (hd : EncodedTable.Regular d) (x : Fin d.1 → Bool) :
    RationalAffineTemplateMachine.value (v,imaginary.val,d,List.ofFn x) =
      RationalAffineTemplateMachine.value (v,imaginary.val,
        RationalAffineTemplateSource.sourceCode (RawAffineTemplateNormalization.normalize d),List.ofFn x) := by
  rw [RawAffineTemplateNormalization.coefficient_exact imaginary d hd,
    RationalAffineTemplateSource.value_fromCode]

end Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineRowsSource
