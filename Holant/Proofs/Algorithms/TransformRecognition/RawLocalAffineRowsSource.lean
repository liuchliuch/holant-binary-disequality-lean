import Holant.Proofs.Algorithms.TransformRecognition.RationalLocalAffineRowsMachine
import Holant.Proofs.Algorithms.TransformRecognition.RawAffineCandidateSource


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawLocalAffineRowsSource
set_option backward.isDefEq.respectTransparency false
open Holant.Tractable
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open RationalLocalAffineRowsMachine
variable {n v : ℕ}

noncomputable def recordSource (B : LocalAffineNormalForm.Code n)
    (scale inverse : (Fin n → Bool) → Fin v)
    (code : (Fin n → Bool) → EncodedTable.Data) (a : Fin n → Bool) : Record :=
  (List.ofFn a,decide (a ∈ B.1),(scale a).val,(inverse a).val,code a)

noncomputable def sourceRecords (B : LocalAffineNormalForm.Code n)
    (scale inverse : (Fin n → Bool) → Fin v)
    (code : (Fin n → Bool) → EncodedTable.Data) : List Record :=
  (SparseTransform.allWords n).map (recordSource B scale inverse code)

theorem support_source (r : Input) (hw : r.1.1.2.1=v)
    (f : (Fin n → Bool) → Sparse.Poly v 1)
    (hf : ∀ x, RationalSlotTableMachine.polynomial r.1.1 (List.ofFn x)=RationalInputMachine.rowWire (f x))
    (B : LocalAffineNormalForm.Code n) (scale inverse : (Fin n → Bool) → Fin v)
    (code : (Fin n → Bool) → EncodedTable.Data) (a : Fin n → Bool) :
    supportRow r (recordSource B scale inverse code a)=RationalInputMachine.rowWire
      (SymbolicLocalAffineRows.supportRow f B inverse a) := by
  unfold supportRow recordSource
  simp only [hf,hw]
  by_cases h : a ∈ B.1
  · simp only [h,decide_true,ite_true,RationalSparseMachine.variable_wire,
      RationalSparseMachine.one_wire,RationalSparseMachine.mul_wire,RationalSparseMachine.sub_wire,
      SymbolicLocalAffineRows.supportRow,SparseLocalAffineTemplate.supportRow]
  · simp only [h,decide_false,Bool.false_eq_true,ite_false,
      SymbolicLocalAffineRows.supportRow,SparseLocalAffineTemplate.supportRow]

theorem twist_source (r : Input) (hw : r.1.1.2.1=v)
    (f : (Fin n → Bool) → Sparse.Poly v 1)
    (hf : ∀ x, RationalSlotTableMachine.polynomial r.1.1 (List.ofFn x)=RationalInputMachine.rowWire (f x))
    (B : LocalAffineNormalForm.Code n) (imaginary eighth : Fin v)
    (hi : r.1.2.1=imaginary.val) (he : r.1.2.2=eighth.val)
    (scale inverse : (Fin n → Bool) → Fin v)
    (code : (Fin n → Bool) → EncodedTable.Data)
    (hc : ∀ a x, RationalAffineTemplateMachine.value (v,imaginary.val,code a,List.ofFn x)=
      RationalInputMachine.rowWire (SymbolicPhaseCoefficients.affineCoefficient imaginary (B.2 a) x))
    (a x : Fin n → Bool) :
    twistRow r (recordSource B scale inverse code a) (List.ofFn x)=RationalInputMachine.rowWire
      (SymbolicLocalAffineRows.twistRow f B imaginary eighth scale a x) := by
  unfold twistRow recordSource
  simp only [hw,hi,he,hf,hc,RationalLocalTwistMachine.value_source,
    RationalSparseMachine.variable_wire,RationalSparseMachine.mul_wire,RationalSparseMachine.sub_wire]
  rfl

theorem flatMap_support {A C : Type} (xs : List A) (p : A → Prop) [DecidablePred p]
    (f : A → List C) :
    xs.flatMap (fun a => if p a then f a else []) =
      (xs.filter (fun a => decide (p a))).flatMap f := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : p a <;> simp [h,ih]

theorem rows_source (r : Input) (hw : r.1.1.2.1=v) (hn : r.1.1.2.2.1=n)
    (f : (Fin n → Bool) → Sparse.Poly v 1)
    (hf : ∀ x, RationalSlotTableMachine.polynomial r.1.1 (List.ofFn x)=RationalInputMachine.rowWire (f x))
    (B : LocalAffineNormalForm.Code n) (imaginary eighth : Fin v)
    (hi : r.1.2.1=imaginary.val) (he : r.1.2.2=eighth.val)
    (scale inverse : (Fin n → Bool) → Fin v)
    (code : (Fin n → Bool) → EncodedTable.Data)
    (hc : ∀ a x, RationalAffineTemplateMachine.value (v,imaginary.val,code a,List.ofFn x)=
      RationalInputMachine.rowWire (SymbolicPhaseCoefficients.affineCoefficient imaginary (B.2 a) x))
    (hr : r.2=sourceRecords B scale inverse code) :
    rows r=(SymbolicLocalAffineRows.rows f B imaginary eighth scale inverse).map RationalInputMachine.rowWire := by
  have hs : r.2.map (supportRow r) =
      ((SparseTransform.allWords n).map (SymbolicLocalAffineRows.supportRow f B inverse)).map
        RationalInputMachine.rowWire := by
    rw [hr]
    simp only [sourceRecords,List.map_map,Function.comp_def,support_source r hw f hf B scale inverse code]
  have ht : ∀ a : Fin n → Bool,
      twists r (recordSource B scale inverse code a) =
        if a ∈ B.1 then ((SparseTransform.allWords n).map
          (SymbolicLocalAffineRows.twistRow f B imaginary eighth scale a)).map RationalInputMachine.rowWire
        else [] := by
    intro a
    simp only [twists,recordSource,hn,RationalTableMachine.words_eq,List.map_map,Function.comp_def,
      decide_eq_true_eq]
    congr 1
    apply List.map_congr_left
    intro x hx
    exact twist_source r hw f hf B imaginary eighth hi he scale inverse code hc a x
  rw [rows,hs,hr]
  simp only [sourceRecords,List.flatMap_map,Function.comp_def,ht,SymbolicLocalAffineRows.rows,
    List.map_append,List.map_flatMap]
  rw [flatMap_support]

end Holant.LocalDrafts.MainChain.TransformRecognition.RawLocalAffineRowsSource
