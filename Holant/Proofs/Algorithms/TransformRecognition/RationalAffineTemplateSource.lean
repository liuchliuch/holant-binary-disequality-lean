import Holant.Proofs.Algorithms.TransformRecognition.RationalAffineTemplateMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalAffineTemplateSource
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open RationalAffineTemplateMachine

noncomputable def sourceCode {n : ℕ} (C : AffineNormalForm.Code n) : EncodedTable.Data :=
  (n,C.1.toList.map (fun e => (decide (e.2=1),List.ofFn (fun j => decide (e.1 j=1)))),
    C.2.1,List.ofFn C.2.2.1,List.ofFn (fun j => List.ofFn (fun k => if C.2.2.2 j k then 2 else 0)))

theorem bit2_injective : Function.Injective FiniteCore.bit2 := by
  intro a b h
  cases a <;> cases b <;> simp_all [FiniteCore.bit2]

instance equationHoldsDecidable {n : ℕ} (e : AffineNormalForm.Equation n) (x : Fin n → Bool) :
    Decidable (AffineNormalForm.equationHolds e x) := by
  unfold AffineNormalForm.equationHolds
  infer_instance

theorem row_support {n : ℕ} (e : AffineNormalForm.Equation n) (x : Fin n → Bool) :
    decide (DensePrograms.dot (List.ofFn (fun j => decide (e.1 j=1))) (List.ofFn x) = decide (e.2=1)) =
      decide (AffineNormalForm.equationHolds e x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  have hd := DensePrograms.dot_exact (fun j => decide (e.1 j=1)) x
  simp only [EncodedTable.bit2_residue,FiniteCore.dot_eq] at hd
  constructor
  · intro h
    rw [h,EncodedTable.bit2_residue] at hd
    exact hd.symm
  · intro h
    apply bit2_injective
    rw [hd,EncodedTable.bit2_residue]
    exact h

theorem support_fromCode {n : ℕ} (C : AffineNormalForm.Code n) (x : Fin n → Bool) :
    support (sourceCode C,List.ofFn x) = SymbolicPhaseCoefficients.supportCheck C.1 x := by
  apply Bool.eq_iff_iff.mpr
  simp only [support,sourceCode,List.all_map,Function.comp_def,row_support,List.all_eq_true,
    decide_eq_true_eq,Finset.mem_toList]
  exact (SymbolicPhaseCoefficients.supportCheck_iff C.1 x).symm

theorem phase_fromCode {n : ℕ} (C : AffineNormalForm.Code n) (x : Fin n → Bool) :
    DensePrograms.phaseValue (sourceCode C,List.ofFn x) = SymbolicPhaseCoefficients.phaseResidue C.2 x := by
  simp [DensePrograms.phaseValue,DensePrograms.linearValue,DensePrograms.mixedValue,
    EncodedTable.constant,EncodedTable.linear,EncodedTable.mixed,sourceCode,
    DensePrograms.range_map,DensePrograms.getD_ofFn,SymbolicPhaseCoefficients.phaseResidue,
    FiniteCore.bit4,bitValue,List.sum_ofFn]

theorem value_fromCode {n v : ℕ} (imaginary : Fin v)
    (C : AffineNormalForm.Code n) (x : Fin n → Bool) :
    value (v,imaginary.val,sourceCode C,List.ofFn x) = RationalInputMachine.rowWire
      (SymbolicPhaseCoefficients.affineCoefficient imaginary C x) := by
  unfold value
  rw [support_fromCode,phase_fromCode,RationalSparseMachine.variable_wire]
  by_cases hs : SymbolicPhaseCoefficients.supportCheck C.1 x=true
  · simp only [hs,ite_true,SymbolicPhaseCoefficients.affineCoefficient,RationalPowerMachine.power_wire]
  · simp only [hs,ite_false,SymbolicPhaseCoefficients.affineCoefficient,
      RationalInputMachine.rowWire,List.map_nil,Bool.false_eq_true,ite_false]

noncomputable def source_outputs {n v : ℕ} (imaginary : Fin v)
    (C : AffineNormalForm.Code n) (x : Fin n → Bool) :
    TM2OutputsInTime executes.machine.computer
      (encoding.encode (v,imaginary.val,sourceCode C,List.ofFn x))
      (some (RationalSparseMachine.encoding.encode (RationalInputMachine.rowWire
        (SymbolicPhaseCoefficients.affineCoefficient imaginary C x))))
      (executes.cost (v,imaginary.val,sourceCode C,List.ofFn x)) := by
  have h := executes.outputs (v,imaginary.val,sourceCode C,List.ofFn x)
  rw [value_fromCode] at h
  exact h

end Holant.LocalDrafts.MainChain.TransformRecognition.RationalAffineTemplateSource
