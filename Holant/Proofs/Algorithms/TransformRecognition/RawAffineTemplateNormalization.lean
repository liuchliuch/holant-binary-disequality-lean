import Holant.Proofs.Algorithms.TransformRecognition.RawAffineEnumeration


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineTemplateNormalization
set_option backward.isDefEq.respectTransparency false
open Holant.Tractable
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition

def equation (n : ℕ) (r : EncodedTable.Row) : AffineNormalForm.Equation n :=
  (fun i => FiniteCore.bit2 (r.2.getD i.val false),FiniteCore.bit2 r.1)

def normalize (d : EncodedTable.Data) : AffineNormalForm.Code d.1 :=
  ((d.2.1.map (equation d.1)).toFinset,EncodedTable.constant d,
    (fun i => EncodedTable.linear d i.val),
    (fun i j => decide (EncodedTable.mixed d i.val j.val=2)))

theorem bit_roundtrip (b : Bool) : decide (FiniteCore.bit2 b=1)=b := by
  cases b <;> decide

theorem list_ofFn_getD {A : Type} (xs : List A) (fallback : A) (n : ℕ) (hn : xs.length=n) :
    List.ofFn (fun i : Fin n => xs.getD i.val fallback)=xs := by
  subst n
  have he : (fun i : Fin xs.length => xs.getD i.val fallback) = xs.get := by
    funext i
    exact List.getD_eq_getElem (l := xs) (d := fallback) i.isLt
  rw [he,List.ofFn_get]

theorem row_roundtrip (n : ℕ) (r : EncodedTable.Row) (hr : r.2.length=n) :
    RawAffineEnumeration.rowCode (equation n r)=r := by
  simp only [RawAffineEnumeration.rowCode,equation,bit_roundtrip]
  rw [list_ofFn_getD _ _ _ hr]

theorem row_check (n : ℕ) (r : EncodedTable.Row) (hr : r.2.length=n) (x : Fin n → Bool) :
    decide (DensePrograms.dot r.2 (List.ofFn x)=r.1) =
      decide (AffineNormalForm.equationHolds (equation n r) x) := by
  have h := RationalAffineTemplateSource.row_support (equation n r) x
  have he := row_roundtrip n r hr
  change decide (DensePrograms.dot (RawAffineEnumeration.rowCode (equation n r)).2 (List.ofFn x) =
    (RawAffineEnumeration.rowCode (equation n r)).1) = _ at h
  rwa [he] at h

theorem support_exact (d : EncodedTable.Data) (hd : EncodedTable.Regular d) (x : Fin d.1 → Bool) :
    RationalAffineTemplateMachine.support (d,List.ofFn x) =
      SymbolicPhaseCoefficients.supportCheck (normalize d).1 x := by
  apply Bool.eq_iff_iff.mpr
  rw [SymbolicPhaseCoefficients.supportCheck_iff]
  simp only [RationalAffineTemplateMachine.support,List.all_eq_true,
    AffineNormalForm.supportHolds,normalize,List.mem_toFinset,List.mem_map]
  constructor
  · intro h e he
    obtain ⟨r,hr,rfl⟩ := he
    have hk := h r hr
    rw [row_check _ r (hd.1 r hr) x] at hk
    exact of_decide_eq_true hk
  · intro h r hr
    rw [row_check _ r (hd.1 r hr) x]
    exact decide_eq_true (h _ ⟨r,hr,rfl⟩)

theorem phase_exact (d : EncodedTable.Data) (hd : EncodedTable.Regular d) (x : Fin d.1 → Bool) :
    DensePrograms.phaseValue (d,List.ofFn x) =
      SymbolicPhaseCoefficients.phaseResidue (normalize d).2 x := by
  rw [DensePrograms.phaseValue_exact d hd,SymbolicPhaseCoefficients.phaseResidue_eq]
  simp only [QuadraticPhase.eval,EncodedTable.phase,AffineNormalForm.phase,normalize,
    DensePrograms.getD_ofFn]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i<j
  · rcases hd.2.2.2.2 i j hij with hm | hm
    · have hz : (0 : ZMod 4) ≠ 2 := by decide
      simp [hij,hm,hz]
    · simp [hij,hm]
  · simp [hij]

theorem coefficient_exact {v : ℕ} (imaginary : Fin v)
    (d : EncodedTable.Data) (hd : EncodedTable.Regular d) (x : Fin d.1 → Bool) :
    RationalAffineTemplateMachine.value (v,imaginary.val,d,List.ofFn x) =
      RationalInputMachine.rowWire
        (SymbolicPhaseCoefficients.affineCoefficient imaginary (normalize d) x) := by
  unfold RationalAffineTemplateMachine.value
  rw [support_exact d hd x,phase_exact d hd x,RationalSparseMachine.variable_wire]
  by_cases hs : SymbolicPhaseCoefficients.supportCheck (normalize d).1 x=true
  · simp only [hs,ite_true,SymbolicPhaseCoefficients.affineCoefficient,RationalPowerMachine.power_wire]
  · simp only [hs,ite_false,SymbolicPhaseCoefficients.affineCoefficient,RationalInputMachine.rowWire,List.map_nil,Bool.false_eq_true,ite_false]

end Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineTemplateNormalization
