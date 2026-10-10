import Holant.Proofs.Hardness.GeneralEOPhaseExtractionMatchingConjugation
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionPositiveSwitch
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionClosurePhase
import Mathlib.GroupTheory.Perm.Sign

/-! Matching switches close the binary-symmetric residual when all actual
quaternary graphs are zero or positive tensor products. The source-level
contrapositive supplies an actual quaternary graph outside that residual. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionMatchingSwitch
open Holant Holant.Complexity FixedGadgetSubstitution
namespace C
export GeneralEOPhaseExtractionCore (Collinear area collinear_trans collinear_zero_left)
end C
namespace M
export GeneralEOPhaseExtractionMatchingNormalForm (value realize normal_form)
end M
namespace O
export GeneralEOPhaseExtractionMatchingOrder (blockPerm value_blockPerm)
end O
namespace P
export GeneralEOPhaseExtractionMatchingCap (capSignature lastPerm value_partial partial_permute
  cap cap_denote labels exact native central selfdual)
end P
namespace Q
export GeneralEOPhaseExtractionPositiveSwitch (positive comparison)
end Q
namespace R
export GeneralEOPinnedDescentNetwork (reboundary reboundaryLabels reboundary_denote)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def Comparable (a b : ℂ) : Prop := (a=0 ↔ b=0) ∧ C.Collinear a b

theorem comparable_refl (a : ℂ) : Comparable a a := by
  exact ⟨Iff.rfl,by simp [C.Collinear,C.area,mul_comm]⟩

theorem comparable_symm {a b : ℂ} (h : Comparable a b) : Comparable b a := by
  refine ⟨h.1.symm,?_⟩
  have he := h.2
  unfold C.Collinear C.area at he ⊢
  linarith

theorem comparable_trans {a b c : ℂ} (h : Comparable a b) (g : Comparable b c) : Comparable a c := by
  refine ⟨h.1.trans g.1,?_⟩
  by_cases hb : b=0
  · rw [h.1.mpr hb,g.1.mp hb]
    exact C.collinear_zero_left 0
  · exact C.collinear_trans hb h.2 g.2

def PositivePattern (f : Signature ℂ 4) : Prop :=
  f=0 ∨ ∃c : ℂ,∃e : Equiv.Perm (Fin 4),Tensor.reindex e f=Q.positive c

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature ℂ (a i.val))

def AllPositive : Prop :=
  ∀ (Q : Network ℂ 4) (QL : Labelling Q.shape s 1 a),
    LabelledNetwork.Exact G Q QL → (∀e,Q.edge e=Signature.disequality) →
    Signature.CentralSupport Q.denote → SelfDualPinObstruction.SelfDual Q.denote → PositivePattern Q.denote

variable (hGood : AllPositive G)

include hGood in
theorem last_comparison (k : ℕ) (S : Network ℂ (2*k+4))
    (SL : Labelling S.shape s 1 a) (hL : LabelledNetwork.Exact G S SL)
    (hN : ∀e,S.edge e=Signature.disequality) (hE : Signature.CentralSupport S.denote)
    (hS : SelfDualPinObstruction.SelfDual S.denote) (p : Equiv.Perm (Fin 4)) :
    Comparable (M.value (k+2) S.denote) (M.value (k+2) (Tensor.reindex (P.lastPerm k p) S.denote)) := by
  let U := P.cap k S
  have hU : PositivePattern U.denote := hGood U (P.labels k S SL)
    (P.exact G k S SL hL) (P.native k S hN) (P.central k S hE) (P.selfdual k S hS)
  obtain ⟨A,hA,ha⟩ := M.realize 2 U (Equiv.refl _)
  obtain ⟨B,hB,hb⟩ := M.realize 2 U p
  have h := Q.comparison U hU hA hB
  rw [ha,hb] at h
  change Comparable (M.value 2 U.denote) (M.value 2 (Tensor.reindex p U.denote)) at h
  rw [P.value_partial k S.denote,
    P.value_partial k (Tensor.reindex (P.lastPerm k p) S.denote),P.partial_permute]
  rw [←P.cap_denote]
  exact h

include hGood in
theorem swap_comparison (k : ℕ) (S : Network ℂ (2*k+4))
    (SL : Labelling S.shape s 1 a) (hL : LabelledNetwork.Exact G S SL)
    (hN : ∀e,S.edge e=Signature.disequality) (hE : Signature.CentralSupport S.denote)
    (hS : SelfDualPinObstruction.SelfDual S.denote) (i j : Fin (2*k+4)) :
    Comparable (M.value (k+2) S.denote) (M.value (k+2) (Tensor.reindex (Equiv.swap i j) S.denote)) := by
  obtain ⟨p,q,hpq⟩ := GeneralEOPhaseExtractionMatchingConjugation.tail_swap k i j
  let T := R.reboundary S (O.blockPerm p)
  let TL := R.reboundaryLabels S SL (O.blockPerm p)
  have hTE : Signature.CentralSupport T.denote :=
    GeneralEOCentralHoleCoordinates.reboundary_central S (O.blockPerm p).symm hE
  have hTS : SelfDualPinObstruction.SelfDual T.denote := by
    intro x
    rw [R.reboundary_denote]
    exact hS (x ∘ O.blockPerm p)
  have h := last_comparison G hGood k T TL hL hN hTE hTS q
  have hT : T.denote=Tensor.reindex (O.blockPerm p) S.denote := R.reboundary_denote _ _
  have hv : Tensor.reindex (P.lastPerm k q) T.denote=
      Tensor.reindex (O.blockPerm p) (Tensor.reindex (Equiv.swap i j) S.denote) := by
    rw [hT]
    change Tensor.reindex ((O.blockPerm p).trans (P.lastPerm k q)) S.denote=
      Tensor.reindex ((Equiv.swap i j).trans (O.blockPerm p)) S.denote
    rw [hpq]
  rw [hv,hT,O.value_blockPerm,O.value_blockPerm] at h
  exact h

include hGood in
theorem all_comparable (k : ℕ) (S : Network ℂ (2*k+4))
    (SL : Labelling S.shape s 1 a) (hL : LabelledNetwork.Exact G S SL)
    (hN : ∀e,S.edge e=Signature.disequality) (hE : Signature.CentralSupport S.denote)
    (hS : SelfDualPinObstruction.SelfDual S.denote) (e : Equiv.Perm (Fin (2*k+4))) :
    Comparable (M.value (k+2) S.denote) (M.value (k+2) (Tensor.reindex e S.denote)) := by
  induction e using Equiv.Perm.swap_induction_on with
  | one => exact comparable_refl _
  | swap_mul e i j _ ih =>
    have hTE := GeneralEOCentralHoleCoordinates.reboundary_central S e.symm hE
    have hTS : SelfDualPinObstruction.SelfDual (R.reboundary S e).denote := by
      intro x
      rw [R.reboundary_denote]
      exact hS (x ∘ e)
    have h := swap_comparison G hGood k (R.reboundary S e) (R.reboundaryLabels S SL e)
      hL hN hTE hTS i j
    rw [R.reboundary_denote] at h
    exact comparable_trans ih h

include hGood in
/-- If every actual original-labelled quaternary graph is zero or a positive
pair tensor, every central selfdual original-labelled source is ARS. -/
theorem ars_of_positive_caps (k : ℕ) (S : Network ℂ (2*k+4))
    (SL : Labelling S.shape s 1 a) (hL : LabelledNetwork.Exact G S SL)
    (hN : ∀e,S.edge e=Signature.disequality) (hE : Signature.CentralSupport S.denote)
    (hS : SelfDualPinObstruction.SelfDual S.denote) : GeneralEOARSBoundary.ARSUpToScale S.denote := by
  classical
  by_contra hA
  obtain ⟨A,B,hA',hB',hphase⟩ := GeneralEOPhaseExtractionClosurePhase.nonars_closed_phase S hE hS hA
  obtain ⟨e,he⟩ := M.normal_form (k+2) S hA'
  obtain ⟨f,hf⟩ := M.normal_form (k+2) S hB'
  have h := comparable_trans (comparable_symm (all_comparable G hGood k S SL hL hN hE hS e))
    (all_comparable G hGood k S SL hL hN hE hS f)
  rw [he,hf] at hphase
  exact hphase h.2

/-- The non-ARS binary-symmetric branch supplies a real original-labelled
quaternary graph outside zero and positive tensor products. It may already be
a hard/pinning source or the signed tensor-square programme resource. -/
theorem exists_nonpositive_quaternary (k : ℕ) (S : Network ℂ (2*k+4))
    (SL : Labelling S.shape s 1 a) (hL : LabelledNetwork.Exact G S SL)
    (hN : ∀e,S.edge e=Signature.disequality) (hE : Signature.CentralSupport S.denote)
    (hS : SelfDualPinObstruction.SelfDual S.denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale S.denote) :
    ∃ (Q : Network ℂ 4) (QL : Labelling Q.shape s 1 a),
      LabelledNetwork.Exact G Q QL ∧ (∀e,Q.edge e=Signature.disequality) ∧
      Signature.CentralSupport Q.denote ∧ SelfDualPinObstruction.SelfDual Q.denote ∧ ¬PositivePattern Q.denote := by
  classical
  by_contra h
  push Not at h
  exact hA (ars_of_positive_caps G h k S SL hL hN hE hS)

/-- Arbitrary-arity form; central support and non-ARS exclude odd, nullary,
and binary sources internally. -/
theorem exists_nonpositive_quaternary_any {n : ℕ} (S : Network ℂ n)
    (SL : Labelling S.shape s 1 a) (hL : LabelledNetwork.Exact G S SL)
    (hN : ∀e,S.edge e=Signature.disequality) (hE : Signature.CentralSupport S.denote)
    (hS : SelfDualPinObstruction.SelfDual S.denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale S.denote) :
    ∃ (Q : Network ℂ 4) (QL : Labelling Q.shape s 1 a),
      LabelledNetwork.Exact G Q QL ∧ (∀e,Q.edge e=Signature.disequality) ∧
      Signature.CentralSupport Q.denote ∧ SelfDualPinObstruction.SelfDual Q.denote ∧ ¬PositivePattern Q.denote := by
  obtain ⟨x,y,hxy⟩ := GeneralEOPhaseExtractionStructure.nonars_has_phase S.denote (Or.inl hS) hA
  have hx := (GeneralEOPhaseExtractionCore.noncollinear_nonzero hxy).1
  have hw : 2*weight x=n := by
    by_contra h
    exact hx (hE x h)
  have hn0 : n≠0 := by
    rintro rfl
    have he : x=y := by funext i; exact Fin.elim0 i
    rw [he] at hxy
    exact hxy (comparable_refl (S.denote y)).2
  have hn2 : n≠2 := by
    rintro rfl
    exact hxy (GeneralEOPhaseExtractionSigns.binary_singlePhase S.denote hE (Or.inl hS) x y)
  obtain ⟨k,rfl⟩ : ∃k,n=2*k+4 := ⟨weight x-2,by omega⟩
  exact exists_nonpositive_quaternary G k S SL hL hN hE hS hA

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionMatchingSwitch
