import Holant.Certificates.AffineEndpoint.Scalars
import Holant.Tractable.AffineOperations
import Holant.Certificates.AffineReference.FullEvenCoverage

/-! Complete intrinsic normalized affine phase parameters, with genuine
Z/4 quadratics and the actual AlgebraicComplex phase interpretation. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev MixedPair (d : ℕ) := {p : Fin d×Fin d // p.1<p.2}
abbrev PhaseParameters (d : ℕ) := (Fin d→Fin 4) × (MixedPair d→Bool)

 def phaseQuadratic {d : ℕ} (p : PhaseParameters d) : QuadraticPhase d where
  constant := 0
  linear j := (p.1 j).val
  mixed j k := if h : j<k then (if p.2 ⟨(j,k),h⟩ then 2 else 0) else 0
  even_mixed j k h := by
    simp only [dif_pos h]
    cases p.2 ⟨(j,k),h⟩ <;> simp

 def phaseValue {d : ℕ} (p : PhaseParameters d) (y : Fin d→Bool) : AlgebraicComplex :=
  fourthRootPhase ((phaseQuadratic p).eval y)

 def intrinsicParameters {d : ℕ} (Q : QuadraticPhase d) : PhaseParameters d :=
  (fun j => ⟨(Q.linear j).val,(Q.linear j).val_lt⟩,
    fun jk => decide (Q.mixed jk.val.1 jk.val.2=2))

 theorem intrinsicParameters_eval {d : ℕ} (Q : QuadraticPhase d) (y : Fin d→Bool) :
    (phaseQuadratic (intrinsicParameters Q)).eval y=Q.eval y-Q.constant := by
  have hlin (j : Fin d) : (phaseQuadratic (intrinsicParameters Q)).linear j=Q.linear j := by
    simp [phaseQuadratic,intrinsicParameters]
  have h02 : (0 : ZMod 4)≠2 := by decide
  have hmix (j k : Fin d) (h : j<k) :
      (phaseQuadratic (intrinsicParameters Q)).mixed j k=Q.mixed j k := by
    rcases Q.even_mixed j k h with hq|hq <;>
      simp [phaseQuadratic,intrinsicParameters,h,hq,h02]
  have hc : (phaseQuadratic (intrinsicParameters Q)).constant=0 := rfl
  simp only [QuadraticPhase.eval,hlin,hc,zero_add]
  have hm : (∑j,∑k,if j<k then
      (phaseQuadratic (intrinsicParameters Q)).mixed j k*bitValue (ZMod 4) (y j)*bitValue (ZMod 4) (y k) else 0)=
      ∑j,∑k,if j<k then Q.mixed j k*bitValue (ZMod 4) (y j)*bitValue (ZMod 4) (y k) else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : j<k
    · simp [h,hmix j k h]
    · simp [h]
  rw [hm]
  ring

 theorem phaseValue_affine {d : ℕ} (p : PhaseParameters d) : Affine (phaseValue p) :=
  TwoTranslate.affine_quadratic_phase (phaseQuadratic p)

 theorem phaseValue_origin {d : ℕ} (p : PhaseParameters d) : phaseValue p (origin d)=1 := by
  simp [phaseValue,QuadraticPhase.eval,phaseQuadratic,origin]

 theorem normalized_full_phase_coverage {d : ℕ} (f : Signature AlgebraicComplex d)
    (hf : Affine f) (hn : ∀y,f y≠0) (h0 : f (origin d)=1) :
    ∃p : PhaseParameters d,f=phaseValue p := by
  rcases hf with hz|⟨c,hc,S,Q,hf⟩
  · exact False.elim (hn (origin d) (congrFun hz _))
  have hS (y : Fin d→Bool) : S.Holds y := by
    have h := hn y
    rw [hf] at h
    by_contra hs
    exact h (by simp [affineFormula,hs])
  have hs : c*fourthRootPhase Q.constant=1 := by
    have h := congrFun hf (origin d)
    rw [h0] at h
    simpa [affineFormula,hS,QuadraticPhase.eval,origin] using h.symm
  refine ⟨intrinsicParameters Q,?_⟩
  funext y
  rw [hf]
  simp only [affineFormula,if_pos (hS y),phaseValue,intrinsicParameters_eval,fourthRootPhase_sub]
  have hcval : c=1/fourthRootPhase Q.constant :=
    (eq_div_iff (fourthRootPhase_ne_zero _)).mpr hs
  rw [hcval]
  ring

 theorem phase_parameter_counts :
    Fintype.card (PhaseParameters 0)=1 ∧ Fintype.card (PhaseParameters 1)=4 ∧
    Fintype.card (PhaseParameters 2)=32 ∧ Fintype.card (PhaseParameters 3)=512 ∧
    Fintype.card (PhaseParameters 4)=16384 := by
  simp only [PhaseParameters,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  decide +kernel

end
end Holant.Certificates.AffineEndpoint
