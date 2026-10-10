import Holant.ReedMuller.CoefficientAtlas.Code
import Holant.ReedMuller.FlatNetwork.Coordinates
import Holant.Tractable.Affine

/-! Explicit finite affine equations for translated and permuted RM(1,3).
The scalar is recovered from an actual algebraic tensor coefficient, so no
complex witness is silently treated as an algebraic source coefficient. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2CodeAffine
open Holant Holant.Tractable
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CoefficientAtlas
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false
attribute [local instance] Classical.propDecidable

def row (r : Fin (Fintype.card (BinaryVector 8))) : BinaryVector 8 :=
  (Fintype.equivFin (BinaryVector 8)).symm r

def system (e : Equiv.Perm (Fin 8)) (a : BinaryVector 8) : AffineSystem 8 where
  rows := Fintype.card (BinaryVector 8)
  matrix r i := if row r∈code then row r (e.symm i) else 0
  rhs r := if row r∈code then -dot a (row r) else 0

private theorem dot_permute (e : Equiv.Perm (Fin 8)) (x : Fin 8→Bool) (v : BinaryVector 8) :
    (∑ i, v (e.symm i)*bitValue (ZMod 2) (x i)) =
      dot (fun p => boolEquiv (x (e p))) v := by
  rw [←Equiv.sum_comp e (fun i => v (e.symm i)*bitValue (ZMod 2) (x i))]
  simp only [Equiv.symm_apply_apply,dot,boolEquiv,bitValue,mul_comm]
  rfl

private theorem dot_add (u v w : BinaryVector 8) : dot (u+v) w=dot u w+dot v w := by
  simp only [dot,Pi.add_apply,add_mul,Finset.sum_add_distrib]

theorem system_holds (e : Equiv.Perm (Fin 8)) (a : BinaryVector 8) (x : Fin 8→Bool) :
    (system e a).Holds x ↔ (fun p => boolEquiv (x (e p)))+a∈code := by
  rw [code_selfDual]
  constructor
  · intro h v hv
    have hr : row (Fintype.equivFin (BinaryVector 8) v)=v :=
      (Fintype.equivFin (BinaryVector 8)).symm_apply_apply v
    have he := h (Fintype.equivFin (BinaryVector 8) v)
    simp only [system,hr,if_pos hv] at he
    rw [dot_permute] at he
    rw [dot_add,he,neg_add_cancel]
  · intro h r
    change (∑ i, (if row r∈code then row r (e.symm i) else 0)*bitValue (ZMod 2) (x i)) =
      if row r∈code then -dot a (row r) else 0
    by_cases hr : row r∈code
    · simp only [if_pos hr,dot_permute]
      have he := h (row r) hr
      rw [dot_add] at he
      exact eq_neg_of_add_eq_zero_left he
    · simp [hr]

theorem affine_of_code (f : Signature AlgebraicComplex 8) (nonzero : f≠0)
    (e : Equiv.Perm (Fin 8)) (a : BinaryVector 8) (c : ℂ) (_hc : c≠0)
    (equation : ∀ x,(f x:ℂ)=if (fun p => boolEquiv (x (e p)))+a∈code then c else 0) :
    Affine f := by
  classical
  obtain ⟨z,hz⟩ : ∃z,f z≠0 := by
    by_contra h
    push Not at h
    exact nonzero (funext h)
  have hzC : (f z:ℂ)≠0 := by simpa using hz
  have active : (fun p => boolEquiv (z (e p)))+a∈code := by
    by_contra h
    exact hzC ((equation z).trans (if_neg h))
  have coeff : (f z:ℂ)=c := (equation z).trans (if_pos active)
  apply Or.inr
  refine ⟨f z,hz,system e a,QuadraticPhase.zero 8,?_⟩
  funext x
  apply Subtype.ext
  rw [equation]
  simp only [affineFormula,QuadraticPhase.zero_eval,fourthRootPhase_zero,mul_one,system_holds]
  split_ifs <;> simp [coeff]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2CodeAffine
end
