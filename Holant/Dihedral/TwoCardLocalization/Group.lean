import Holant.Dihedral.TwoCardLocalization.DistinctCore
import Holant.Dihedral.TwoCardLocalization.FusionTags

/-! The literal source dihedral group satisfies the shared matching-surgery
matrix interface. Transfer safety and membership are proved equivalent here. -/
noncomputable section
namespace Holant.Dihedral.TwoCardLocalization
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Certificates
set_option backward.isDefEq.respectTransparency false

theorem groupM_matrix_group {m : ℕ} (hm : 0<m) :
    MatchingContractionClosure.ProjectiveMatrixGroup (K:=Scalar) (groupM m) := by
  have hG := groupM_is_group hm
  refine ⟨?_,?_,?_,?_⟩
  · have he : (1 : Matrix Bool Bool Scalar) = (Signature.equality : Mat) := by
      funext a b
      simp [Signature.equality,Matrix.one_apply]
    rw [he]
    exact hG.identity_mem
  · intro A hA B hB
    exact hG.mul_mem A hA B hB
  · intro A hA
    obtain ⟨B,hB,hAB,hBA⟩ := hG.inverse_mem A hA
    refine ⟨B,hB,?_,?_⟩
    · funext a b
      have h := congrFun (congrFun hAB a) b
      simpa [Kernel.mul,Matrix.mul_apply,Signature.equality,Matrix.one_apply] using h
    · funext a b
      have h := congrFun (congrFun hBA a) b
      simpa [Kernel.mul,Matrix.mul_apply,Signature.equality,Matrix.one_apply] using h
  · intro A hA c hc
    exact hG.scale_mem A hA c hc

theorem groupM_X {m : ℕ} (hm : 0<m) :
    (MatchingContractionClosure.X (K:=Scalar) : Mat) ∈ groupM m := by
  have he : (MatchingContractionClosure.X (K:=Scalar) : Mat)=M true 1 := by
    funext a b
    cases a <;> cases b <;> simp [MatchingContractionClosure.X,M,monomial,Signature.disequality]
  rw [he]
  exact M_mem_group hm true (Roots.one m)

theorem groupM_reversal {m : ℕ} (hm : 0<m) :
    MatchingContractionClosure.ReversalStable (K:=Scalar) (groupM m) := by
  intro A hA
  exact groupM_mul hm (groupM_mul hm (groupM_X hm) (transpose_group_mem hm hA)) (groupM_X hm)

theorem safe_groupM_iff {m : ℕ} (hm : 0<m) (A : Mat) :
    MatchingContractionClosure.SafeBinary (K:=Scalar) (groupM m) A ↔ A ∈ groupM m := by
  constructor
  · intro h
    have hh := (groupM_matrix_group hm).mul_mem _ h _ (groupM_X hm)
    simpa only [MatchingContractionClosure.transfer,Matrix.mul_assoc,
      MatchingContractionClosure.X_mul_X,Matrix.mul_one] using hh
  · intro h
    exact groupM_mul hm h (groupM_X hm)

end Holant.Dihedral.TwoCardLocalization
