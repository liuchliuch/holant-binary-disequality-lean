import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeAffinePorts

/-! Exact positive and negative counts under a proper affine face. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeSignedCounts
open Holant
open OrdinaryNegativeSignedPortsCore (Port)
open scoped BigOperators
namespace A
export NoXReciprocalRankThreeAffinePorts (Transform transformed offset)
end A
namespace P
export OrdinaryNegativeSparseRankThreeParity (image)
export NoXSeparateSignedProjection (signedCount)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {n : ℕ}
theorem transformed_count (p : Fin n→Port 7) (t : A.Transform) (j : Fin 7) (bit : Bool) :
    P.signedCount (A.transformed p t) j bit=
      ∑k : Fin 7,if P.image t.base k=j.succ then P.signedCount p k (bit ^^ A.offset t k) else 0 := by
  unfold P.signedCount
  have distribute (h : Prop) [Decidable h] (g : Fin n→ℕ) :
      (if h then ∑i,g i else 0)=∑i,if h then g i else 0 := by split_ifs <;> simp
  simp_rw [distribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  cases hp:p i with
  | inl b=>simp [A.transformed,hp]
  | inr v=>
    rcases v with ⟨k,s⟩
    have he (v : Fin 8) (h : v≠0) : (⟨v.val-1,by omega⟩ : Fin 7)=j ↔ v=j.succ := by
      constructor <;> intro hh <;> apply Fin.ext
      · have hv:=congrArg Fin.val hh
        have hn:=v.pos_iff_ne_zero.mpr h
        simp only [Fin.val_mk,Fin.val_succ] at hv ⊢
        omega
      · have hv:=congrArg Fin.val hh
        simp only [Fin.val_mk,Fin.val_succ] at hv ⊢
        omega
    have hs:j.succ≠(0 : Fin 8) := Fin.succ_ne_zero j
    rw [Finset.sum_eq_single k]
    · by_cases hz:P.image t.base k=0
      · simp [A.transformed,hp,hz,Ne.symm hs]
      · cases s <;> cases bit <;> cases ho:A.offset t k <;>
          simp [A.transformed,hp,hz,he _ hz,ho]
    · intro v _ hv
      simp [hv,Ne.symm hv]
    · simp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeSignedCounts
end
