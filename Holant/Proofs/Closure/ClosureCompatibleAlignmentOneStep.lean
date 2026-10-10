import Holant.Proofs.Closure.ClosureCompatibleAlignmentSurgery
import Holant.Proofs.Closure.ClosureCompatibleAlignmentCurrentClosure

/-! Higher-arity common-matching localization requires only one proper
outside contraction.  Two genuine line tags survive that same instruction,
but a matching ancestor has at most one kernel-dependent residual factor.
The CURRENT specialization constructs every matching premise from raw keys. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.CompatibleCoefficientLine
open Holant.Dihedral.TwoCardLocalization

set_option backward.isDefEq.respectTransparency false in
theorem common_matching_one_step_bound {m r : ℕ} (hm : 3 ≤ m) (large : 2 ≤ r)
    (h : Signature Scalar (2*r+4))
    (proper : ∀ cut : Equiv.Perm (Fin (2*r+2)),∀ γ : Bool,∀ t : {t : Scalar // Roots m t},
      outsideClose cut (M γ t.val) h = 0 ∨
        ClosureSixPort.AlgebraicRootMatching m (outsideClose cut (M γ t.val) h))
    (K₀ K₁ : Mat) (p : (Fin (r+1) × Bool) ≃ Fin (2*r+2))
    (A₀ A₁ : Fin (r+1) → Mat) (κ₀ κ₁ : Scalar)
    (member₀ : ∀ e,A₀ e ∈ groupM m) (member₁ : ∀ e,A₁ e ∈ groupM m)
    (nonzero₀ : κ₀ ≠ 0) (nonzero₁ : κ₁ ≠ 0)
    (equation₀ : Signature.contract K₀ h = MC.productValue p A₀ κ₀)
    (equation₁ : Signature.contract K₁ h = MC.productValue p A₁ κ₁)
    (e f : Fin (r+1)) (different : e ≠ f) :
    ProjectivelyEqual (A₁ e) (A₀ e) ∨ ProjectivelyEqual (A₁ f) (A₀ f) := by
  classical
  by_contra none
  have tagE : ¬ ProjectivelyEqual (A₁ e) (A₀ e) := fun equal => none (Or.inl equal)
  have tagF : ¬ ProjectivelyEqual (A₁ f) (A₀ f) := fun equal => none (Or.inr equal)
  have third : ∃ j : Fin (r+1),j ≠ e ∧ j ≠ f := by
    let bad : Finset (Fin (r+1)) := {e,f}
    have bound : bad.card ≤ 2 := by
      simpa only [bad,Finset.card_singleton] using Finset.card_insert_le e ({f} : Finset (Fin (r+1)))
    have less : bad.card < (Finset.univ : Finset (Fin (r+1))).card := by
      simp only [Finset.card_univ,Fintype.card_fin]
      omega
    obtain ⟨j,_member,outside⟩ := Finset.exists_mem_notMem_of_card_lt_card less
    exact ⟨j,by simpa only [bad,Finset.mem_insert,Finset.mem_singleton,not_or] using outside⟩
  obtain ⟨j,je,jf⟩ := third
  obtain ⟨α₀,parity₀⟩ := group_hasParity (by omega) (member₀ j)
  obtain ⟨α₁,parity₁⟩ := group_hasParity (by omega) (member₁ j)
  by_cases same : α₁ = α₀
  · subst α₁
    obtain ⟨t,trace₀,trace₁⟩ := compatible_trace hm parity₀ parity₁
    let cut := deleteOrder p j
    let ports := deleteOutputPorts p j
    let B₀ := fun d : MC.OtherEdges j => A₀ d.val
    let B₁ := fun d : MC.OtherEdges j => A₁ d.val
    let c₀ := Holant.Certificates.MatchingContractionClosure.trace (A₀ j) (M α₀ t.val)*κ₀
    let c₁ := Holant.Certificates.MatchingContractionClosure.trace (A₁ j) (M α₀ t.val)*κ₁
    have hc₀ : c₀ ≠ 0 := mul_ne_zero trace₀ nonzero₀
    have hc₁ : c₁ ≠ 0 := mul_ne_zero trace₁ nonzero₁
    have live₀ : MC.productValue ports B₀ c₀ ≠ 0 :=
      group_product_nonzero (by omega : 0<m) ports B₀ c₀ (fun d => member₀ d.val) hc₀
    have live₁ : MC.productValue ports B₁ c₁ ≠ 0 :=
      group_product_nonzero (by omega : 0<m) ports B₁ c₁ (fun d => member₁ d.val) hc₁
    have inherited₀ : Signature.contract K₀ (outsideClose cut (M α₀ t.val) h) = MC.productValue ports B₀ c₀ := by
      rw [outside_card,equation₀]
      exact ordered_delete_product p A₀ κ₀ j (M α₀ t.val)
    have inherited₁ : Signature.contract K₁ (outsideClose cut (M α₀ t.val) h) = MC.productValue ports B₁ c₁ := by
      rw [outside_card,equation₁]
      exact ordered_delete_product p A₁ κ₁ j (M α₀ t.val)
    rcases proper cut α₀ t with zero | ⟨R,_members,_scalar,literal⟩
    · apply live₀
      rw [← inherited₀,zero,Signature.contract_zero]
    · rw [literal] at inherited₀ inherited₁
      let e' : MC.OtherEdges j := ⟨e,Ne.symm je⟩
      let f' : MC.OtherEdges j := ⟨f,Ne.symm jf⟩
      have distinct : e' ≠ f' := fun equal => different (congrArg Subtype.val equal)
      have bound := matching_ancestor_factor_line_bound R K₀ K₁ ports B₀ B₁ c₀ c₁ live₀ live₁
        (fun d => groupM_det_nonzero (by omega) (member₀ d.val)) inherited₀ inherited₁ e' f' distinct
      rcases bound with line | line
      · exact tagE ((projective_as_matrix_line _ _).mpr line)
      · exact tagF ((projective_as_matrix_line _ _).mpr line)
  · have opposite : α₁ = !α₀ := by cases value : α₀ <;> cases α₁ <;> simp_all
    subst α₁
    obtain ⟨t,fused⟩ := fuse_parity_discrepancy hm (A₀ e) (A₁ e) (A₀ j) (A₁ j)
      (member₀ e) (member₁ e) α₀ parity₀ parity₁
    let C := M false t.val
    let cut := spliceOrder p e j
    let ports := spliceOutputPorts p e j (Ne.symm je)
    let B₀ := MC.spliceFactors C A₀ e j
    let B₁ := MC.spliceFactors C A₁ e j
    have hC : C ∈ groupM m := M_mem_group (by omega) false t.property
    have hB₀ : ∀ d,B₀ d ∈ groupM m := spliceFactors_member (by omega) A₀ e j C member₀ hC
    have hB₁ : ∀ d,B₁ d ∈ groupM m := spliceFactors_member (by omega) A₁ e j C member₁ hC
    have live₀ : MC.productValue ports B₀ κ₀ ≠ 0 := group_product_nonzero (by omega) ports B₀ κ₀ hB₀ nonzero₀
    have live₁ : MC.productValue ports B₁ κ₁ ≠ 0 := group_product_nonzero (by omega) ports B₁ κ₁ hB₁ nonzero₁
    have inherited₀ : Signature.contract K₀ (outsideClose cut C h) = MC.productValue ports B₀ κ₀ := by
      rw [outside_card,equation₀,ordered_splice_product p A₀ κ₀ e j (Ne.symm je)]
    have inherited₁ : Signature.contract K₁ (outsideClose cut C h) = MC.productValue ports B₁ κ₁ := by
      rw [outside_card,equation₁,ordered_splice_product p A₁ κ₁ e j (Ne.symm je)]
    rcases proper cut false t with zero | ⟨R,_members,_scalar,literal⟩
    · apply live₀
      rw [← inherited₀,zero,Signature.contract_zero]
    · rw [literal] at inherited₀ inherited₁
      let e' : MC.OtherEdges j := ⟨e,Ne.symm je⟩
      let f' : MC.OtherEdges j := ⟨f,Ne.symm jf⟩
      have distinct : e' ≠ f' := fun equal => different (congrArg Subtype.val equal)
      have tagE' : ¬ ProjectivelyEqual (B₁ e') (B₀ e') := by
        simpa [B₀,B₁,e',Holant.Certificates.MatchingContractionClosure.spliceFactors,
          C,generic_fuse_eq_marked] using fused
      have tagF' : ¬ ProjectivelyEqual (B₁ f') (B₀ f') := by
        simpa [B₀,B₁,f',Holant.Certificates.MatchingContractionClosure.spliceFactors,
          Ne.symm different] using tagF
      have bound := matching_ancestor_factor_line_bound R K₀ K₁ ports B₀ B₁ κ₀ κ₁ live₀ live₁
        (fun d => groupM_det_nonzero (by omega) (hB₀ d)) inherited₀ inherited₁ e' f' distinct
      rcases bound with line | line
      · exact tagE' ((projective_as_matrix_line _ _).mpr line)
      · exact tagF' ((projective_as_matrix_line _ _).mpr line)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
