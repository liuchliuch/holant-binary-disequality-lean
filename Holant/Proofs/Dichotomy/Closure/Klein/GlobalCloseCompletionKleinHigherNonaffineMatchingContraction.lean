import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineEdgeCoordinates

/-! Reindexing the literal matching overlap by actual alternating cycle ports
and original edge IDs. No graph contraction identity is assumed. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
open Equiv
open scoped BigOperators
namespace Matching
variable {P I : Type*} {r : ℕ}
namespace PairCoordinates
variable {M : Matching P r} (C : M.PairCoordinates I)

 def assignments : (P → Bool) ≃ ((I → Bool) × (I → Bool)) where
  toFun x := (fun i => x (C.ports (i,false)),fun i => x (C.ports (i,true)))
  invFun xy p := if (C.ports.symm p).2 then xy.2 (C.ports.symm p).1 else xy.1 (C.ports.symm p).1
  left_inv x := by
    funext p
    obtain ⟨⟨i,b⟩,rfl⟩ := C.ports.surjective p
    cases b <;> simp
  right_inv xy := by
    rcases xy with ⟨x,y⟩
    apply Prod.ext <;> funext i <;> simp

@[simp] theorem assignments_symm_false (x y : I → Bool) (i : I) :
    C.assignments.symm (x,y) (C.ports (i,false)) = x i := by simp [assignments]

@[simp] theorem assignments_symm_true (x y : I → Bool) (i : I) :
    C.assignments.symm (x,y) (C.ports (i,true)) = y i := by simp [assignments]

 theorem dualTensor_eq_prod [Fintype I] (a : Fin r → Label) (x : P → Bool) :
    M.dualTensor a x = ∏ i, oriented (C.reverse i) (dual (a (C.edges i)))
      (x (C.ports (i,false))) (x (C.ports (i,true))) := by
  rw [dualTensor]
  exact (Fintype.prod_equiv C.edges _ _ (fun i => (C.dual_entry a x i).symm)).symm

 theorem tensor_eq_prod [Fintype I] (a : Fin r → Label) (x : P → Bool) :
    M.tensor a x = ∏ i, oriented (C.reverse i) (E (a (C.edges i)))
      (x (C.ports (i,false))) (x (C.ports (i,true))) := by
  rw [tensor]
  exact (Fintype.prod_equiv C.edges _ _ (fun i => (C.tensor_entry a x i).symm)).symm

 theorem sum_assignments [Fintype I] [DecidableEq I] [Fintype P] [DecidableEq P] (f : (P → Bool) → ℂ) :
    ∑ z, f z = ∑ x : I → Bool, ∑ y : I → Bool, f (C.assignments.symm (x,y)) := by
  simpa only [Fintype.sum_prod_type] using
    (Fintype.sum_equiv C.assignments f (fun xy => f (C.assignments.symm xy))
      (fun z => congrArg f (C.assignments.symm_apply_apply z).symm))

end PairCoordinates

variable [Fintype P] [LinearOrder P]

 theorem overlap_eq_cycle_sum (M N : Matching P r) (fixed labels : Fin r → Label) :
    M.overlap N fixed labels =
      ∑ x : M.CycleEdge N → Bool, ∑ y : M.CycleEdge N → Bool,
        ∏ e, oriented ((M.mCoordinates N).reverse e) (dual (labels ((M.mCoordinates N).edges e))) (x e) (y e) *
          oriented ((M.nCoordinates N).reverse e) (E (fixed ((M.nCoordinates N).edges e))) (y e) (x (M.cycleNext N e)) := by
  rw [overlap,coefficient,(M.mCoordinates N).sum_assignments]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [(M.mCoordinates N).dualTensor_eq_prod,(M.nCoordinates N).tensor_eq_prod,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e he
  have hmf : (M.mCoordinates N).ports (e,false) = M.canonicalPorts N (e,false) := rfl
  have hmt : (M.mCoordinates N).ports (e,true) = M.canonicalPorts N (e,true) := rfl
  have hnf : (M.nCoordinates N).ports (e,false) = (M.mCoordinates N).ports (e,true) := rfl
  have hnt : (M.nCoordinates N).ports (e,true) = (M.mCoordinates N).ports (M.cycleNext N e,false) := rfl
  rw [hnf,hnt]
  simp only [PairCoordinates.assignments_symm_false,PairCoordinates.assignments_symm_true]

end Matching
end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
