import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureChargeTwoReduce

/-! Signed charge two modulo four forces the reduced resource to be an
actual binary with both constant entries nonzero. No diagonal gate is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoSmall
open Holant Holant.Complexity
namespace R
export NoIPureChargeTwoReduce (Reduced)
end R
namespace W
export NoIPureChargeTwoWords (row opposite)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {size : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin size)→Signature K (arity i.val))

theorem arity_two (D : R.Reduced H 2) : D.arity=2 := by
  have p:=D.positive
  have b:=D.small
  have c:=D.charge
  have w:=Holant.weight_le D.mask
  unfold Holant.charge at c
  omega

theorem constant_live (mask : Fin 2→Bool) (u v : K) (un : u≠0) (vn : v≠0)
    (residue : Holant.charge mask%4=2) :
    W.row mask u v (fun _=>false)≠0 ∧ W.row mask u v (fun _=>true)≠0 := by
  cases h0 : mask 0 <;> cases h1 : mask 1
  all_goals simp only [Holant.charge,Holant.weight,Fin.sum_univ_two,h0,h1,
    Bool.false_eq_true,if_false,if_true] at residue
  all_goals norm_num at residue
  all_goals simp [W.row,W.opposite,funext_iff,Fin.forall_fin_succ,h0,h1,un,vn]

theorem source (D : R.Reduced H 2) : ∃B : NativeAntiTargetSource.Output H 2,
    B.network.denote (fun _=>false)≠0 ∧ B.network.denote (fun _=>true)≠0 := by
  have hn:=arity_two H D
  obtain ⟨n,positive,small,N,mask,u,v,un,vn,form,residue⟩:=D
  change n=2 at hn
  subst n
  refine ⟨N,?_⟩
  rw [form]
  exact constant_live mask u v un vn residue

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoSmall
end
