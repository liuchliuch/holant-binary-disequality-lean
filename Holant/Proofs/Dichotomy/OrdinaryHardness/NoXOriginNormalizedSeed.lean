import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOriginSeed

/-! The normalization graph is built in the unchanged source field; its
algebraic semantic image retains the selected non-Affine local twist. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginNormalizedSeed
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open scoped BigOperators
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {K : Type} [Field K] {s n : ℕ} {arity : ℕ→ℕ}
variable {H : (i : Fin s)→Signature K (arity i.val)}

theorem mapped_graph (phi : K→+*AlgebraicComplex) (N : M.Macro H (n+2)) (A : M.Macro H 2)
    (v w : K) (anti : A.network.denote=NoXWeightedAntiSigned.anti v w) (a : Word (n+2)) :
    ∃Q : M.Macro H (n+2),(fun x=>phi (Q.network.denote x))=
      NoXOriginNormalizationPhase.normalized (fun x=>phi (N.network.denote x)) a (phi v) (phi w) := by
  classical
  let S := Finset.univ.filter (fun i=>a i=true)
  obtain ⟨Q,hQ⟩ := NoXOriginNormalizationGraph.exists_graph N A v w anti S
  refine ⟨Q,funext fun x=>?_⟩
  rw [hQ,NoXOriginNormalizationPhase.normalized,NoXOriginNormalizationPhase.weight,map_mul,map_prod]
  have shift : NoXOriginNormalizationGraph.shiftSet S x=xor a x := by
    funext i
    cases ha : a i <;> simp [NoXOriginNormalizationGraph.shiftSet,S,AffinePhase.xor,ha]
  rw [shift]
  congr 1
  simp only [S,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  cases a i <;> cases x i <;> simp

theorem exists_bad_origin (phi : K→+*AlgebraicComplex) (N : M.Macro H n)
    (P : M.Macro H 1) (A : M.Macro H 2)
    (pin : P.network.denote=fun x=>if x 0=false then 1 else 0)
    (v w : K) (anti : A.network.denote=NoXWeightedAntiSigned.anti v w)
    (hv : v≠0) (hw : w≠0) (fourth : phi v^4= -(phi w^4))
    (bad : ¬LocalAffine (fun x=>phi (N.network.denote x))) :
    ∃Q : M.Macro H (n+2),phi (Q.network.denote (origin (n+2)))≠0 ∧
      ¬Affine (fun x=>phi (Q.network.denote x)) := by
  obtain ⟨a,supported,negative⟩ := NoXOriginSeed.bad_padded phi N P pin bad
  obtain ⟨Q,hQ⟩ := mapped_graph phi (NoXOriginSeed.padded N P) A v w anti a
  have hv' : phi v≠0 := (map_ne_zero phi).mpr hv
  have hw' : phi w≠0 := (map_ne_zero phi).mpr hw
  refine ⟨Q,?_,?_⟩
  · change (fun x=>phi (Q.network.denote x)) (origin (n+2))≠0
    rw [hQ]
    exact NoXOriginNormalizationPhase.origin_nonzero _ a (phi v) (phi w) hw' supported
  · rw [hQ]
    exact NoXOriginNormalizationPhase.not_affine _ a (phi v) (phi w) hv' hw' fourth negative

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginNormalizedSeed
end
