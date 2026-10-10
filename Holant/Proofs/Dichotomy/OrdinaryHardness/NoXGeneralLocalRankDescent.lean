import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralLocalRestriction
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOriginRestrictionGraphs

/-! Actual pin and Eq4 graphs lower the support rank of every bad
LocalAffine row of rank at least four. The original field, label table,
and physical arity stay fixed throughout the graph construction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalRankDescent
open Holant Holant.Tractable
open OrdinaryNegativeAffineSystematicSupport
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] {s n r : ℕ} {arity : ℕ→ℕ}
variable {H : (i : Fin s)→Signature K (arity i.val)} (phi : K→+*AlgebraicComplex)
variable (N : M.Macro H (n+2)) (P : Bool→M.Macro H 1) (E : M.Macro H 4)
variable (pin : ∀bit,(P bit).network.denote=fun x=>if x 0=bit then 1 else 0)
variable (eq4 : E.network.denote=Holant.EightVertex.ProductAnchor.equalityFour)
variable (D : SystematicSupport (fun x=>phi (N.network.denote x)) (r+4))
variable (square : Affine (fun x=>phi (N.network.denote x)^2))
variable (bad : ¬LocalAffine (fun x=>phi (N.network.denote x)))
include D pin eq4 square bad in
theorem graph : ∃Q : M.Macro H (n+2),
    ¬LocalAffine (fun x=>phi (Q.network.denote x)) ∧
    Nonempty (SystematicSupport (fun x=>phi (Q.network.denote x)) (r+3)) := by
  rcases NoXGeneralLocalRestriction.restriction D square bad with pcase|ecase
  · obtain ⟨p,bit,hp,chart⟩:=pcase
    let Q:=NoXOriginRestrictionGraphs.pinMask N (P bit) p
    have value : (fun x=>phi (Q.network.denote x))=
        pinMask (fun x=>phi (N.network.denote x)) p bit := by
      funext x
      rw [NoXOriginRestrictionGraphs.pinMask_value N (P bit) p bit (pin bit)]
      by_cases hx : x p=bit <;> simp [pinMask,hx]
    refine ⟨Q,?_,?_⟩
    · rwa [value]
    · rwa [value]
  · obtain ⟨p,q,pq,hp,chart⟩:=ecase
    obtain ⟨e,he0,he1⟩:=NoXLocalPermutation.pair_permutation p q (0 : Fin (n+2)) 1 pq
      (by intro he;have hv:=congrArg Fin.val he;change 0=1 at hv;omega)
    let Q:=NoXOriginRestrictionGraphs.equalMask N E e
    have value : (fun x=>phi (Q.network.denote x))=
        NoXLocalPairSupport.equalMask (fun x=>phi (N.network.denote x)) p q := by
      funext x
      rw [NoXOriginRestrictionGraphs.equalMask_value N E eq4 e p q he0 he1]
      by_cases hx : x p=x q <;> simp [NoXLocalPairSupport.equalMask,hx]
    refine ⟨Q,?_,?_⟩
    · rwa [value]
    · rwa [value]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalRankDescent
end
