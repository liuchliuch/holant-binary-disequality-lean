import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalStarCriterion
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOriginRestrictionGraphs
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOriginRestrictionSupport

/-! A non-Affine origin-supported graph of support rank at least four has
an actual zero-pin or Eq4 equality restriction of strictly smaller rank.
The ordered physical arity and original label table remain unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginRankDescent
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeAffineSystematicSupport
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
section Semantic
variable {n r : ℕ} {f : Signature AlgebraicComplex n}

variable (D : SystematicSupport f (r+4)) (square : Affine (fun x=>f x^2))
variable (origin : f (AffinePhase.origin n)≠0) (bad : ¬Affine f)
include D square origin bad in
theorem restriction :
    (∃p : Fin n,¬Affine (pinMask f p false) ∧
      Nonempty (SystematicSupport (pinMask f p false) (r+3))) ∨
    (∃p q : Fin n,p≠q ∧ ¬Affine (NoXLocalPairSupport.equalMask f p q) ∧
      Nonempty (SystematicSupport (NoXLocalPairSupport.equalMask f p q) (r+3))) := by
  have nonzero : f≠0 := by intro h;exact origin (congrFun h _)
  have reduced_bad := D.nonAffine_reduced square nonzero bad
  rcases NoXLocalStarCriterion.bad_cut D.reduced D.reduced_full (by omega) reduced_bad with pin|pair
  · obtain ⟨i,hi⟩ := pin
    refine Or.inl ⟨D.ports i,?_,NoXOriginRestrictionSupport.pin_chart D i false⟩
    intro good
    apply hi
    have h := good.precompose D.encode D.affine
    convert h using 1
    funext x
    simp only [NoXLocalStarCriterion.zeroCut,SystematicSupport.reduced,pinMask,D.free]
  · obtain ⟨i,j,ij,hi⟩ := pair
    refine Or.inr ⟨D.ports i,D.ports j,fun h=>ij (D.injective h),?_,
      NoXOriginRestrictionSupport.equal_chart D i j ij⟩
    intro good
    apply hi
    have h := good.precompose D.encode D.affine
    convert h using 1
    funext x
    simp only [NoXLocalStarCriterion.equalCut,SystematicSupport.reduced,
      NoXLocalPairSupport.equalMask,D.free]

end Semantic

variable {n r : ℕ}
variable {K : Type} [Field K] {s : ℕ} {arity : ℕ→ℕ}
variable {H : (i : Fin s)→Signature K (arity i.val)} (phi : K→+*AlgebraicComplex)
variable (N : M.Macro H (n+2)) (P : M.Macro H 1) (E : M.Macro H 4)
variable (pin : P.network.denote=fun x=>if x 0=false then 1 else 0)
variable (eq4 : E.network.denote=Holant.EightVertex.ProductAnchor.equalityFour)
variable (D : SystematicSupport (fun x=>phi (N.network.denote x)) (r+4))
variable (square : Affine (fun x=>phi (N.network.denote x)^2))
variable (origin : phi (N.network.denote (AffinePhase.origin (n+2)))≠0)
variable (bad : ¬Affine (fun x=>phi (N.network.denote x)))
include D pin eq4 square origin bad in
theorem graph : ∃Q : M.Macro H (n+2),
    phi (Q.network.denote (AffinePhase.origin (n+2)))≠0 ∧
    ¬Affine (fun x=>phi (Q.network.denote x)) ∧
    Nonempty (SystematicSupport (fun x=>phi (Q.network.denote x)) (r+3)) := by
  rcases restriction D square origin bad with pcase|ecase
  · obtain ⟨p,hp,chart⟩ := pcase
    let Q := NoXOriginRestrictionGraphs.pinMask N P p
    have value : (fun x=>phi (Q.network.denote x))=
        pinMask (fun x=>phi (N.network.denote x)) p false := by
      funext x
      rw [NoXOriginRestrictionGraphs.pinMask_value N P p false pin]
      by_cases hx : x p=false <;> simp [pinMask,hx]
    refine ⟨Q,?_,?_,?_⟩
    · change (fun x=>phi (Q.network.denote x)) (AffinePhase.origin (n+2))≠0
      rw [value]
      simpa [pinMask,AffinePhase.origin] using origin
    · rwa [value]
    · rwa [value]
  · obtain ⟨p,q,pq,hp,chart⟩ := ecase
    obtain ⟨e,he0,he1⟩ := NoXLocalPermutation.pair_permutation p q (0 : Fin (n+2)) 1 pq (by intro he; have hv:=congrArg Fin.val he; change 0=1 at hv; omega)
    let Q := NoXOriginRestrictionGraphs.equalMask N E e
    have value : (fun x=>phi (Q.network.denote x))=
        NoXLocalPairSupport.equalMask (fun x=>phi (N.network.denote x)) p q := by
      funext x
      rw [NoXOriginRestrictionGraphs.equalMask_value N E eq4 e p q he0 he1]
      by_cases hx : x p=x q <;> simp [NoXLocalPairSupport.equalMask,hx]
    refine ⟨Q,?_,?_,?_⟩
    · change (fun x=>phi (Q.network.denote x)) (AffinePhase.origin (n+2))≠0
      rw [value]
      simpa [NoXLocalPairSupport.equalMask,AffinePhase.origin] using origin
    · rwa [value]
    · rwa [value]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginRankDescent
end
