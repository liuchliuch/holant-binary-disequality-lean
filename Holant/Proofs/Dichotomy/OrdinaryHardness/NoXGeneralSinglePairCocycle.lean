import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalStarCriterion

/-! Third-ratio symmetry and propagation for a single fixed equality pair.
All identities retain the literal nonzero values of the full function. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSinglePairCocycle
open Holant Holant.Tractable Holant.Tractable.AffinePhase
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {n : ℕ} (f : Signature AlgebraicComplex n)

theorem xor_swap (a b c : Word n) : xor (xor a b) c=xor (xor a c) b := by
  rw [xor_assoc,xor_comm b c,←xor_assoc]

theorem swap_first (z u v w : Word n) : thirdRatio f z u v w=thirdRatio f z v u w := by
  simp only [thirdRatio,xor_swap z u v]
  ring

theorem swap_last (z u v w : Word n) : thirdRatio f z u v w=thirdRatio f z u w v := by
  simp only [thirdRatio,xor_swap (xor z u) v w,xor_swap z v w]
  ring

variable (full : ∀x,f x≠0)
include full in
theorem shift_of_cross (z t u v w : Word n)
    (left : thirdRatio f z t v w=1)
    (right : thirdRatio f (xor z u) t v w=1) :
    thirdRatio f (xor z t) u v w=thirdRatio f z u v w := by
  have a:=NoXThirdRatioCocycle.direction_sum f full z t u v w
  have b:=NoXThirdRatioCocycle.direction_sum f full z u t v w
  rw [left,one_mul] at a
  rw [right,mul_one] at b
  rw [xor_comm t u] at a
  exact a.symm.trans b

variable (pins : ∀p,Affine (NoXLocalStarCriterion.zeroCut f p))
include full pins in
theorem one_endpoint (z : Word n) (i j k p : Fin n)
    (good : Affine (NoXLocalStarCriterion.equalCut f p i))
    (ij : i≠j) (ik : i≠k) (pi : p≠i) (pj : p≠j) (pk : p≠k) :
    thirdRatio f z (basis i) (basis j) (basis k)=1 := by
  by_cases hp : z p=false
  · exact NoXLocalStarCriterion.zero_ratio f full p (pins p) _ _ _ _ hp
      (by simp [basis,pi]) (by simp [basis,pj]) (by simp [basis,pk])
  have hp' : z p=true := Bool.eq_true_of_not_eq_false hp
  let b : Word n := Function.update (Function.update z p false) i false
  have bi : b i=false := by simp [b]
  have bp : b p=false := by simp [b,pi]
  have hpair : thirdRatio f b (xor (basis p) (basis i)) (basis j) (basis k)=1 := by
    apply NoXLocalStarCriterion.equal_ratio f full p i good _ _ _ _ (bp.trans bi.symm)
    · simp [AffinePhase.xor,basis,pi,Ne.symm pi]
    · simp [basis,pj,ij]
    · simp [basis,pk,ik]
  have hpin : thirdRatio f b (basis p) (basis j) (basis k)=1 := by
    exact NoXLocalStarCriterion.zero_ratio f full i (pins i) _ _ _ _ bi
      (by simp [basis,Ne.symm pi]) (by simp [basis,ij]) (by simp [basis,ik])
  have hbase : thirdRatio f (xor b (basis p)) (basis i) (basis j) (basis k)=1 := by
    have h:=NoXThirdRatioCocycle.direction_sum f full b (basis p) (basis i) (basis j) (basis k)
    rw [hpair,hpin,one_mul] at h
    exact h.symm
  have base_eq : xor b (basis p)=Function.update z i false := by
    funext t
    by_cases hi : t=i
    · subst t;simp [AffinePhase.xor,basis,b,Ne.symm pi]
    by_cases ht : t=p
    · subst t;simp [AffinePhase.xor,basis,b,pi,hp']
    · simp [AffinePhase.xor,basis,b,hi,ht]
  rw [base_eq] at hbase
  cases zi : z i with
  | false=>
      have hz : Function.update z i false=z := by simp [←zi]
      simpa [hz] using hbase
  | true=>
      have hz : xor (Function.update z i false) (basis i)=z := by
        funext t
        by_cases ht : t=i
        · subst t;simp [AffinePhase.xor,basis,zi]
        · simp [AffinePhase.xor,basis,ht]
      have h:=NoXThirdRatioCocycle.shift_first f full (Function.update z i false) (basis i) (basis j) (basis k)
      simpa only [hz,hbase,inv_one] using h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSinglePairCocycle
end
