import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXThirdRatioCocycle
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalAffineCubeControls

/-! Origin-through coordinate and equality hyperplanes determine an Affine
full-support function in dimension at least four. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalStarCriterion
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.AffinePatching
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {n : ℕ}

def zeroCut (f : Signature AlgebraicComplex n) (p : Fin n) : Signature AlgebraicComplex n :=
  fun x=>if x p=false then f x else 0

def equalCut (f : Signature AlgebraicComplex n) (p q : Fin n) : Signature AlgebraicComplex n :=
  fun x=>if x p=x q then f x else 0

theorem cube_zero (z u v w : Word n) (p : Fin n)
    (hz : z p=false) (hu : u p=false) (hv : v p=false) (hw : w p=false) (a : Fin 8) :
    cubeWords z u v w a p=false := by
  fin_cases a <;> simp [cubeWords,AffinePhase.xor,hz,hu,hv,hw]

theorem cube_equal (z u v w : Word n) (p q : Fin n)
    (hz : z p=z q) (hu : u p=u q) (hv : v p=v q) (hw : w p=w q) (a : Fin 8) :
    cubeWords z u v w a p=cubeWords z u v w a q := by
  fin_cases a <;> simp [cubeWords,AffinePhase.xor,hz,hu,hv,hw]

variable (f : Signature AlgebraicComplex n) (full : ∀x,f x≠0)
include full in
theorem zero_ratio (p : Fin n) (good : Affine (zeroCut f p)) (z u v w : Word n)
    (hz : z p=false) (hu : u p=false) (hv : v p=false) (hw : w p=false) :
    thirdRatio f z u v w=1 := by
  have same (a : Fin 8) : zeroCut f p (cubeWords z u v w a)=f (cubeWords z u v w a) := by
    simp only [zeroCut,cube_zero z u v w p hz hu hv hw a,ite_true]
  have eq := NoXLocalMergeFailure.ratio_agree _ _ z u v w same
  rw [←eq]
  exact affine_supported_cube _ good z u v w (fun a=>by rw [same];exact full _)

include full in
theorem equal_ratio (p q : Fin n) (good : Affine (equalCut f p q)) (z u v w : Word n)
    (hz : z p=z q) (hu : u p=u q) (hv : v p=v q) (hw : w p=w q) :
    thirdRatio f z u v w=1 := by
  have same (a : Fin 8) : equalCut f p q (cubeWords z u v w a)=f (cubeWords z u v w a) := by
    simp only [equalCut,cube_equal z u v w p q hz hu hv hw a,ite_true]
  have eq := NoXLocalMergeFailure.ratio_agree _ _ z u v w same
  rw [←eq]
  exact affine_supported_cube _ good z u v w (fun a=>by rw [same];exact full _)

variable (pins : ∀p,Affine (zeroCut f p)) (pairs : ∀p q,p≠q→Affine (equalCut f p q))
include full pins pairs in
theorem two_outside (z : Word n) (i j k p q : Fin n)
    (pi : p≠i) (pj : p≠j) (pk : p≠k) (qi : q≠i) (qj : q≠j) (qk : q≠k) (pq : p≠q) :
    thirdRatio f z (basis i) (basis j) (basis k)=1 := by
  by_cases hp : z p=false
  · exact zero_ratio f full p (pins p) _ _ _ _ hp
      (by simp [basis,pi]) (by simp [basis,pj]) (by simp [basis,pk])
  by_cases hq : z q=false
  · exact zero_ratio f full q (pins q) _ _ _ _ hq
      (by simp [basis,qi]) (by simp [basis,qj]) (by simp [basis,qk])
  have hp' : z p=true := Bool.eq_true_of_not_eq_false hp
  have hq' : z q=true := Bool.eq_true_of_not_eq_false hq
  exact equal_ratio f full p q (pairs p q pq) _ _ _ _ (hp'.trans hq'.symm)
    (by simp [basis,pi,qi]) (by simp [basis,pj,qj]) (by simp [basis,pk,qk])

include full pins pairs in
theorem distinct_cube (z : Word n) (i j k p : Fin n)
    (ij : i≠j) (ik : i≠k) (pi : p≠i) (pj : p≠j) (pk : p≠k) :
    thirdRatio f z (basis i) (basis j) (basis k)=1 := by
  by_cases hp : z p=false
  · exact zero_ratio f full p (pins p) _ _ _ _ hp
      (by simp [basis,pi]) (by simp [basis,pj]) (by simp [basis,pk])
  have hp' : z p=true := Bool.eq_true_of_not_eq_false hp
  let b : Word n := Function.update (Function.update z p false) i false
  have bi : b i=false := by simp [b]
  have bp : b p=false := by simp [b,pi]
  have hpair : thirdRatio f b (xor (basis p) (basis i)) (basis j) (basis k)=1 := by
    apply equal_ratio f full p i (pairs p i pi) _ _ _ _ (bp.trans bi.symm)
    · simp [AffinePhase.xor,basis,pi,Ne.symm pi]
    · simp [basis,pj,ij]
    · simp [basis,pk,ik]
  have hpin : thirdRatio f b (basis p) (basis j) (basis k)=1 := by
    exact zero_ratio f full i (pins i) _ _ _ _ bi
      (by simp [basis,Ne.symm pi]) (by simp [basis,ij]) (by simp [basis,ik])
  have hbase : thirdRatio f (xor b (basis p)) (basis i) (basis j) (basis k)=1 := by
    have h := NoXThirdRatioCocycle.direction_sum f full b (basis p) (basis i) (basis j) (basis k)
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
  | false =>
    have hz : Function.update z i false=z := by simp [←zi]
    simpa [hz] using hbase
  | true =>
    have hz : xor (Function.update z i false) (basis i)=z := by
      funext t
      by_cases ht : t=i
      · subst t;simp [AffinePhase.xor,basis,zi]
      · simp [AffinePhase.xor,basis,ht]
    have h := NoXThirdRatioCocycle.shift_first f full (Function.update z i false)
      (basis i) (basis j) (basis k)
    simpa only [hz,hbase,inv_one] using h

include full pins pairs in
theorem affine (higher : 4≤n) : Affine f := by
  classical
  apply OrdinaryNegativeAffineThreeFaces.affine_of_coordinate_cubes f full
  intro z i j k
  let S : Finset (Fin n) := {i,j,k}
  have small : S.card≤3 := by
    exact (Finset.card_insert_le _ _).trans (by
      have h := Finset.card_insert_le j ({k} : Finset (Fin n))
      simpa using Nat.add_le_add_right h 1)
  have nonempty : 0<Sᶜ.card := by
    rw [Finset.card_compl];simp only [Fintype.card_fin];omega
  obtain ⟨p,hp⟩ := Finset.card_pos.mp nonempty
  have hp' : p∉S := Finset.mem_compl.mp hp
  have pi : p≠i := by intro h;exact hp' (by simp [S,h])
  have pj : p≠j := by intro h;exact hp' (by simp [S,h])
  have pk : p≠k := by intro h;exact hp' (by simp [S,h])
  by_cases ij : i=j
  · have small' : S.card≤2 := by simpa [S,ij] using (Finset.card_insert_le j ({k} : Finset (Fin n)))
    have large : 1<Sᶜ.card := by
      rw [Finset.card_compl];simp only [Fintype.card_fin];omega
    obtain ⟨p,hp,q,hq,pq⟩ := Finset.one_lt_card.mp large
    have hp' := Finset.mem_compl.mp hp
    have hq' := Finset.mem_compl.mp hq
    exact two_outside f full pins pairs z i j k p q
      (by intro h;exact hp' (by simp [S,h])) (by intro h;exact hp' (by simp [S,h]))
      (by intro h;exact hp' (by simp [S,h])) (by intro h;exact hq' (by simp [S,h]))
      (by intro h;exact hq' (by simp [S,h])) (by intro h;exact hq' (by simp [S,h])) pq
  by_cases ik : i=k
  · have small' : S.card≤2 := by simpa [S,ik] using (Finset.card_insert_le j ({k} : Finset (Fin n)))
    have large : 1<Sᶜ.card := by
      rw [Finset.card_compl];simp only [Fintype.card_fin];omega
    obtain ⟨p,hp,q,hq,pq⟩ := Finset.one_lt_card.mp large
    have hp' := Finset.mem_compl.mp hp
    have hq' := Finset.mem_compl.mp hq
    exact two_outside f full pins pairs z i j k p q
      (by intro h;exact hp' (by simp [S,h])) (by intro h;exact hp' (by simp [S,h]))
      (by intro h;exact hp' (by simp [S,h])) (by intro h;exact hq' (by simp [S,h]))
      (by intro h;exact hq' (by simp [S,h])) (by intro h;exact hq' (by simp [S,h])) pq
  exact distinct_cube f full pins pairs z i j k p ij ik pi pj pk

include full in
theorem bad_cut (higher : 4≤n) (bad : ¬Affine f) :
    (∃p,¬Affine (zeroCut f p)) ∨ (∃p q,p≠q ∧ ¬Affine (equalCut f p q)) := by
  classical
  by_contra h
  push Not at h
  apply bad
  exact affine f full h.1 h.2 higher

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalStarCriterion
end
