import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralLocalRankDescent
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOriginSeed

/-! Least support rank among actual LocalAffine-bad graphs over one unchanged
label table is between one and three. Both pin values and literal Eq4 suffice;
the original row is never translated by an unavailable physical anti gate. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalMinimalGraph
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeAffineSystematicSupport
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {K : Type} [Field K] {s n : ℕ} {arity : ℕ→ℕ}
variable {H : (i : Fin s)→Signature K (arity i.val)} (phi : K→+*AlgebraicComplex)
variable (P : Bool→M.Macro H 1) (E : M.Macro H 4)
variable (pin : ∀bit,(P bit).network.denote=fun x=>if x 0=bit then 1 else 0)
variable (eq4 : E.network.denote=Holant.EightVertex.ProductAnchor.equalityFour)
variable (squares : ∀Q : M.Macro H (n+2),Affine (fun x=>phi (Q.network.denote x)^2))

def Witness (r : ℕ) : Prop := ∃Q : M.Macro H (n+2),
  ¬LocalAffine (fun x=>phi (Q.network.denote x)) ∧
  Nonempty (SystematicSupport (fun x=>phi (Q.network.denote x)) r)

include squares in
theorem rank_positive {r : ℕ} (wit : Witness (n:=n) (H:=H) phi r) : 1≤r := by
  by_contra h
  have hr : r=0 := by omega
  subst r
  obtain ⟨Q,bad,⟨D⟩⟩:=wit
  obtain ⟨a,z,i,j,k,cube⟩:=NoXLocalAffineCubeWitness.witness D (squares Q) bad
  exact Fin.elim0 i

include pin eq4 squares in
theorem minimal (exists_witness : ∃r,Witness (n:=n) (H:=H) phi r) :
    ∃r,1≤r ∧ r≤3 ∧ Witness (n:=n) (H:=H) phi r ∧
      ∀t,t<r→¬Witness (n:=n) (H:=H) phi t := by
  classical
  let r:=Nat.find exists_witness
  have selected : Witness (n:=n) (H:=H) phi r:=Nat.find_spec exists_witness
  refine ⟨r,rank_positive phi squares selected,?_,selected,?_⟩
  · by_contra large
    have lower : 4≤r:=by omega
    obtain ⟨t,ht⟩ : ∃t,r=t+4:=⟨r-4,by omega⟩
    obtain ⟨Q,bad,⟨D⟩⟩:=selected
    rw [ht] at D
    obtain ⟨Q',bad',chart'⟩:=NoXGeneralLocalRankDescent.graph phi Q P E pin eq4 D (squares Q) bad
    have smaller : Witness (n:=n) (H:=H) phi (t+3):=⟨Q',bad',chart'⟩
    have minimum : r≤t+3:=Nat.find_min' exists_witness smaller
    omega
  · exact fun t ht=>Nat.find_min exists_witness ht

include pin eq4 squares in
theorem bounded (exists_witness : ∃r,Witness (n:=n) (H:=H) phi r) :
    ∃r,1≤r ∧ r≤3 ∧ Witness (n:=n) (H:=H) phi r := by
  obtain ⟨r,lower,upper,selected,_⟩:=minimal phi P E pin eq4 squares exists_witness
  exact ⟨r,lower,upper,selected⟩

include pin squares in
theorem seed (N : M.Macro H n) (bad : ¬LocalAffine (fun x=>phi (N.network.denote x))) :
    ∃r,Witness (n:=n) (H:=H) phi r := by
  let Q:=NoXOriginSeed.padded N (P false)
  obtain ⟨a,supported,negative⟩:=NoXOriginSeed.bad_padded phi N (P false) (pin false) bad
  have badQ : ¬LocalAffine (fun x=>phi (Q.network.denote x)):=fun good=>negative (good a supported)
  have nonzero : (fun x=>phi (Q.network.denote x))≠0:=by
    intro zero
    exact supported (congrFun zero a)
  obtain ⟨r,chart⟩:=exists_of_affine_square (fun x=>phi (Q.network.denote x)) (squares Q) nonzero
  exact ⟨r,Q,badQ,chart⟩

include pin eq4 squares in
theorem from_bad (N : M.Macro H n) (bad : ¬LocalAffine (fun x=>phi (N.network.denote x))) :
    ∃r,1≤r ∧ r≤3 ∧ Witness (n:=n) (H:=H) phi r ∧
      ∀t,t<r→¬Witness (n:=n) (H:=H) phi t :=
  minimal phi P E pin eq4 squares (seed phi P pin squares N bad)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalMinimalGraph
end
