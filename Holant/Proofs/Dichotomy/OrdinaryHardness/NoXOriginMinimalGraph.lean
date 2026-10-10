import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOriginRankDescent

/-! Well-founded support-rank minimization ranges only over actual ordinary
graphs with the original fixed label table. The square hypothesis is supplied
by NoXOriginGraphClosure.square under failure of original-oracle hardness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginMinimalGraph
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
variable (P : M.Macro H 1) (E : M.Macro H 4)
variable (pin : P.network.denote=fun x=>if x 0=false then 1 else 0)
variable (eq4 : E.network.denote=Holant.EightVertex.ProductAnchor.equalityFour)
variable (squares : ∀Q : M.Macro H (n+2),Affine (fun x=>phi (Q.network.denote x)^2))

def Witness (r : ℕ) : Prop := ∃Q : M.Macro H (n+2),
  phi (Q.network.denote (origin (n+2)))≠0 ∧ ¬Affine (fun x=>phi (Q.network.denote x)) ∧
  Nonempty (SystematicSupport (fun x=>phi (Q.network.denote x)) r)

include squares in
theorem rank_positive {r : ℕ} (wit : Witness (n:=n) (H:=H) phi r) : 1≤r := by
  by_contra h
  have hr : r=0 := by omega
  subst r
  obtain ⟨Q,nonzero,bad,⟨D⟩⟩ := wit
  have hf : (fun x=>phi (Q.network.denote x))≠0 := by
    intro zero;exact nonzero (congrFun zero _)
  apply D.nonAffine_reduced (squares Q) hf bad
  convert affine_constant 0 (D.reduced (origin 0)) using 1
  funext x
  exact congrArg D.reduced (Subsingleton.elim x (origin 0))

include pin eq4 squares in
theorem bounded (exists_witness : ∃r,Witness (n:=n) (H:=H) phi r) :
    ∃r,1≤r ∧ r≤3 ∧ Witness (n:=n) (H:=H) phi r := by
  classical
  let r := Nat.find exists_witness
  have selected : Witness (n:=n) (H:=H) phi r := Nat.find_spec exists_witness
  refine ⟨r,rank_positive phi squares selected,?_,selected⟩
  by_contra large
  have lower : 4≤r := by omega
  obtain ⟨t,ht⟩ : ∃t,r=t+4 := ⟨r-4,by omega⟩
  obtain ⟨Q,nonzero,bad,⟨D⟩⟩ := selected
  rw [ht] at D
  obtain ⟨Q',origin',bad',chart'⟩ := NoXOriginRankDescent.graph phi Q P E pin eq4 D
    (squares Q) nonzero bad
  have smaller : Witness (n:=n) (H:=H) phi (t+3) := ⟨Q',origin',bad',chart'⟩
  have minimum : r≤t+3 := Nat.find_min' exists_witness smaller
  omega

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginMinimalGraph
end
