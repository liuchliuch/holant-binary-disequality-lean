import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePinFace

/-! Failure of parity support supplies a genuine odd two-corner resource
using only the two native pins. The parity-uniform alternative is explicit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureOddFace
open Holant
namespace D
export NoIPureTwoColorFace (distance Face)
end D
namespace P
export NoIPurePinProjection (pin)
end P
namespace O
export NativeAntiTargetSource (Output)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false

def color {n : ℕ} (x : Fin n→Bool) : Bool:=decide (weight x%2=1)
def UniformParity {K : Type*} [Zero K] {n : ℕ} (f : Signature K n) : Prop:=
  ∃b : Bool,∀x,f x≠0 → color x=b

theorem distance_mod {n : ℕ} (x y : Fin n→Bool) :
    D.distance x y%2=(weight x+weight y)%2 := by
  induction n with
  | zero=>simp [NoIPureTwoColorFace.distance,
      Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance.distance,weight]
  | succ n ih=>
    have h:=ih (fun i=>x i.succ) (fun i=>y i.succ)
    simp only [NoIPureTwoColorFace.distance,
      Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance.distance,weight] at h ⊢
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
    cases hx:x 0 <;>cases hy:y 0 <;>simp only [hx,hy,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true] at * <;>omega

theorem distance_odd {n : ℕ} (x y : Fin n→Bool) (different : color x≠color y) :
    Odd (D.distance x y) := by
  have hm:weight x%2≠weight y%2:=by
    intro same
    exact different (by simp only [color,same])
  have hd:=distance_mod x y
  refine ⟨D.distance x y/2,?_⟩
  omega

theorem mixed_pair {K : Type*} [Zero K] {n : ℕ} (f : Signature K n)
    (mixed : ¬UniformParity f) : ∃x y,f x≠0 ∧ f y≠0 ∧ color x≠color y := by
  classical
  have live:∃x,f x≠0:=by
    by_contra empty
    push_neg at empty
    exact mixed ⟨false,fun x hx=>False.elim (hx (empty x))⟩
  obtain ⟨x,hx⟩:=live
  by_contra none
  apply mixed
  refine ⟨color x,?_⟩
  intro y hy
  by_contra bad
  exact none ⟨x,y,hx,hy,fun h=>bad h.symm⟩

variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (arity i.val))
variable (pins : Bool→O.Output H 1)
variable (pinsForm : ∀bit,(pins bit).network.denote=P.pin bit)

include pinsForm in
theorem source {n : ℕ} (N : O.Output H n) (mixed : ¬UniformParity N.network.denote) :
    ∃m,Odd m ∧ 0<m ∧ ∃R : O.Output H m,∃mask : Fin m→Bool,∃a b : K,
      a≠0 ∧ b≠0 ∧ charge mask%4≠0 ∧
      R.network.denote=fun z=>if z=mask then a else if z=(fun i=>!mask i) then b else 0 := by
  obtain ⟨x,y,hx,hy,hc,face⟩:=NoIPureTwoColorFace.source N.network.denote color (mixed_pair _ mixed)
  have different:x≠y:=by intro same;exact hc (congrArg color same)
  obtain ⟨m,hm,dm,R,mask,charge_eq,form⟩:=NoIPurePinFace.source H pins pinsForm N x y different face
  have odd:Odd m:=by rw [dm];exact distance_odd x y hc
  refine ⟨m,odd,hm,R,mask,N.network.denote x,N.network.denote y,hx,hy,?_,form⟩
  obtain ⟨k,hk⟩:=odd
  unfold charge
  omega

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureOddFace
end
