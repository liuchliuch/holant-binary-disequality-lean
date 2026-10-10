import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePinProjection

/-! A two-corner coordinate face is obtained by actual native pin caps.
The exact two original coefficients survive, and the new arity is their
Hamming distance. There is no physical bit-flip hypothesis. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePinFace
open Holant
namespace P
export NoIPurePinProjection (pin tail insert insert_tail tail_insert distance_tail difference_tail face_insert output value)
end P
namespace D
export NoIPureTwoColorFace (distance Face)
end D
namespace O
export NativeAntiTargetSource (Output)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (arity i.val))
variable (pins : Bool→O.Output H 1)
variable (pinsForm : ∀bit,(pins bit).network.denote=P.pin bit)

include pinsForm in
theorem source {n : ℕ} (N : O.Output H n) (x y : Fin n→Bool) (different : x≠y)
    (face : ∀z,D.Face x y z → N.network.denote z≠0 → z=x ∨ z=y) :
    ∃m,0<m ∧ m=D.distance x y ∧ ∃R : O.Output H m,∃mask : Fin m→Bool,
      charge mask=(weight x : ℤ)-weight y ∧
      R.network.denote=fun z=>if z=mask then N.network.denote x else
        if z=(fun i=>!mask i) then N.network.denote y else 0 := by
  classical
  induction n with
  | zero=>
    exact False.elim (different (Subsingleton.elim _ _))
  | succ n ih=>
    by_cases agree:∃i,x i=y i
    · obtain ⟨i,agree⟩:=agree
      let R:=P.output H pins N i (x i)
      let u:=P.tail i x
      let v:=P.tail i y
      have xu : P.insert i (x i) u=x:=P.insert_tail i x
      have yv : P.insert i (x i) v=y:=by rw [agree];exact P.insert_tail i y
      have uv:u≠v:=by
        intro same
        exact different (xu.symm.trans ((congrArg (P.insert i (x i)) same).trans yv))
      have ex:R.network.denote u=N.network.denote x:=by
        change (P.output H pins N i (x i)).network.denote u=_
        rw [P.value H pins pinsForm]
        exact congrArg N.network.denote xu
      have ey:R.network.denote v=N.network.denote y:=by
        change (P.output H pins N i (x i)).network.denote v=_
        rw [P.value H pins pinsForm]
        exact congrArg N.network.denote yv
      have small : ∀z,D.Face u v z → R.network.denote z≠0 → z=u ∨ z=v := by
        intro z hz hn
        have live:N.network.denote (P.insert i (x i) z)≠0:=by
          simpa only [R,P.value H pins pinsForm] using hn
        have corner:=face (P.insert i (x i) z) (P.face_insert i x y agree z hz) live
        rcases corner with left|right
        · exact Or.inl (by simpa only [P.tail_insert] using congrArg (P.tail i) left)
        · exact Or.inr (by simpa only [P.tail_insert] using congrArg (P.tail i) right)
      obtain ⟨m,hm,dm,S,mask,charge_eq,form⟩:=ih R u v uv small
      refine ⟨m,hm,dm.trans (P.distance_tail i x y agree),S,mask,
        charge_eq.trans (P.difference_tail i x y agree),?_⟩
      simpa only [ex,ey] using form
    · push_neg at agree
      have complement:y=(fun i=>!x i):=by
        funext i
        have h:=agree i
        cases hx:x i <;> cases hy:y i <;> simp_all
      have dist:D.distance x y=n+1:=by
        unfold NoIPureTwoColorFace.distance
          Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance.distance
        simp [agree]
      refine ⟨n+1,by omega,dist.symm,N,x,?_,?_⟩
      · have wc:=weight_compl_add x
        rw [complement]
        unfold charge
        omega
      · funext z
        by_cases zx:z=x
        · simp [zx]
        by_cases zy:z=y
        · rw [if_neg zx,if_pos (zy.trans complement),zy]
        · have zero:N.network.denote z=0:=by
            by_contra live
            have hz:D.Face x y z:=by intro i same;exact False.elim (agree i same)
            exact (face z hz live).elim zx zy
          simp only [zx,ite_false,←complement,zy,zero]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePinFace
end
