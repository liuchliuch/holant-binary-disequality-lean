import Holant.Proofs.Hardness.GeneralOddNonisotropicFrame

/-! Internally produced endpoint-support gadgets from actual ordinary graphs.
Every step attaches one fresh copy of the given unary by one Eq edge, possibly
after an explicit boundary permutation.  No desired gadget is an input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddNonisotropicDescent
open Holant
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
open GeneralOddNonisotropicFrame
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K]

def EndpointSupport {n : ℕ} (f : Signature K n) : Prop :=
  ∀ x,f x≠0 → x=(fun _ => false) ∨ x=(fun _ => true)

/-- An arbitrary nonzero coefficient away from the unary's own axis produces
an actual generalized equality gadget of positive arity. Its opposite endpoint
is nonzero; its own-axis endpoint is retained and may vanish. -/
theorem descend (F : SignatureFamily K) (U : Network K 1)
    (hUF : Uses U F) (hUE : Ordinary U) (n : ℕ) (N : Network K n)
    (hNF : Uses N F) (hNE : Ordinary N) (x : Fin n → Bool)
    (hx : chart U.denote N.denote x≠0) (hx0 : x≠(fun _ => false)) :
    ∃ m k : ℕ,0<m ∧ m+k=n ∧ ∃ V : Network K m,
      Uses V F ∧ Ordinary V ∧
      EndpointSupport (chart U.denote V.denote) ∧
      chart U.denote V.denote (fun _ => true)≠0 ∧
      V.shape.vertices=k*U.shape.vertices+N.shape.vertices ∧
      V.shape.edges=k*(U.shape.edges+1)+N.shape.edges := by
  classical
  induction n with
  | zero => exact False.elim (hx0 (funext fun i => Fin.elim0 i))
  | succ n ih =>
    by_cases hstop : EndpointSupport (chart U.denote N.denote)
    · refine ⟨n+1,0,by omega,by omega,N,hNF,hNE,hstop,?_,by simp,by simp⟩
      have hxt := (hstop x hx).resolve_left hx0
      rwa [←hxt]
    · obtain ⟨y,hy,hy0,hy1⟩ : ∃y,chart U.denote N.denote y≠0 ∧
          y≠(fun _ => false) ∧ y≠(fun _ => true) := by
        unfold EndpointSupport at hstop
        push Not at hstop
        exact hstop
      obtain ⟨i,hi⟩ : ∃i,y i=false := by
        by_contra h
        push Not at h
        apply hy1
        funext i
        exact Bool.eq_true_of_not_eq_false (h i)
      let e : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 i
      let R := reboundary N e
      let y' : Fin (n+1) → Bool := fun j => y (e j)
      let z : Fin n → Bool := fun j => y' j.succ
      have hhead : y' 0=false := by simpa [y',e] using hi
      have hcons : Fin.cons false z=y' := by
        funext j
        refine Fin.cases hhead.symm (fun _ => rfl) j
      have hback : (fun j => y' (e j))=y := by
        funext j
        simp [y',e]
      have hz : chart U.denote (capHead U R).denote z≠0 := by
        rw [chart_capHead,hcons,chart_reboundary,hback]
        exact hy
      have hz0 : z≠(fun _ => false) := by
        intro hzero
        apply hy0
        rw [←hback,←hcons,hzero]
        funext j
        have hc0 : Fin.cons false (fun _ : Fin n => false)=(fun _ => false) := by
          funext t
          refine Fin.cases ?_ (fun _ => ?_) t <;> rfl
        exact congrFun hc0 (e j)
      obtain ⟨m,k,hm,hkn,V,hVF,hVE,hVsupport,hVtrue,hVv,hVe⟩ :=
        ih (capHead U R) (capHead_uses F U R hUF hNF)
          (capHead_ordinary U R hUE hNE) z hz hz0
      refine ⟨m,k+1,hm,by omega,V,hVF,hVE,hVsupport,hVtrue,?_,?_⟩
      · rw [hVv,capHead_vertices]
        change k*U.shape.vertices+(U.shape.vertices+N.shape.vertices)=_
        ring
      · rw [hVe,capHead_edges]
        change k*(U.shape.edges+1)+(U.shape.edges+1+N.shape.edges)=_
        ring

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddNonisotropicDescent
